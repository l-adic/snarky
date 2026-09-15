-- | N=1 wrap_main library circuit for the side-loaded main parent
-- | (`Simple_chain` from `dump_side_loaded_main.ml`).
-- |
-- | Configuration: branches=1, step_widths=[1], slot widths `[2]`
-- | (single slot with bound 2 for the side-loaded prev),
-- | wrap_domain=2^14, Features.none. Mirrors OCaml dumper params at
-- | `dump_side_loaded_main.ml`'s `Simple_chain` rule:
-- | `padded:[[0]; [2]]`, `step_widths:[1]`, `domain_log2:14`.
-- |
-- | Distinct from `compileWrapMainN1` (Simple_chain N1 with widths `[1]`)
-- | — the slot's bound differs (2 vs 1), exercising wrap_main's Pseudo
-- | dispatch over `Vector 0 / Vector 2` instead of `Vector 0 / Vector 1`.
module Pickles.CircuitDiffs.PureScript.WrapMainSideLoadedMain
  ( compileWrapMainSideLoadedMain
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepVKFromCompiled, deriveWrapVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainSideLoadedMain (StepMainSideLoadedMainParams, compileStepMainSideLoadedMain)
import Pickles.Field (StepField, WrapField)
import Pickles.Wrap.Advice (WrapAdvice)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

compileWrapMainSideLoadedMain
  :: IvpWrapParams
  -> StepMainSideLoadedMainParams
  -> Effect WrapArtifact
compileWrapMainSideLoadedMain { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainSideLoadedMain stepParams
  vestaSrs <- createCRS @StepField
  pallasSrs <- createCRS @WrapField
  realStepVK <- deriveStepVKFromCompiled @1 @1 vestaSrs stepArt.stepCs
  let

    config :: WrapMainConfig 1 1
    config =
      { stepWidths: 1 :< Vector.nil
      , domainLog2s: stepArt.stepDomainLog2 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Nothing
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  -- mpv=1, single side-loaded slot with bound 2 (the side-loaded
  -- prev's `max_proofs_verified = N2` upper bound). Slots derived
  -- from the `Slot 2 _` spec via funcdep.
  let
    dummyAdvice :: WrapAdvice 1 1
    dummyAdvice = unsafeCoerce unit
  wrapCs <- compile noAdvice (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    ( \stmt ->
        wrapMain @1 @1 @1
          config
          stmt
          dummyAdvice
          (2 :< Vector.nil)
    )
  wrapVk <- deriveWrapVKFromCompiled @2 pallasSrs wrapCs
  pure
    { stepCs: stepArt.stepCs
    , stepDomainLog2: stepArt.stepDomainLog2
    , wrapCs
    , wrapVk
    }
