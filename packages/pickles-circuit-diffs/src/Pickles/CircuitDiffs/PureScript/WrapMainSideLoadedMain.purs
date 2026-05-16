-- | N=1 wrap_main library circuit for the side-loaded main parent
-- | (`Simple_chain` from `dump_side_loaded_main.ml`).
-- |
-- | Configuration: branches=1, step_widths=[1], slot shape `Slots1 2`
-- | (single slot with bound 2 for the side-loaded prev),
-- | wrap_domain=2^14, Features.none. Mirrors OCaml dumper params at
-- | `dump_side_loaded_main.ml`'s `Simple_chain` rule:
-- | `padded:[[0]; [2]]`, `step_widths:[1]`, `domain_log2:14`.
-- |
-- | Distinct from `compileWrapMainN1` (Simple_chain N1 with `Slots1 1`)
-- | — the slot's bound differs (2 vs 1), exercising wrap_main's Pseudo
-- | dispatch over `Vector 0 / Vector 2` instead of `Vector 0 / Vector 1`.
module Pickles.CircuitDiffs.PureScript.WrapMainSideLoadedMain
  ( compileWrapMainSideLoadedMain
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (Tuple1)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepVKFromCompiled, deriveWrapVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainSideLoadedMain (StepMainSideLoadedMainParams, compileStepMainSideLoadedMain)
import Pickles.Field (StepField, WrapField)
import Pickles.Slots (SideLoaded, Slot)
import Pickles.Types (StatementIO)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMainForPrevs)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Circuit.DSL (F)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

compileWrapMainSideLoadedMain
  :: IvpWrapParams
  -> StepMainSideLoadedMainParams
  -> Effect WrapArtifact
compileWrapMainSideLoadedMain { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainSideLoadedMain stepParams
  vestaSrs <- createCRS @StepField
  pallasSrs <- createCRS @WrapField
  let
    realStepVK = deriveStepVKFromCompiled @1 @1 vestaSrs stepArt.stepCs

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
  -- from the `Slot SideLoaded` spec via funcdep.
  wrapCs <- compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    ( \stmt ->
        wrapMainForPrevs @1
          @(Tuple1 (Slot SideLoaded 2 1 (StatementIO (F StepField) Unit)))
          @1
          config
          stmt
    )
    Kimchi.initialState
  pure
    { stepCs: stepArt.stepCs
    , stepDomainLog2: stepArt.stepDomainLog2
    , wrapCs
    , wrapVk: deriveWrapVKFromCompiled @1 @2 pallasSrs wrapCs
    }
