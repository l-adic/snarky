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
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, deriveStepVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainSideLoadedMain (StepMainSideLoadedMainParams, compileStepMainSideLoadedMain)
import Pickles.Types (StepField, WrapField)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Pickles.Wrap.Slots (Slots1)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

compileWrapMainSideLoadedMain
  :: IvpWrapParams
  -> StepMainSideLoadedMainParams
  -> Effect (CompiledCircuit WrapField)
compileWrapMainSideLoadedMain { lagrangeAt, blindingH } stepParams = do
  -- Recompile the step CS and derive its VK commitments. Same pattern
  -- as `compileWrapMainN1` / `compileWrapMainN2` etc. — the previous
  -- `dummyVestaPt`-based VK with 28 components sharing
  -- `(1, vestaGenY)` produced 14 fewer Generic gates than the real
  -- production VK with distinct commitments embedded via `choose_key`.
  stepBuiltState <- compileStepMainSideLoadedMain stepParams
  vestaSrs <- createCRS @StepField
  let
    realStepVK = deriveStepVKFromCompiled @1 vestaSrs stepBuiltState
    config :: WrapMainConfig 1
    config =
      -- domainLog2 = 14 mirrors production side-loaded `Simple_chain`
      -- (mpv=N1 → wrap_domain.h = 2^14 per `common.ml:25-29`).
      { stepWidths: 1 :< Vector.nil
      , domainLog2s: 14 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Nothing
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  -- `Slots1 2`: mpv=1, single slot with bound 2 (the side-loaded
  -- prev's `max_proofs_verified = N2` upper bound). Differs from
  -- WrapMain's `Slots1 1` (Simple_chain's bound is N1).
  compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMain @1 @(Slots1 2) config stmt)
    Kimchi.initialState
