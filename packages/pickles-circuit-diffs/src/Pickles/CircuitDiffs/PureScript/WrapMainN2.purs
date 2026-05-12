-- | N2 wrapper for the `wrap_main` library circuit.
-- |
-- | Configuration: `branches=1`, `step_widths=[2]`,
-- | `Max_widths_by_slot=[N2;N2]`, `Features.none`. Single rule
-- | (`prevs = [self; self]`), so `branches = 1`.
-- |
-- | `stepKeys` VK constants are derived by compiling the same
-- | Simple_chain N2 step CS (`step_main_simple_chain_n2_circuit`)
-- | and running the kimchi commitment pipeline; this produces the
-- | same baked-in constants OCaml's `Pickles.compile_promise` does.
-- | Reference: OCaml `dump_simple_chain_n2.ml`.
module Pickles.CircuitDiffs.PureScript.WrapMainN2
  ( compileWrapMainN2
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (Tuple2)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepVKFromCompiled, deriveWrapVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainSimpleChainN2 (StepMainSimpleChainN2Params, compileStepMainSimpleChainN2)
import Pickles.Field (StepField, WrapField)
import Pickles.Slots (Compiled, Slot)
import Pickles.Types (StatementIO)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMainForPrevs)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Circuit.DSL (F)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

compileWrapMainN2
  :: IvpWrapParams
  -> StepMainSimpleChainN2Params
  -> Effect WrapArtifact
compileWrapMainN2 { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainSimpleChainN2 stepParams
  vestaSrs <- createCRS @StepField
  pallasSrs <- createCRS @WrapField
  let
    realStepVK = deriveStepVKFromCompiled @2 vestaSrs stepArt.stepCs

    config :: WrapMainConfig 1
    config =
      { stepWidths: 2 :< Vector.nil
      , domainLog2s: stepArt.stepDomainLog2 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Nothing
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  -- mpv=2, slots [2; 2]; derived from PrevsSpec via funcdep.
  wrapCs <- compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    ( \stmt ->
        wrapMainForPrevs @1
          @(Tuple2 (Slot Compiled 2 (StatementIO (F StepField) Unit)) (Slot Compiled 2 (StatementIO (F StepField) Unit)))
          config
          stmt
    )
    Kimchi.initialState
  pure
    { stepCs: stepArt.stepCs
    , stepDomainLog2: stepArt.stepDomainLog2
    , wrapCs
    , wrapVk: deriveWrapVKFromCompiled @2 pallasSrs wrapCs
    }
