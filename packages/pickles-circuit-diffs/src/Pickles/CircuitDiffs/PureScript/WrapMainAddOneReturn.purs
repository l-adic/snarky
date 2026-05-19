-- | N=0 wrapper for the `wrap_main` library circuit (Add_one_return):
-- | the wrapped step proof has no prev `unfinalized_proofs` /
-- | `messages_for_next_wrap_proof` entries, so the wrap circuit's
-- | verify-one-of-step is minimal.
-- |
-- | Configuration: `branches=1`, `step_widths=[0]`,
-- | `Max_widths_by_slot=[N0; N0]`, `Features.none`. OCaml fixture:
-- | `wrap_main_add_one_return_circuit.json`.
module Pickles.CircuitDiffs.PureScript.WrapMainAddOneReturn
  ( compileWrapMainAddOneReturn
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepVKFromCompiled, deriveWrapVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainAddOneReturn (StepMainAddOneReturnParams, compileStepMainAddOneReturn)
import Pickles.Field (StepField, WrapField)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMainForPrevs)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

compileWrapMainAddOneReturn
  :: IvpWrapParams
  -> StepMainAddOneReturnParams
  -> Effect WrapArtifact
compileWrapMainAddOneReturn { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainAddOneReturn stepParams
  vestaSrs <- createCRS @StepField
  pallasSrs <- createCRS @WrapField
  let
    realStepVK = deriveStepVKFromCompiled @1 @0 vestaSrs stepArt.stepCs

    config :: WrapMainConfig 1 1
    config =
      { stepWidths: 0 :< Vector.nil
      , domainLog2s: stepArt.stepDomainLog2 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Nothing
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  -- `slots` derived from `@Unit` via `SlotsFromSpec` funcdep.
  wrapCs <- compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMainForPrevs @1 @Unit @1 config stmt)
    Kimchi.initialState
  pure
    { stepCs: stepArt.stepCs
    , stepDomainLog2: stepArt.stepDomainLog2
    , wrapCs
    , wrapVk: deriveWrapVKFromCompiled @1 @2 pallasSrs wrapCs
    }
