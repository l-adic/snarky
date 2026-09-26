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

import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepVKCommsFromCompiled, deriveWrapVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainAddOneReturn (StepMainAddOneReturnParams, compileStepMainAddOneReturn)
import Pickles.CircuitDiffs.PureScript.WrapMainConstants (wrapMainConstants)
import Pickles.Field (StepField, WrapField)
import Pickles.Prove.Wrap (stepVkForCircuit)
import Pickles.Wrap.Advice (WrapAdvice)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

compileWrapMainAddOneReturn
  :: IvpWrapParams
  -> StepMainAddOneReturnParams
  -> Effect WrapArtifact
compileWrapMainAddOneReturn { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainAddOneReturn stepParams
  vestaSrs <- createCRS @StepField
  pallasSrs <- createCRS @WrapField
  stepComms <- deriveStepVKCommsFromCompiled @1 @0 vestaSrs stepArt.stepCs
  let realStepVK = stepVkForCircuit stepComms
  let

    config :: WrapMainConfig 1 0 1
    config =
      { stepWidths: 0 :< Vector.nil
      , domainLog2s: stepArt.stepDomainLog2 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeTable: \i -> (lagrangeAt i).constant :< Vector.nil
      , blindingH
      , prevWrapDomainPins: Vector.nil :< Vector.nil
      }
  -- mpv=0: no prev slots, so no per-slot widths.
  let
    dummyAdvice :: WrapAdvice 0 1
    dummyAdvice = unsafeCoerce unit
  wrapCs <- compile noAdvice (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMain @1 @0 @1 config stmt dummyAdvice Vector.nil)
  wrapVk <- deriveWrapVKFromCompiled @2 pallasSrs wrapCs
  pure
    { stepCs: stepArt.stepCs
    , stepDomainLog2: stepArt.stepDomainLog2
    , wrapCs
    , wrapVk
    , constants: wrapMainConstants config (stepComms :< Vector.nil) Vector.nil
    }
