-- | N1 wrapper for the wrap_main library circuit.
-- |
-- | Configuration: branches=1, step_widths=[1], Max_widths_by_slot=[N0; N1],
-- | Features.none. The slot widths come from the [[0]; [1]] padded vector
-- | passed to `Wrap_main.wrap_main` in `dump_circuit_impl.ml` for this fixture.
module Pickles.CircuitDiffs.PureScript.WrapMain
  ( compileWrapMainN1
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepVKCommsFromCompiled, deriveWrapVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainSimpleChain (StepMainSimpleChainParams, compileStepMainSimpleChain)
import Pickles.CircuitDiffs.PureScript.WrapMainConstants (wrapMainConstants)
import Pickles.Field (StepField, WrapField)
import Pickles.ProofsVerified (ProofsVerified(..))
import Pickles.Prove.Wrap (stepVkForCircuit)
import Pickles.Wrap.Advice (WrapAdvice)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

compileWrapMainN1
  :: IvpWrapParams
  -> StepMainSimpleChainParams
  -> Effect WrapArtifact
compileWrapMainN1 { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainSimpleChain stepParams
  vestaSrs <- createCRS @StepField
  pallasSrs <- createCRS @WrapField
  stepComms <- deriveStepVKCommsFromCompiled @1 @1 vestaSrs stepArt.stepCs
  let realStepVK = stepVkForCircuit stepComms
  let

    config :: WrapMainConfig 1 1 1
    config =
      { stepWidths: 1 :< Vector.nil
      , domainLog2s: stepArt.stepDomainLog2 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeTable: \i -> (lagrangeAt i).constant :< Vector.nil
      , blindingH
      , prevWrapDomainPins: (Just N1 :< Vector.nil) :< Vector.nil
      }
  -- mpv=1, slot 0 width=1; slots derived from PrevsSpec via funcdep.
  let
    dummyAdvice :: WrapAdvice 1 1
    dummyAdvice = unsafeCoerce unit
  wrapCs <- compile noAdvice (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMain @1 @1 @1 config stmt dummyAdvice (1 :< Vector.nil))
  wrapVk <- deriveWrapVKFromCompiled @2 pallasSrs wrapCs
  pure
    { stepCs: stepArt.stepCs
    , stepDomainLog2: stepArt.stepDomainLog2
    , wrapCs
    , wrapVk
    , constants: wrapMainConstants config (stepComms :< Vector.nil) (1 :< Vector.nil)
    }
