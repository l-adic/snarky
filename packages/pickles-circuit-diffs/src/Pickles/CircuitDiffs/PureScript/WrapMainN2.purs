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

import Data.Maybe (Maybe(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepVKCommsFromCompiled, deriveWrapVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainSimpleChainN2 (StepMainSimpleChainN2Params, compileStepMainSimpleChainN2)
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

compileWrapMainN2
  :: IvpWrapParams
  -> StepMainSimpleChainN2Params
  -> Effect WrapArtifact
compileWrapMainN2 { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainSimpleChainN2 stepParams
  vestaSrs <- createCRS @StepField
  pallasSrs <- createCRS @WrapField
  stepComms <- deriveStepVKCommsFromCompiled @1 @2 vestaSrs stepArt.stepCs
  let realStepVK = stepVkForCircuit stepComms
  let

    config :: WrapMainConfig 1 2 1
    config =
      { stepWidths: 2 :< Vector.nil
      , domainLog2s: stepArt.stepDomainLog2 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeTable: \i -> (lagrangeAt i).constant :< Vector.nil
      , blindingH
      , prevWrapDomainPins: (Just N1 :< Just N1 :< Vector.nil) :< Vector.nil
      }
  -- mpv=2, slots [2; 2]; derived from PrevsSpec via funcdep.
  let
    dummyAdvice :: WrapAdvice 2 1
    dummyAdvice = unsafeCoerce unit

    slotWidths :: Vector 2 Int
    slotWidths = 2 :< 2 :< Vector.nil
  wrapCs <- compile noAdvice (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    ( \stmt ->
        wrapMain @1 @2 @1
          config
          stmt
          dummyAdvice
          slotWidths
    )
  wrapVk <- deriveWrapVKFromCompiled @2 pallasSrs wrapCs
  pure
    { stepCs: stepArt.stepCs
    , stepDomainLog2: stepArt.stepDomainLog2
    , wrapCs
    , wrapVk
    , constants: wrapMainConstants config (stepComms :< Vector.nil) slotWidths
    }
