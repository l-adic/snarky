-- | The wrap circuit of the `import_two_phase_chain` tag, whose step
-- | circuit `step_main_import_two_phase_chain_circuit` dumps.
-- |
-- | Configuration: branches=1, step_widths=[2], prev slots [1, 2] (slot 0
-- | = a `two_phase_chain` proof, slot 1 = the tag's own), both at wrap
-- | domain N1, Features.none.
-- |
-- | No OCaml dump of this circuit exists; it is compiled for its key,
-- | which the step circuit's self slot verifies against
-- | (`stepMainConstants`).
module Pickles.CircuitDiffs.PureScript.WrapMainImportTwoPhaseChain
  ( compileWrapMainImportTwoPhaseChain
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepKey, deriveWrapKey)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainImportTwoPhaseChain (StepMainImportTwoPhaseChainParams, compileStepMainImportTwoPhaseChain)
import Pickles.Dump.Constants (wrapMainConstants)
import Pickles.Field (StepField, WrapField)
import Pickles.ProofsVerified (ProofsVerified(..))
import Pickles.Prove.Step (extractWrapVKCommsAdvice)
import Pickles.Prove.Wrap (extractStepVKComms, stepVkForCircuit)
import Pickles.Wrap.Advice (WrapAdvice)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pasta (PallasG)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

compileWrapMainImportTwoPhaseChain
  :: CRS PallasG
  -> IvpWrapParams
  -> StepMainImportTwoPhaseChainParams
  -> Effect WrapArtifact
compileWrapMainImportTwoPhaseChain pallasSrs { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainImportTwoPhaseChain pallasSrs stepParams
  vestaSrs <- createCRS @StepField
  stepKey <- deriveStepKey @2 vestaSrs stepArt.stepCs
  let realStepVK = stepVkForCircuit (extractStepVKComms @1 stepKey.verifierIndex)
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
  -- slot 0 carries a `two_phase_chain` proof's one accumulator, slot 1
  -- the tag's own two
  let
    dummyAdvice :: WrapAdvice 2 1
    dummyAdvice = unsafeCoerce unit

    slotWidths :: Vector 2 Int
    slotWidths = 1 :< 2 :< Vector.nil
  wrapCs <- compile noAdvice (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMain @1 @2 @1 config stmt dummyAdvice slotWidths)
  wrapKey <- deriveWrapKey @2 pallasSrs wrapCs
  constants <- wrapMainConstants config vestaSrs (stepKey :< Vector.nil) slotWidths
  pure
    { stepCs: stepArt.stepCs
    , stepDomainLog2: stepArt.stepDomainLog2
    , wrapCs
    , wrapVk: extractWrapVKCommsAdvice wrapKey.verifierIndex
    , wrapKey
    , constants
    }
