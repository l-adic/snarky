-- | N=2 wrapper for the wrap_main library circuit (Tree_proof_return).
-- |
-- | Configuration: branches=1, step_widths=[2], heterogeneous prev slots
-- | [0, 2] (slot 0 = No_recursion_return proof, slot 1 = Tree_proof_return
-- | self), wrap domain 2^13, Features.none.
-- |
-- | OCaml dump target: `wrap_main_tree_proof_return_circuit.json` produced
-- | by `mina/src/lib/crypto/pickles/dump_circuit_impl.ml` with
-- | `step_widths:[2]`, `padded:[[0];[2]]`, `domain_log2:13`.
module Pickles.CircuitDiffs.PureScript.WrapMainTreeProofReturn
  ( compileWrapMainTreeProofReturn
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepKey, deriveWrapKey)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainTreeProofReturn (StepMainTreeProofReturnParams, compileStepMainTreeProofReturn)
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

compileWrapMainTreeProofReturn
  :: CRS PallasG
  -> IvpWrapParams
  -> StepMainTreeProofReturnParams
  -> Effect WrapArtifact
compileWrapMainTreeProofReturn pallasSrs { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainTreeProofReturn pallasSrs stepParams
  vestaSrs <- createCRS @StepField
  stepKey <- deriveStepKey @2 vestaSrs stepArt.stepCs
  let stepComms = extractStepVKComms @1 stepKey.verifierIndex
  let realStepVK = stepVkForCircuit stepComms
  let

    config :: WrapMainConfig 1 2 1
    config =
      -- N=2 Tree_proof_return: single branch, step_widths=[2].
      -- `domainLog2s` is derived from the step artifact (= 15 for TPR).
      { stepWidths: 2 :< Vector.nil
      , domainLog2s: stepArt.stepDomainLog2 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeTable: \i -> (lagrangeAt i).constant :< Vector.nil
      , blindingH
      , prevWrapDomainPins: (Just N0 :< Just N1 :< Vector.nil) :< Vector.nil
      }
  -- TPR: 2 prev slots, [NRR (n=0); self (n=2)]; slots derived from
  -- PrevsSpec via funcdep.
  let
    dummyAdvice :: WrapAdvice 2 1
    dummyAdvice = unsafeCoerce unit

    slotWidths :: Vector 2 Int
    slotWidths = 0 :< 2 :< Vector.nil
  wrapCs <- compile noAdvice (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    ( \stmt ->
        wrapMain @1 @2 @1
          config
          stmt
          dummyAdvice
          slotWidths
    )
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
