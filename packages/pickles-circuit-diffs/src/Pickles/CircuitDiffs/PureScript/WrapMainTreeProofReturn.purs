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
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepVKFromCompiled, deriveWrapVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainTreeProofReturn (StepMainTreeProofReturnParams, compileStepMainTreeProofReturn)
import Pickles.Field (StepField, WrapField)
import Pickles.ProofsVerified (ProofsVerified(..))
import Pickles.Wrap.Advice (WrapAdvice)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

compileWrapMainTreeProofReturn
  :: IvpWrapParams
  -> StepMainTreeProofReturnParams
  -> Effect WrapArtifact
compileWrapMainTreeProofReturn { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainTreeProofReturn stepParams
  vestaSrs <- createCRS @StepField
  pallasSrs <- createCRS @WrapField
  realStepVK <- deriveStepVKFromCompiled @1 @2 vestaSrs stepArt.stepCs
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
  wrapCs <- compile noAdvice (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    ( \stmt ->
        wrapMain @1 @2 @1
          config
          stmt
          dummyAdvice
          (0 :< 2 :< Vector.nil)
    )
  wrapVk <- deriveWrapVKFromCompiled @2 pallasSrs wrapCs
  pure
    { stepCs: stepArt.stepCs
    , stepDomainLog2: stepArt.stepDomainLog2
    , wrapCs
    , wrapVk
    }
