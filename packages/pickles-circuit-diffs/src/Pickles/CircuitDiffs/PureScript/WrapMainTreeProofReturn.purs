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

import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (Tuple2)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepVKFromCompiled, deriveWrapVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainTreeProofReturn (StepMainTreeProofReturnParams, compileStepMainTreeProofReturn)
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

compileWrapMainTreeProofReturn
  :: IvpWrapParams
  -> StepMainTreeProofReturnParams
  -> Effect WrapArtifact
compileWrapMainTreeProofReturn { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainTreeProofReturn stepParams
  vestaSrs <- createCRS @StepField
  pallasSrs <- createCRS @WrapField
  let
    realStepVK = deriveStepVKFromCompiled @2 vestaSrs stepArt.stepCs

    config :: WrapMainConfig 1
    config =
      -- N=2 Tree_proof_return: single branch, step_widths=[2].
      -- `domainLog2s` is derived from the step artifact (= 15 for TPR).
      { stepWidths: 2 :< Vector.nil
      , domainLog2s: stepArt.stepDomainLog2 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Nothing
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  -- TPR: 2 prev slots, [NRR (n=0); self (n=2)]; slots derived from
  -- PrevsSpec via funcdep.
  wrapCs <- compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    ( \stmt ->
        wrapMainForPrevs @1
          @(Tuple2 (Slot Compiled 0 (StatementIO Unit (F StepField))) (Slot Compiled 2 (StatementIO Unit (F StepField))))
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
