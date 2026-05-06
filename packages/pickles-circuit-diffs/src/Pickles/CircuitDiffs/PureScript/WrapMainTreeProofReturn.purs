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
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, deriveStepVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainTreeProofReturn (StepMainTreeProofReturnParams, compileStepMainTreeProofReturn)
import Pickles.Types (StepField, WrapField)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Pickles.Wrap.Slots (Slots2)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

compileWrapMainTreeProofReturn
  :: IvpWrapParams
  -> StepMainTreeProofReturnParams
  -> Effect (CompiledCircuit WrapField)
compileWrapMainTreeProofReturn { lagrangeAt, blindingH } stepParams = do
  -- Recompile the TPR step CS (mpv=2 with heterogeneous prevs [N0, N2])
  -- and derive its VK commitments. Mirrors the wrap_main_circuit /
  -- wrap_main_n2 / wrap_main_add_one_return fixes — replaces the
  -- dummyVestaPt-based VK whose 27 components share `(1, vestaGenY)`
  -- coords with the real production VK from the kimchi commitment
  -- pipeline.
  stepBuiltState <- compileStepMainTreeProofReturn stepParams
  vestaSrs <- createCRS @StepField
  let
    realStepVK = deriveStepVKFromCompiled @2 vestaSrs stepBuiltState
    config :: WrapMainConfig 1
    config =
      -- N=2 Tree_proof_return: single branch, step_widths=[2].
      -- `domainLog2s` is the STEP proof's evaluation domain log2,
      -- consumed by `Branch_data.Checked.Wrap.pack` as `4 * log2`.
      -- For TPR the step CS rounds to 2^15 (verified empirically:
      -- branch_data row 81's R coeff is `60 = 4*15` in the OCaml
      -- fixture, not 64 = 4*16).
      { stepWidths: 2 :< Vector.nil
      , domainLog2s: 15 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Nothing
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMain @1 @(Slots2 0 2) config stmt)
    Kimchi.initialState
