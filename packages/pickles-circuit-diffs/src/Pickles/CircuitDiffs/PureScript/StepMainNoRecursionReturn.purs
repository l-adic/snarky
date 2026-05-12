module Pickles.CircuitDiffs.PureScript.StepMainNoRecursionReturn
  ( compileStepMainNoRecursionReturn
  , StepMainNoRecursionReturnParams
  , class NoRecursionReturnAdvice
  ) where

-- | step_main circuit for the No_recursion_return rule.
-- |
-- | **N = 0**, **Output mode**: no previous proofs, no recursion, no
-- | verify_one. The rule takes no input and returns `output = 0`. This
-- | is the simplest possible Output-mode circuit — exercises the
-- | `Output _ -> ret_var` branch of step_main's hash_messages_for_next_step_proof
-- | absorb (step_main.ml:566-573) where `hashAppFields = varToFields output`
-- | (no input contribution, unlike Add_one_return's Input_and_output mode).
-- |
-- | Dual of Add_one_return at N=0 in terms of max_proofs_verified shape,
-- | differing only in public-input mode (Output vs. Input_and_output).
-- | Precursor to the Tree_proof_return proof-level byte-for-byte test:
-- | Tree_proof_return's slot 0 consumes a real No_recursion_return proof,
-- | so getting No_recursion_return circuit-identical is the first rung.
-- |
-- | Reference: mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:89-126
-- |            (No_recursion_return) — `public_input:(Output StepField.typ)`,
-- |            `max_proofs_verified:N0`, rule `output = StepField.zero`.
-- |
-- | OCaml dump target: `packages/pickles-circuit-diffs/circuits/ocaml/step_main_no_recursion_return_circuit.json`
-- | produced by the `step_main_no_recursion_return` entry in
-- | `mina/src/lib/crypto/pickles/dump_circuit_impl.ml`.

import Prelude

import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, dummyWrapSg, mkStepArtifact)
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Step.Main (RuleOutput, stepMain)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, const_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type StepMainNoRecursionReturnParams =
  { lagrangeAt :: LagrangeBaseLookup StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | Application-specific advice for the No_recursion_return rule.
-- |
-- | The rule allocates NO witness values — `output = 0` is a pure
-- | in-circuit constant. The class exists only so the stepMain
-- | constraint stays uniform with the other rules; no methods to
-- | implement.
class Monad m <= NoRecursionReturnAdvice m

instance (Monad m) => NoRecursionReturnAdvice m

-- | No_recursion_return rule: `output = 0`, N = 0 prev proofs,
-- | Output mode (input = Unit).
-- | Reference: test_no_sideloaded.ml:100-107
noRecursionReturnRule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => NoRecursionReturnAdvice m
  => Unit
  -> Snarky (KimchiConstraint StepField) t m
       (RuleOutput 0 Unit (FVar StepField))
noRecursionReturnRule _ = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: const_ zero
  }

compileStepMainNoRecursionReturn
  :: StepMainNoRecursionReturnParams -> Effect StepArtifact
compileStepMainNoRecursionReturn params =
  mkStepArtifact <$>
    compile (Proxy @Unit) (Proxy @(Vector 1 (F StepField))) (Proxy @(KimchiConstraint StepField))
      -- N=0: output size = 33*0 + 1 = 1 (just the msgForNextStep digest —
      -- no unfinalized_proofs, no messages_for_next_wrap_proof entries).
      -- N=0 has no prev proofs, so prevInputVal/prevInput are unused —
      -- pick any concrete CircuitType-havers; Unit works.
      --
      -- Output mode: inputVal/input are Unit (no caller-supplied input),
      -- outputVal/output are `F StepField` / `FVar StepField` (the returned
      -- field). Contrast Add_one_return's Input_and_output mode where
      -- inputVal/outputVal are both `F StepField`.
      -- Visible axes: @prevsSpec @inputVal @outputVal @prevInputVal
      -- @valCarrier @mpvMax. Implicit: input/output/prevInput (via
      -- CircuitType), mpvPad (MpvPadding), outputSize (Mul/Add chain),
      -- nd (from perSlotFopDomainLog2s shape).
      -- Single-rule, Nil prevs: len = 0, mpvMax = 0, mpvPad = 0.
      -- outputSize = mpvMax*32 + 1 + mpvMax = 1.
      ( \_ -> stepMain @Unit @Unit @(F StepField) @Unit @Unit @0 @1
          noRecursionReturnRule
          { perSlotLagrangeAt: Vector.nil
          , blindingH: params.blindingH
          , perSlotFopDomainLog2s: Vector.nil
          , perSlotVkBlueprints: unit
          }
          dummyWrapSg
          -- Side-loaded VK carrier: no slots, carrier = `Unit`.
          unit
      )
      Kimchi.initialState
