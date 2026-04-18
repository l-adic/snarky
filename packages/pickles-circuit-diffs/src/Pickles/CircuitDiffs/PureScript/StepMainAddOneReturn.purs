module Pickles.CircuitDiffs.PureScript.StepMainAddOneReturn
  ( compileStepMainAddOneReturn
  , StepMainAddOneReturnParams
  , class AddOneReturnAdvice
  ) where

-- | step_main circuit for the Add_one_return rule.
-- |
-- | **N = 0**: no previous proofs, no recursion, no verify_one. The rule
-- | is a single field operation: `output = 1 + input`. This is the
-- | simplest possible Output-mode-style circuit and specifically exercises
-- | the Input_and_output public_input branch of `stepMain` — where the
-- | sponge input for messages_for_next_step_proof is
-- | `(app_state, ret_var)` (OCaml step_main.ml:566-573) rather than just
-- | `app_state` (Input mode) or `ret_var` (Output mode).
-- |
-- | Reference: mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:431-470
-- |            (Add_one_return) — `public_input:(Input_and_output (Field.typ, Field.typ))`,
-- |            `max_proofs_verified:N0`, rule `output = Field.(add one x)`.
-- |
-- | OCaml dump target: `packages/pickles-circuit-diffs/circuits/ocaml/step_main_add_one_return_circuit.json`
-- | produced by the `step_main_add_one_return` entry in
-- | `mina/src/lib/crypto/pickles/dump_circuit_impl.ml`.

import Prelude

import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Unsafe (unsafePerformEffect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyWrapSg)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Step.Main (RuleOutput, stepMain)
import Pickles.Types (StepField)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, const_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type StepMainAddOneReturnParams =
  { lagrangeAt :: LagrangeBaseLookup StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | Application-specific advice for the Add_one_return rule.
-- |
-- | The rule allocates NO witness values — `output = 1 + input` is a
-- | pure in-circuit computation. The class exists only so the stepMain
-- | constraint stays uniform with the other rules; no methods to
-- | implement. The `Effect` instance is automatically satisfied (empty).
class Monad m <= AddOneReturnAdvice m

-- | Compilation instance: no-op (class has no methods). Kept as an
-- | explicit instance for symmetry with SimpleChainAdvice and to make
-- | it clear the rule requires no advice plumbing at all.
instance (Monad m) => AddOneReturnAdvice m

-- | Add_one_return rule: `output = 1 + input`, N = 0 prev proofs.
-- | Reference: test_no_sideloaded.ml:440-452
addOneReturnRule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => AddOneReturnAdvice m
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m (RuleOutput 0 Unit (FVar StepField))
addOneReturnRule x = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: CVar.add_ (const_ one) x
  }

compileStepMainAddOneReturn :: StepMainAddOneReturnParams -> CompiledCircuit StepField
compileStepMainAddOneReturn params = unsafePerformEffect $
  compile (Proxy @Unit) (Proxy @(Vector 1 (F StepField))) (Proxy @(KimchiConstraint StepField))
    -- N=0: output size = 33*0 + 1 = 1 (just the msgForNextStep digest —
    -- no unfinalized_proofs, no messages_for_next_wrap_proof entries).
    -- OCaml step domain log2 = 9 (tiny, no verify_one machinery).
    -- N=0 has no prev proofs, so prevInputVal/prevInput are unused —
    -- pick any concrete CircuitType-havers; Unit works.
    ( \_ -> stepMain @0 @1 @(F StepField) @(FVar StepField) @(F StepField) @(FVar StepField) @Unit @Unit
        addOneReturnRule
        { lagrangeAt: params.lagrangeAt, blindingH: params.blindingH, fopDomainLog2: 13 }
        dummyWrapSg
    )
    Kimchi.initialState
