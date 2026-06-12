module Pickles.CircuitDiffs.PureScript.StepMainAddOneReturn
  ( compileStepMainAddOneReturn
  , StepMainAddOneReturnParams
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
-- |            (Add_one_return) — `public_input:(Input_and_output (StepField.typ, StepField.typ))`,
-- |            `max_proofs_verified:N0`, rule `output = StepField.(add one x)`.
-- |
-- | OCaml dump target: `packages/pickles-circuit-diffs/circuits/ocaml/step_main_add_one_return_circuit.json`
-- | produced by the `step_main_add_one_return` entry in
-- | `mina/src/lib/crypto/pickles/dump_circuit_impl.ml`.

import Prelude

import Data.Maybe (Maybe(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Ref as Ref
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, dummyWrapSg, mkStepArtifact)
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Step.Advice (StepAdvice)
import Pickles.Step.Main (RuleOutput, stepMain)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (AsProver, F, FVar, Snarky, const_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type StepMainAddOneReturnParams =
  { lagrangeAt :: LagrangeBaseLookup 1 StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | Add_one_return rule: `output = 1 + input`, N = 0 prev proofs.
-- | Reference: test_no_sideloaded.ml:440-452
addOneReturnRule
  :: forall r
   . PrimeField StepField
  => AsProver StepField r Unit
  -> FVar StepField
  -> Snarky StepField (KimchiConstraint StepField) r (RuleOutput 0 Unit (FVar StepField))
addOneReturnRule _ x = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: CVar.add_ (const_ one) x
  }

compileStepMainAddOneReturn
  :: StepMainAddOneReturnParams -> Effect StepArtifact
compileStepMainAddOneReturn params = do
  throwawayCaptureRef <- Ref.new Nothing
  -- `carrier` (value-side per-proof witness carrier) is not determined
  -- by `stepMain`'s var-side `StepSlotsCarrier` constraint; pin it here
  -- (mpv=0 ⇒ empty `Unit` carrier).
  let
    dummyAdvice :: StepAdvice _ _ _ _ _ _ Unit _ _
    dummyAdvice = unsafeCoerce unit
  mkStepArtifact <$> do
    compile noAdvice (Proxy @Unit) (Proxy @(Vector 1 (F StepField))) (Proxy @(KimchiConstraint StepField))
      -- N=0: output size = 33*0 + 1 = 1 (just the msgForNextStep digest —
      -- no unfinalized_proofs, no messages_for_next_wrap_proof entries).
      -- OCaml step domain log2 = 9 (tiny, no verify_one machinery).
      -- N=0 has no prev proofs, so prevInputVal/prevInput are unused —
      -- pick any concrete CircuitType-havers; Unit works.
      -- Single-rule, Nil prevs: len = 0, mpvMax = 0, mpvPad = 0.
      ( \_ -> stepMain @Unit @(F StepField) @(F StepField) @Unit @Unit @0 @1 @Unit @1
          addOneReturnRule
          { perSlotLagrangeAt: Vector.nil
          , blindingH: params.blindingH
          , perSlotFopDomainLog2s: Vector.nil
          , perSlotVkBlueprints: unit
          }
          dummyWrapSg
          -- Side-loaded VK carrier: no side-loaded
          -- slots in Unit, so the carrier is `Unit`.
          unit
          dummyAdvice
          throwawayCaptureRef
      )
