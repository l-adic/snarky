-- | PureScript-side analog of OCaml's `No_recursion_return` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:89-126` +
-- |  `mina/src/lib/crypto/pickles/dump_no_recursion_return/dump_no_recursion_return.ml`).
-- |
-- | Runs the same N=0 Output-mode rule (`public_output = 0`, no prev
-- | proofs) through the PS step+wrap prover and emits a trace that
-- | should byte-identical-match the OCaml fixture at
-- | `packages/pickles/test/fixtures/no_recursion_return_base_case.trace`
-- | via `tools/no_recursion_return_trace_diff.sh`.
-- |
-- | This is the simplest possible proof-level test — N=0 means no
-- | prev proofs, no verify_one, no heterogeneous advice. The trace
-- | contains only compile.* (stepVK+wrapVK), step.* (one step proof),
-- | wrap.* (one wrap proof), step_main_outer.* (outer-hash sponge),
-- | ivp.* (in-circuit IVP checks), ipa.* (IPA rounds) and the
-- | begin/end markers — no `expand_proof.*` / `msgForNextStep.*` /
-- | `tock_pi.*` since there's no prev proof to run oracles on or
-- | hash into messages_for_next_step_proof.
-- |
-- | This is the FIRST rung of the Tree_proof_return proof-level
-- | ladder: once this converges, we have a PS No_recursion_return
-- | prover that can produce slot-0 proofs for Tree_proof_return.
-- |
-- | Required env vars at runtime:
-- | - `PICKLES_TRACE_FILE` — path to the trace log (truncated).
-- | - `KIMCHI_DETERMINISTIC_SEED` — u64 seed for the patched kimchi RNG.
module Test.Pickles.Prove.NoRecursionReturn
  ( spec
  ) where

import Prelude

import Data.Array as Array
import Data.Int.Bits as Int
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Foldable (for_)
import Pickles.Dummy as Dummy
import Pickles.ProofFFI as ProofFFI
import Pickles.Prove.Step (StepRule, buildStepAdvice, stepCompile)
import Pickles.Prove.Wrap (extractStepVKComms)
import Pickles.Step.Prevs (PrevsSpecNil)
import Pickles.Trace as Trace
import Pickles.Types (StepField, WrapField)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Impl.Vesta as VestaImpl
import Snarky.Circuit.DSL (F(..), FVar, Snarky, const_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Spec (SpecT, describe, it)

-- | The No_recursion_return rule: `output = 0`, N = 0 prev proofs,
-- | Output mode (input = Unit, output = Field).
-- | Reference: test_no_sideloaded.ml:100-107
noRecursionReturnRule :: forall t m. StepRule 0 Unit Unit (F StepField) (FVar StepField) Unit Unit
noRecursionReturnRule _ = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: const_ zero
  }

-- | The loop entry point.
spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.NoRecursionReturn" do
  it "single N=0 Output-mode proof trace matches OCaml fixture" \_ -> do
    liftEffect $ Trace.string "no_recursion_return.begin" "base_case"

    -- ===== SRS setup (same hardcoded depths as Simple_chain) =====
    let pallasWrapSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    let lagrangeSrs = pallasWrapSrs
    vestaSrsLoaded <- liftEffect $ createCRS @StepField
    let vestaSrs = vestaSrsLoaded
    let _pallasProofCrs = pallasWrapSrs

    -- Ro-derived Dummy.Ipa.{Wrap,Step}.sg points used as step_main's
    -- compile-time dummy_sg constant. Unused at N=0 (no verify_one)
    -- but required by stepCompile's type signature.
    let
      dummySgValues = Dummy.computeDummySgValues lagrangeSrs vestaSrs
      wrapSg = dummySgValues.ipa.wrap.sg

    -- OCaml No_recursion_return: default wrap_domains for N0 →
    -- h = 2^13 (common.ml:25-29). No override_wrap_domain.
    let
      wrapDomainLog2 = 13

      srsData =
        -- N=0: all per-slot vectors are nil (no prev slots).
        { perSlotLagrangeAt: Vector.nil
        , blindingH:
            (coerce $ ProofFFI.vestaSrsBlindingGenerator lagrangeSrs)
              :: AffinePoint (F StepField)
        , perSlotFopDomainLog2: Vector.nil
        , perSlotKnownWrapKeys: Vector.nil
        }

      dummySg :: AffinePoint StepField
      dummySg = wrapSg

      ctx =
        { srsData
        , dummySg
        , crs: vestaSrs
        }

      -- Placeholder advice for `stepCompile`. Values unused during
      -- compile — only the spec shape (PrevsSpecNil = len 0) matters.
      placeholderAdvice = buildStepAdvice @PrevsSpecNil
        { publicInput: unit
        , mostRecentWidth: 0
        , wrapDomainLog2
        }

    -- ===== Phase 1: compile the step circuit =====
    -- N=0 Output mode: inputVal=Unit, input=Unit, outputVal=F StepField,
    -- output=FVar StepField, prevInputVal=Unit, prevInput=Unit,
    -- outputSize=1 (= 33*0 + 1, just the msgForNextStep digest).
    stepCR <- liftEffect $
      stepCompile @PrevsSpecNil @1 @Unit @Unit @(F StepField) @(FVar StepField) @Unit @Unit ctx noRecursionReturnRule placeholderAdvice

    -- ===== Emit step VK + compile metadata =====
    -- Mirrors OCaml's `compile.ml` emissions: log_size_of_group of the
    -- step VK's underlying kimchi domain, followed by the structural
    -- domain values and the VK commitment points.
    let stepDomainLog2 = ProofFFI.pallasProverIndexDomainLog2 stepCR.proverIndex
    let stepVkComms = extractStepVKComms stepCR.verifierIndex
    liftEffect do
      Trace.int "compile.stepVK.0.log_size_of_group" stepDomainLog2
      Trace.int "compile.step_domains.0.h.log2" stepDomainLog2
      Trace.int "compile.wrap_domains.h.log2" wrapDomainLog2
      for_ (Array.mapWithIndex Tuple (Vector.toUnfoldable stepVkComms.sigmaComm)) \(Tuple i pt) -> do
        Trace.field ("compile.stepVK.sigma." <> show i <> ".x") (coerce pt.x :: F WrapField)
        Trace.field ("compile.stepVK.sigma." <> show i <> ".y") (coerce pt.y :: F WrapField)
      for_ (Array.mapWithIndex Tuple (Vector.toUnfoldable stepVkComms.coefficientsComm)) \(Tuple i pt) -> do
        Trace.field ("compile.stepVK.coeff." <> show i <> ".x") (coerce pt.x :: F WrapField)
        Trace.field ("compile.stepVK.coeff." <> show i <> ".y") (coerce pt.y :: F WrapField)
      Trace.field "compile.stepVK.generic.x" (coerce stepVkComms.genericComm.x :: F WrapField)
      Trace.field "compile.stepVK.generic.y" (coerce stepVkComms.genericComm.y :: F WrapField)
      Trace.field "compile.stepVK.psm.x" (coerce stepVkComms.psmComm.x :: F WrapField)
      Trace.field "compile.stepVK.psm.y" (coerce stepVkComms.psmComm.y :: F WrapField)
      Trace.field "compile.stepVK.complete_add.x" (coerce stepVkComms.completeAddComm.x :: F WrapField)
      Trace.field "compile.stepVK.complete_add.y" (coerce stepVkComms.completeAddComm.y :: F WrapField)
      Trace.field "compile.stepVK.mul.x" (coerce stepVkComms.mulComm.x :: F WrapField)
      Trace.field "compile.stepVK.mul.y" (coerce stepVkComms.mulComm.y :: F WrapField)
      Trace.field "compile.stepVK.emul.x" (coerce stepVkComms.emulComm.x :: F WrapField)
      Trace.field "compile.stepVK.emul.y" (coerce stepVkComms.emulComm.y :: F WrapField)
      Trace.field "compile.stepVK.endomul_scalar.x" (coerce stepVkComms.endomulScalarComm.x :: F WrapField)
      Trace.field "compile.stepVK.endomul_scalar.y" (coerce stepVkComms.endomulScalarComm.y :: F WrapField)

    -- TODO(iteration-2): wrap compile — needs N=0 wrap infrastructure
    --   (buildWrapMainConfigN0 + NoSlots-typed WrapAdvice).
    -- TODO(iteration-3): step prove.
    -- TODO(iteration-4): wrap prove.

    liftEffect $ Trace.string "no_recursion_return.end" "base_case_verified"
