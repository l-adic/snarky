-- | PureScript-side analog of OCaml's `Simple_chain` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:128-205` +
-- |  `mina/src/lib/crypto/pickles/dump_simple_chain/dump_simple_chain.ml`).
-- |
-- | Runs the exact same inductive rule (`prev + 1`) at
-- | `max_proofs_verified = N1`, base case only (self = 0), through
-- | the generic `Pickles.Prove.Step.stepProve` orchestrator. The trace
-- | file PureScript emits is diffed byte-for-byte against the OCaml
-- | fixture at `packages/pickles/test/fixtures/simple_chain_base_case.trace`
-- | via `tools/simple_chain_trace_diff.sh`.
-- |
-- | This file is the top-level binding for the Simple_chain test —
-- | the ONLY place concrete `n=1` + `stepDomainLog2=16` +
-- | `wrapDomainLog2=14` + `mostRecentWidth=1` appear. Everything
-- | downstream (`Pickles.Prove.Step`, `Pickles.Step.Main`,
-- | `Pickles.Types`) stays polymorphic in `n`, `ds`, `dw`; type
-- | inference unifies them against `stepMain`'s
-- | `StepWitnessM n StepIPARounds WrapIPARounds ...` constraint when
-- | `stepProve` is invoked here.
-- |
-- | Required env vars at runtime:
-- | - `PICKLES_TRACE_FILE` — path to the trace log (truncated).
-- | - `KIMCHI_DETERMINISTIC_SEED` — u64 seed for the patched kimchi RNG.
module Test.Pickles.Prove.SimpleChain
  ( spec
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Tuple (Tuple(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles.Dummy (computeDummySgValues) as Dummy
import Pickles.Prove.Step (StepRule, buildStepAdvice, buildStepAdviceWithOracles, stepCompile, stepSolveAndProve)
import Pickles.Prove.Wrap (WrapAdvice, buildWrapMainConfigN1, extractStepVKComms, wrapCompile, zeroWrapAdvice)
import Pickles.Prove.Wrap (WrapCompileContext) as WP
import Pickles.Wrap.Slots (Slots2)
import Pickles.ProofFFI (vestaSrsBlindingGenerator, vestaSrsLagrangeCommitmentAt) as ProofFFI
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Trace as Trace
import Pickles.Types (StepField, WrapField)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F(..), assertAny_, const_, equals_, exists, not_)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Spec (SpecT, describe, it)
import Control.Monad.Trans.Class (lift) as MT

-- | PureScript translation of the Simple_chain inductive rule, verbatim
-- | from OCaml `dump_simple_chain.ml:62-82` (which itself is verbatim
-- | from `test_no_sideloaded.ml:149-172`):
-- |
-- |     main = fun { public_input = self } ->
-- |       let prev = exists Field.typ ~request:Prev_input in
-- |       let proof = exists (Typ.prover_value ()) ~request:Proof in
-- |       let is_base_case = Field.equal Field.zero self in
-- |       let proof_must_verify = Boolean.not is_base_case in
-- |       let self_correct = Field.(equal (one + prev) self) in
-- |       Boolean.Assert.any [ self_correct; is_base_case ] ;
-- |       { previous_proof_statements = [ { public_input = prev; proof; proof_must_verify } ]
-- |       ; public_output = ()
-- |       ; auxiliary_output = ()
-- |       }
-- |
-- | For the base case (self = 0), `is_base_case` is true so the
-- | assertion passes regardless of `prev`. OCaml's handler supplies
-- | `-1` via `Req.Prev_input`; PureScript can use `0` (the value
-- | doesn't affect the circuit output when `is_base_case = true`).
simpleChainRule :: StepRule 1
simpleChainRule self = do
  -- OCaml `dump_simple_chain.ml:88-95` handler returns
  -- `s_neg_one = Tick.Field.(negate one)`. Match that so the
  -- in-circuit `hashMessagesForNextStepProofOpt` sponge absorbs
  -- `-1` for the prev app_state field, matching what
  -- `dummyWrapTockPublicInput` serializes into the FFI public input.
  prev <- exists $ MT.lift $ pure (F (negate one) :: F StepField)
  isBaseCase <- equals_ (const_ zero) self
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) self
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: proofMustVerify :< Vector.nil
    }

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.SimpleChain" do
  it "base case trace matches OCaml fixture" \_ -> do
    -- Mirror OCaml dump_simple_chain.ml's begin sentinel.
    liftEffect $ Trace.string "simple_chain.begin" "base_case"

    -- ===== SRS + context setup =====
    -- OCaml's Simple_chain loads the Pallas (wrap-side) SRS for the
    -- lagrange basis lookup and the Vesta (step-side) SRS for the
    -- actual step proof creation. Mirror that here.
    lagrangeSrs <- liftEffect PallasImpl.createCRS
    vestaSrs <- liftEffect $ createCRS @StepField
    pallasProofCrs <- liftEffect PallasImpl.createCRS

    -- `Dummy.Ipa.{Wrap,Step}.sg` computed upfront so the step circuit's
    -- compile-time `const_`-wrapped dummy_sg (at `Pickles.Step.Main:465`)
    -- uses the same Ro-derived Pallas point OCaml's step_main bakes in.
    -- Earlier iterations used `{ x: zero, y: zero }` which baked
    -- compile-time zeros into the step constraint system, producing a
    -- step VK that diverged from OCaml's (iter 6 diagnostic confirmed).
    let dummySgValues = Dummy.computeDummySgValues lagrangeSrs vestaSrs
        wrapSg = dummySgValues.ipa.wrap.sg
        stepSg = dummySgValues.ipa.step.sg

    let
      -- OCaml `basic.wrap_domains.h` for N1, from
      -- `dump_circuit_impl.ml:3718-3719`: wrap proof's eval domain = 14.
      wrapDomainLog2 = 14

      -- Step circuit's own kimchi domain log2 for Simple_chain
      -- (`dump_circuit_impl.ml:3721-3723`): 16. Used to size the
      -- wrap's lagrange base lookup over the step VK.
      stepDomainLog2 = 16

      srsData =
        { lagrangeAt:
            mkConstLagrangeBaseLookup \i ->
              (coerce (ProofFFI.vestaSrsLagrangeCommitmentAt lagrangeSrs wrapDomainLog2 i))
                :: AffinePoint (F StepField)
        , blindingH: (coerce $ ProofFFI.vestaSrsBlindingGenerator lagrangeSrs)
            :: AffinePoint (F StepField)
        , fopDomainLog2: wrapDomainLog2
        }

      -- Real Ro-derived Pallas point = Dummy.Ipa.Wrap.sg (OCaml
      -- `dummy.ml:39-40 = Ipa.Wrap.compute_sg challenges`). Used by
      -- step_main as the sg_old padding constant.
      dummySg :: AffinePoint StepField
      dummySg = wrapSg

      ctx =
        { srsData
        , dummySg
        , crs: vestaSrs
        }

      -- Placeholder advice for `stepCompile`. Values aren't inspected
      -- during compile — only the type shape matters — so we pass a
      -- synthetic all-g0-VK advice here. The REAL advice (with oracles
      -- over the compiled wrap VK) is built below for the solver.
      placeholderAdvice = buildStepAdvice
        { appState: F zero
        , mostRecentWidth: 1
        , wrapDomainLog2
        }

    -- ===== Phase 1: compile the step circuit =====
    -- Produces the step prover/verifier index we feed into wrap compile.
    stepCR <- liftEffect $
      stepCompile @1 @34 ctx simpleChainRule placeholderAdvice

    -- === TRACE iter 6: compiled step VK commitments ===
    -- Mirrors OCaml `compile.ml:630-643` `step_vks` emission point.
    -- If these match OCaml byte-for-byte, the step circuit compiles
    -- the same constraint system on both sides and the wrap VK
    -- divergence is isolated to wrap compile config (buildWrapMainConfigN1
    -- or downstream). If they differ, the step circuit itself has an
    -- unexpected divergence from OCaml — memory's "0 diffs in JSON"
    -- claim doesn't extend to the compiled VK.
    let stepVkComms = extractStepVKComms stepCR.verifierIndex
    liftEffect do
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

    -- ===== Phase 2: compile the wrap circuit =====
    -- `buildWrapMainConfigN1` lifts the real step VK commitments into
    -- circuit-variable form for `wrapMain.config.stepKeys`. The wrap
    -- compile itself produces a real `VerifierIndex PallasG WrapField`
    -- that we feed back into the step advice for oracle computation.
    let
      wrapCtx :: WP.WrapCompileContext 1
      wrapCtx =
        { wrapMainConfig:
            buildWrapMainConfigN1 vestaSrs stepCR.verifierIndex stepDomainLog2
        , crs: pallasProofCrs
        }

    -- Simple_chain N1's wrap_main has `Max_widths_by_slot = [N0; N1]`
    -- per `dump_circuit_impl.ml`'s `[[0]; [1]]` padded-vector argument
    -- to `Wrap_main.wrap_main`. That's `slot0Width = 0` (empty) and
    -- `slot1Width = 1`. The `pickles-circuit-diffs` fixture test
    -- `compileWrapMainN1` pins the same `@1 @0 @1` instantiation.
    -- Library-level `zeroWrapAdvice` is polymorphic in the slot widths;
    -- this is the only place in the whole pipeline where the N1 slot
    -- shape is made concrete.
    let n1ZeroAdvice = (zeroWrapAdvice :: WrapAdvice 2 (Slots2 0 1))
    wrapCR <- liftEffect $ wrapCompile wrapCtx n1ZeroAdvice

    -- ===== Phase 3: build real advice with oracles over the real wrap VK =====
    -- OCaml's `step.ml:expand_proof` runs `Tock.Oracles.create` on the
    -- compiled wrap VK + `Proof.dummy` and writes the result into
    -- `fopProofState.plonk.{alpha,beta,gamma,zeta,spongeDigest}`. We do
    -- the same here via `buildStepAdviceWithOracles`.
    -- `wrapSg` and `stepSg` are already computed at the top of the
    -- spec (line ~113) so the step circuit's compile-time `dummy_sg`
    -- constant matches.
    realAdvice <- liftEffect $ buildStepAdviceWithOracles
      { appState: F zero
      , prevAppState: F (negate one) -- OCaml `s_neg_one`
      , mostRecentWidth: 1
      , wrapDomainLog2
      , wrapVK: wrapCR.verifierIndex
      , wrapSg
      , stepSg
      }

    -- ===== Phase 4: run the step solver =====
    result <- liftEffect $
      stepSolveAndProve @1 @34
        (\e -> Exc.throw ("stepSolveAndProve: " <> show e))
        ctx
        simpleChainRule
        stepCR
        realAdvice

    -- ===== Trace the public input array =====
    -- Mirrors mina/src/lib/crypto/pickles/step.ml:828-833 which
    -- iterates over `Backend.Tick.Field.Vector.length public_inputs`
    -- and emits `step.proof.public_input.{i}` per element.
    liftEffect $ for_ (Array.mapWithIndex Tuple result.publicInputs) \(Tuple i x) ->
      Trace.field ("step.proof.public_input." <> show i) x

    liftEffect $ Trace.string "simple_chain.end" "base_case_verified"
