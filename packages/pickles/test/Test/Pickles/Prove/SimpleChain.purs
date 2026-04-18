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

import Control.Monad.Trans.Class (lift) as MT
import Data.Array as Array
import Data.Fin (getFinite)
import Data.Fin (unsafeFinite)
import Data.Foldable (for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Int.Bits as Int
import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw, throwException) as Exc
import Node.Encoding (Encoding(..)) as Enc
import Node.FS.Sync (writeTextFile) as FS
import Node.Process as Process
import Partial.Unsafe (unsafePartial)
import Pickles.Dummy (computeDummySgValues, dummyIpaChallenges, roComputeResult, simpleChainStepDummyFopProofState) as Dummy
import Pickles.Dummy.SimpleChain (simpleChainDummyPlonk, simpleChainDummyPrevEvals)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.Proof.Dummy (dummyWrapProof)
import Pickles.ProofFFI (OraclesResult)
import Pickles.ProofFFI (pallasComputeUT, pallasProofCommitments, pallasProofOpeningPrechallenges, pallasProofOpeningSg, pallasProofOracles, pallasProverIndexDomainLog2, pallasSpongeCheckpointBeforeChallenges, pallasSrsBlindingGenerator, pallasSrsLagrangeCommitmentAt, pallasVerifierIndexDigest, permutationVanishingPolynomial, proofCoefficientEvals, proofIndexEvals, proofSigmaEvals, proofWitnessEvals, proofZEvals, verifyOpeningProof, vestaProofCommitments, vestaProofOpeningDelta, vestaProofOpeningPrechallenges, vestaProofOpeningSg, vestaProofOpeningZ1, vestaProofOpeningZ2, vestaProofOracles, vestaSrsBlindingGenerator, vestaSrsLagrangeCommitmentAt) as ProofFFI
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Prove.Step (StepRule, buildStepAdvice, buildStepAdviceWithOracles, extractWrapVKForStepHash, stepCompile, stepSolveAndProve)
import Pickles.Prove.Step (dummyWrapTockPublicInput)
import Pickles.Prove.Wrap (BuildWrapAdviceInput, WrapAdvice, buildWrapAdvice, buildWrapMainConfigN1, extractStepVKComms, wrapCompile, wrapSolveAndProve, zeroWrapAdvice)
import Pickles.Prove.Wrap (WrapCompileContext) as WP
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure)
import Pickles.Trace as Trace
import Pickles.Types (PaddedLength, StepField)
import Pickles.Types (PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, WrapField, WrapIPARounds)
import Pickles.VerificationKey (StepVK)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProof, hashMessagesForNextWrapProofPureGeneral)
import Pickles.Wrap.Slots (Slots1, slots1)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (constraintSystemToJson) as Kimchi
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Impl.Vesta as VestaImpl
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, UnChecked(..), assertAny_, coerceViaBits, const_, equals_, exists, not_)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, fromInt, toBigInt)
import Snarky.Curves.Class as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (Type2, fromShifted, toShifted)
import Test.Spec (SpecT, describe, it)

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
simpleChainRule :: F StepField -> StepRule 1 (F StepField) (FVar StepField) Unit Unit (F StepField) (FVar StepField)
simpleChainRule prevAppState self = do
  prev <- exists $ MT.lift $ pure prevAppState
  isBaseCase <- equals_ (const_ zero) self
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) self
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: proofMustVerify :< Vector.nil
    , publicOutput: unit
    }

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.SimpleChain" do
  it "base case trace matches OCaml fixture" \_ -> do
    -- Mirror OCaml dump_simple_chain.ml's begin sentinel.
    liftEffect $ Trace.string "simple_chain.begin" "base_case"

    -- ===== SRS + context setup =====
    -- OCaml's Simple_chain uses two SRSes at distinct depths:
    --
    --   * Tick (Vesta) SRS at depth 2^Common.Max_degree.step_log2 = 2^16
    --     for step prover/lagrange basis.
    --   * Tock (Pallas) SRS at depth 2^Common.Max_degree.wrap_log2 = 2^15
    --     for wrap prover/lagrange basis.
    --
    -- The depths are hardcoded per curve in OCaml at
    -- `mina/src/lib/crypto/kimchi_backend/pasta/basic/kimchi_pasta_basic.ml:6,10`
    -- via `Rounds.{Wrap,Step} = Nat.{N15,N16}` and ultimately bottom out at
    -- `Inputs.Urs.create degree` =
    -- `Kimchi_bindings.Protocol.SRS.Fq.create depth` = Rust
    -- `caml_fq_srs_create` = `SRS::<PallasGroup>::create(depth)`.
    --
    -- PS exposes the *same* Rust call as `pallasCrsCreate`, so the
    -- OCaml-faithful path is to call it directly with depth 2^15 for
    -- the Pallas side (instead of `pallasCrsLoadFromCache` which serves
    -- the depth-2^16 step SRS). The wrap VK's `max_poly_size` field is
    -- read from `srs.g.len()` inside kimchi `ProverIndex::create`, so
    -- using a depth-2^15 SRS here is the only way to make the wrap VK
    -- agree with OCaml's `max_poly_size = 32768`. (The field is NOT in
    -- `verifier_index.digest()`, so an `index_digest` match is not
    -- sufficient evidence the SRSes agree — see
    -- `memory/project_simple_chain_max_poly_size_bug.md`.)
    let pallasWrapSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    let lagrangeSrs = pallasWrapSrs
    vestaSrsLoaded <- liftEffect $ createCRS @StepField
    let vestaSrsFresh = VestaImpl.vestaCrsCreate (1 `Int.shl` 16)

    -- DIAGNOSTIC: compare loaded-from-cache vs fresh-created Vesta SRS
    -- to see whether the cached srs-cache/vesta.srs τ matches the fresh
    -- `SRS::<VestaGroup>::create(2^16)` that OCaml wrap_main uses via
    -- `Tick.Keypair.load_urs()` + `set_urs_info []`.
    liftEffect do
      let loadedH = ProofFFI.pallasSrsBlindingGenerator vestaSrsLoaded
      let freshH = ProofFFI.pallasSrsBlindingGenerator vestaSrsFresh
      Trace.field "srs.diag.loaded.H.x" (coerce loadedH.x :: F WrapField)
      Trace.field "srs.diag.loaded.H.y" (coerce loadedH.y :: F WrapField)
      Trace.field "srs.diag.fresh.H.x" (coerce freshH.x :: F WrapField)
      Trace.field "srs.diag.fresh.H.y" (coerce freshH.y :: F WrapField)
      for_ [ 0, 1, 2, 3 ] \i -> do
        let lp = ProofFFI.pallasSrsLagrangeCommitmentAt vestaSrsLoaded 14 i
        let fp = ProofFFI.pallasSrsLagrangeCommitmentAt vestaSrsFresh 14 i
        Trace.field ("srs.diag.loaded.lag14." <> show i <> ".x") (coerce lp.x :: F WrapField)
        Trace.field ("srs.diag.loaded.lag14." <> show i <> ".y") (coerce lp.y :: F WrapField)
        Trace.field ("srs.diag.fresh.lag14." <> show i <> ".x") (coerce fp.x :: F WrapField)
        Trace.field ("srs.diag.fresh.lag14." <> show i <> ".y") (coerce fp.y :: F WrapField)

    let vestaSrs = vestaSrsLoaded
    let pallasProofCrs = pallasWrapSrs

    -- `Dummy.Ipa.{Wrap,Step}.sg` computed upfront so the step circuit's
    -- compile-time `const_`-wrapped dummy_sg (at `Pickles.Step.Main:465`)
    -- uses the same Ro-derived Pallas point OCaml's step_main bakes in.
    -- Earlier iterations used `{ x: zero, y: zero }` which baked
    -- compile-time zeros into the step constraint system, producing a
    -- step VK that diverged from OCaml's (iter 6 diagnostic confirmed).
    let
      dummySgValues = Dummy.computeDummySgValues lagrangeSrs vestaSrs
      wrapSg = dummySgValues.ipa.wrap.sg
      stepSg = dummySgValues.ipa.step.sg

    let
      -- OCaml `basic.wrap_domains.h` for N1, from
      -- `dump_circuit_impl.ml:3718-3719`: wrap proof's eval domain = 14.
      wrapDomainLog2 = 14

      srsData =
        { lagrangeAt:
            mkConstLagrangeBaseLookup \i ->
              (coerce (ProofFFI.vestaSrsLagrangeCommitmentAt lagrangeSrs wrapDomainLog2 i))
                :: AffinePoint (F StepField)
        , blindingH:
            (coerce $ ProofFFI.vestaSrsBlindingGenerator lagrangeSrs)
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
        { publicInput: F zero
        , mostRecentWidth: 1
        , wrapDomainLog2
        }

    -- ===== Phase 1: compile the step circuit =====
    -- Produces the step prover/verifier index we feed into wrap compile.
    stepCR <- liftEffect $
      stepCompile @1 @34 @(F StepField) @(FVar StepField) @Unit @Unit @(F StepField) @(FVar StepField) ctx (simpleChainRule (F (negate one))) placeholderAdvice

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
    --
    -- `stepDomainLog2` is read DYNAMICALLY from the compiled step prover
    -- index (= `Fix_domains.domains` output for the Simple_chain
    -- inductive rule). Previous versions hardcoded 16 (matching the
    -- synthetic `dump_circuit_impl.ml` test config), which didn't match
    -- production's actual ~14. Reading it from the prover index means
    -- this file never has to guess — whatever the compile actually
    -- produced flows through to the wrap compile's `stepKeys` domain.
    let stepDomainLog2 = ProofFFI.pallasProverIndexDomainLog2 stepCR.proverIndex
    let
      wrapCtx :: WP.WrapCompileContext 1
      wrapCtx =
        { wrapMainConfig:
            buildWrapMainConfigN1 vestaSrs stepCR.verifierIndex stepDomainLog2
        , crs: pallasProofCrs
        }

    -- OCaml `dump_simple_chain.ml:55` calls `Pickles.compile_promise`
    -- with `~max_proofs_verified:(module Nat.N1)`, which makes the
    -- production wrap circuit `mpv = 1`. The single slot has width 1
    -- (the rule verifies one previous self-proof). That's
    -- `Slots1 1` — one slot of width 1. PS's wrapMain is now
    -- polymorphic in the slot shape via `PadSlots`, so we just pin
    -- the slots type at the call site here.
    let n1ZeroAdvice = (zeroWrapAdvice :: WrapAdvice 1 (Slots1 1))
    wrapCR <- liftEffect $ wrapCompile @1 @(Slots1 1) wrapCtx n1ZeroAdvice

    -- === TRACE: compiled wrap VK commitments ===
    -- Mirrors OCaml `compile.ml` `compile.wrapVK.*` emission. Diffing
    -- these against OCaml isolates whether the wrap VK divergence is
    -- in the wrap compile itself (= constraint shape / circuit content
    -- differs) or downstream in the extract/hash path.
    -- Wrap VK commitments are Pallas points → coordinates in StepField (Fp).
    -- Diagnostic: shape of PS wrap CS for direct comparison with OCaml.
    liftEffect $ Trace.int "compile.wrapCS.gate_count" (Array.length wrapCR.constraints)
    liftEffect $ Trace.int "compile.wrapCS.public_input_size" (Array.length wrapCR.builtState.publicInputs)

    -- Optional JSON dump of the production wrap CS, gated on the
    -- PICKLES_WRAP_CS_DUMP env var. Mirrors the matching OCaml-side
    -- dump in `compile.ml` so we can do a byte-for-byte JSON diff.
    wrapDumpEnv <- liftEffect $ Process.lookupEnv "PICKLES_WRAP_CS_DUMP"
    case wrapDumpEnv of
      Nothing -> pure unit
      Just path -> liftEffect do
        let json = Kimchi.constraintSystemToJson @WrapField @PallasG wrapCR.constraintSystem
        FS.writeTextFile Enc.UTF8 path json

    let wrapVkComms = extractWrapVKForStepHash wrapCR.verifierIndex
    liftEffect do
      for_ (Array.mapWithIndex Tuple (Vector.toUnfoldable wrapVkComms.sigmaComm)) \(Tuple i pt) -> do
        Trace.field ("compile.wrapVK.sigma." <> show i <> ".x") pt.x
        Trace.field ("compile.wrapVK.sigma." <> show i <> ".y") pt.y
      for_ (Array.mapWithIndex Tuple (Vector.toUnfoldable wrapVkComms.coefficientsComm)) \(Tuple i pt) -> do
        Trace.field ("compile.wrapVK.coeff." <> show i <> ".x") pt.x
        Trace.field ("compile.wrapVK.coeff." <> show i <> ".y") pt.y
      Trace.field "compile.wrapVK.generic.x" wrapVkComms.genericComm.x
      Trace.field "compile.wrapVK.generic.y" wrapVkComms.genericComm.y
      Trace.field "compile.wrapVK.psm.x" wrapVkComms.psmComm.x
      Trace.field "compile.wrapVK.psm.y" wrapVkComms.psmComm.y
      Trace.field "compile.wrapVK.complete_add.x" wrapVkComms.completeAddComm.x
      Trace.field "compile.wrapVK.complete_add.y" wrapVkComms.completeAddComm.y
      Trace.field "compile.wrapVK.mul.x" wrapVkComms.mulComm.x
      Trace.field "compile.wrapVK.mul.y" wrapVkComms.mulComm.y
      Trace.field "compile.wrapVK.emul.x" wrapVkComms.emulComm.x
      Trace.field "compile.wrapVK.emul.y" wrapVkComms.emulComm.y
      Trace.field "compile.wrapVK.endomul_scalar.x" wrapVkComms.endomulScalarComm.x
      Trace.field "compile.wrapVK.endomul_scalar.y" wrapVkComms.endomulScalarComm.y

    -- ===== Phase 3: build real advice with oracles over the real wrap VK =====
    -- OCaml's `step.ml:expand_proof` runs `Tock.Oracles.create` on the
    -- compiled wrap VK + `Proof.dummy` and writes the result into
    -- `fopProofState.plonk.{alpha,beta,gamma,zeta,spongeDigest}`. We do
    -- the same here via `buildStepAdviceWithOracles`.
    -- `wrapSg` and `stepSg` are already computed at the top of the
    -- spec (line ~113) so the step circuit's compile-time `dummy_sg`
    -- constant matches.
    let
      baseCaseDummyChalPoly =
        { sg: wrapSg, challenges: Dummy.dummyIpaChallenges.wrapExpanded }
      baseCaseWrapPI = dummyWrapTockPublicInput
        { mostRecentWidth: 1
        , wrapDomainLog2
        , wrapVK: wrapCR.verifierIndex
        , prevPublicInput: F (negate one)
        , wrapSg
        , stepSg
        , msgWrapDigest: hashMessagesForNextWrapProofPureGeneral
            { sg: stepSg
            , paddedChallenges:
                Dummy.dummyIpaChallenges.wrapExpanded
                  :< Dummy.dummyIpaChallenges.wrapExpanded
                  :< Vector.nil
            }
        }
    { advice: realAdvice, challengePolynomialCommitment: b0ChalPolyComm } <- liftEffect $ buildStepAdviceWithOracles
      { publicInput: F zero
      , prevPublicInput: F (negate one) -- OCaml `s_neg_one`
      , mostRecentWidth: 1
      , wrapDomainLog2
      , wrapVK: wrapCR.verifierIndex
      , wrapSg
      , stepSg
      , wrapProof: dummyWrapProof
      , wrapPublicInput: baseCaseWrapPI
      , prevChalPolys:
          baseCaseDummyChalPoly :< baseCaseDummyChalPoly :< Vector.nil
            :: Vector PaddedLength _

      , wrapPlonkRaw: simpleChainDummyPlonk
      , wrapPrevEvals: simpleChainDummyPrevEvals
      , wrapBranchData:
          { domainLog2: fromInt wrapDomainLog2 :: StepField
          , proofsVerifiedMask: false :< true :< Vector.nil
          }
      , wrapSpongeDigest: zero
      , mustVerify: false
      , wrapOwnPaddedBpChals:
          -- Base case: dummy wrap proof has dummy bp chals in both slots.
          Dummy.dummyIpaChallenges.wrapExpanded
            :< Dummy.dummyIpaChallenges.wrapExpanded
            :< Vector.nil
      , fopState: Dummy.simpleChainStepDummyFopProofState { proofsVerified: 1 }
      -- b0: advice.evals mirrors the compile-time placeholder
      -- (= Ro-derived r.stepDummyPrevEvals) so the step_b0 witness stays
      -- byte-identical to OCaml. Verified empirically: changing to
      -- simpleChainDummyPrevEvals here diverges step_b0 at row 0 despite
      -- both being nominally "dummy prev_evals".
      , stepAdvicePrevEvals: Dummy.roComputeResult.stepDummyPrevEvals
      -- b0: kimchi prev_challenges.challenges for prev = dummy wrap.
      -- Per proof.ml:143, dummy wrap's deferred_values.bulletproof_challenges
      -- = Dummy.Ipa.Step.challenges. Expanded via Ipa.Step.compute_challenges
      -- = `dummyIpaChallenges.stepExpanded` in PS.
      , kimchiPrevChallengesExpanded: Dummy.dummyIpaChallenges.stepExpanded
      , prevChallengesForStepHash: Dummy.dummyIpaChallenges.stepExpanded
      }

    -- ===== Phase 4: run the step solver =====
    result <- liftEffect $
      stepSolveAndProve @1 @34 @(F StepField) @(FVar StepField) @Unit @Unit @(F StepField) @(FVar StepField)
        (\e -> Exc.throw ("stepSolveAndProve: " <> show e))
        ctx
        (simpleChainRule (F (negate one)))
        stepCR
        realAdvice

    -- ===== Trace the public input array =====
    -- Mirrors mina/src/lib/crypto/pickles/step.ml:828-833 which
    -- iterates over `Backend.Tick.Field.Vector.length public_inputs`
    -- and emits `step.proof.public_input.{i}` per element.
    liftEffect $ for_ (Array.mapWithIndex Tuple result.publicInputs) \(Tuple i x) ->
      Trace.field ("step.proof.public_input." <> show i) x

    -- ===== Validate PS's step proof via kimchi's full batch_verify =====
    -- This is a self-contained check: does the step proof we just
    -- produced actually verify against its own verifier index? If yes,
    -- the proof is internally valid (matches OCaml or not) and any
    -- wrap-side IPA failure is a bug in the wrap circuit. If no, the
    -- step prover has a hidden bug that verifyProverIndex (constraint
    -- satisfaction only) didn't catch.
    let
      stepProofValid = ProofFFI.verifyOpeningProof
        stepCR.verifierIndex
        { proof: result.proof, publicInput: result.publicInputs }
    liftEffect $ Trace.int "step.proof.self_verify" (if stepProofValid then 1 else 0)
    when (not stepProofValid)
      $ liftEffect
      $ Exc.throw "PS step proof FAILED kimchi batch_verify — step prover bug"

    -- DIAG: dump step proof's actual opening values from the raw proof.
    -- These MUST match what the wrap circuit's Req.Openings_proof sees.
    -- If they don't, the advice construction is reading wrong bytes.
    liftEffect do
      let stepSg = ProofFFI.pallasProofOpeningSg result.proof
      Trace.field "step.proof.opening.sg.x" stepSg.x
      Trace.field "step.proof.opening.sg.y" stepSg.y
      -- Dump kimchi's ground-truth 128-bit prechallenges for PS step proof.
      -- These are the pre-endo-expansion scalars — same format as the
      -- wrap circuit's `scalarChallenges` from `bulletReduceCircuit`.
      let
        kimchiPrechals = ProofFFI.pallasProofOpeningPrechallenges
          stepCR.verifierIndex
          { proof: result.proof
          , publicInput: result.publicInputs
          , prevChallenges:
              [ { sgX: stepSg.x
                , sgY: stepSg.y
                , challenges: Vector.toUnfoldable Dummy.dummyIpaChallenges.stepExpanded
                }
              ]
          }
      for_ (Array.mapWithIndex Tuple kimchiPrechals) \(Tuple i c) ->
        Trace.field ("kimchi.prechal." <> show i) c
      -- Dump kimchi's `u_t` scalar (post-CIP-absorb, pre-group_map) for
      -- PS step proof. Compare to PS wrap circuit `ipa.dbg.u_t` to test
      -- whether the sponge state diverges AT the CIP absorb / u squeeze.
      let
        kimchiUT = ProofFFI.pallasComputeUT
          stepCR.verifierIndex
          { proof: result.proof, publicInput: result.publicInputs }
      Trace.field "kimchi.u_t" kimchiUT

    -- ===== Phase 5: wrap-prove the step proof =====
    -- Mirrors OCaml `wrap.ml:279` `Wrap.wrap` orchestration for the
    -- Simple_chain base case. The wrap prover takes the step proof and:
    --  1. runs Fp-sponge oracles on it to derive the wrap statement's
    --     deferred_values,
    --  2. packs them + the two messages digests into the wrap_main public
    --     input (via `assembleWrapMainInput`),
    --  3. builds `WrapAdvice` from the step proof + dummy previous-proof
    --     data (base case = no real prev wrap proofs),
    --  4. runs `wrapSolveAndProve` against the already-compiled wrap
    --     circuit (`wrapCR`).
    --
    -- All the step-field parameters (endo, generator, shifts, etc.) come
    -- from the step prover index's actual domain_log2 (read dynamically
    -- as `stepDomainLog2` above), so this path doesn't hardcode values
    -- that would diverge from OCaml if the step circuit changes.

    let
      stepOracles :: OraclesResult StepField
      stepOracles = ProofFFI.pallasProofOracles stepCR.verifierIndex
        { proof: result.proof
        , publicInput: result.publicInputs
        -- Simple_chain N1 base case: the step proof verifies one prev
        -- wrap proof which is the dummy. Its Fp-scalar bulletproof
        -- challenges are `dummyIpaChallenges.stepExpanded`, and its sg
        -- is the dummy Vesta sg from `computeDummySgValues.ipa.step.sg`
        -- (base field = Fq = WrapField coords).
        , prevChallenges:
            [ { sgX: stepSg.x
              , sgY: stepSg.y
              , challenges: Vector.toUnfoldable Dummy.dummyIpaChallenges.stepExpanded
              }
            ]
        }

      stepAllEvals :: AllEvals StepField
      stepAllEvals =
        { ftEval1: stepOracles.ftEval1
        , publicEvals:
            { zeta: stepOracles.publicEvalZeta
            , omegaTimesZeta: stepOracles.publicEvalZetaOmega
            }
        , zEvals: ProofFFI.proofZEvals result.proof
        , witnessEvals: ProofFFI.proofWitnessEvals result.proof
        , coeffEvals: ProofFFI.proofCoefficientEvals result.proof
        , sigmaEvals: ProofFFI.proofSigmaEvals result.proof
        , indexEvals: ProofFFI.proofIndexEvals result.proof
        }

      stepEndoScalar :: StepField
      stepEndoScalar =
        let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

      wrapDvInput :: WrapDeferredValuesInput 1
      wrapDvInput =
        { proof: result.proof
        , verifierIndex: stepCR.verifierIndex
        , publicInput: result.publicInputs
        , allEvals: stepAllEvals
        , pEval0Chunks: [ stepOracles.publicEvalZeta ]
        , domainLog2: stepDomainLog2
        , zkRows: 3
        , srsLengthLog2: 16
        , generator: (domainGenerator stepDomainLog2 :: StepField)
        , shifts: (domainShifts stepDomainLog2 :: Vector 7 StepField)
        , vanishesOnZk: ProofFFI.permutationVanishingPolynomial
            { domainLog2: stepDomainLog2, zkRows: 3, pt: stepOracles.zeta }
        , omegaForLagrange: \_ -> one
        , endo: stepEndoScalar
        , linearizationPoly: Linearization.pallas
        , prevSgs: stepSg :< Vector.nil
        , prevChallenges: Dummy.dummyIpaChallenges.stepExpanded :< Vector.nil
        -- Simple_chain N1: single-slot mask = [mask0=false, mask1=true].
        , proofsVerifiedMask: false :< true :< Vector.nil
        }

      wrapDv = wrapComputeDeferredValues wrapDvInput

      -- `messages_for_next_step_proof` for the wrap statement comes from
      -- recomputing the step-side hash over the wrap VK + app_state +
      -- prev_wrap_sgs + expanded prev_wrap_bp_chals. For the base case,
      -- appState is the step's own self (= zero), the prev wrap proof's
      -- sg is `Dummy.Ipa.Wrap.sg` (Pallas = StepField coords), and the
      -- expanded prev wrap bp chals are `dummyIpaChallenges.wrapExpanded`.
      -- OCaml's `wrap.ml:316-332` computes the walked `messages_for_next_step_proof`
      -- via `Common.hash_messages_for_next_step_proof` applied to the NEW step
      -- proof's OUTPUT reduced messages record (app_state=next_state=0,
      -- sgs=Ipa.Wrap.compute_sg new_bp_chals, chals=new_bp_chals). That value is
      -- byte-identical to the in-circuit hash result the step circuit wrote to
      -- step PI[32] at step_main.ml:540-659, because both hash the same data.
      -- PS's step circuit is gate-equivalent to OCaml (hash_messages_for_next_step_proof_circuit
      -- diff passes) and writes the correct value to PI[32], so reading it here
      -- is faithful to OCaml. (`hashMessagesForNextStepProofPure` is also faithful
      -- in principle but was being called with the dummy's inputs, not the new
      -- step's outputs — that's a bug in the pure-code call site which is
      -- tracked separately; the in-circuit path is authoritative for this test.)
      msgForNextStepDigest :: StepField
      msgForNextStepDigest = unsafePartial $ fromJust $
        Array.index result.publicInputs 32

      -- `messages_for_next_wrap_proof` for the wrap statement is the
      -- hash of the NEW wrap proof's own state: its `sg` (carried over
      -- from the step proof's opening, per OCaml `wrap.ml:541-556`) and
      -- its old bulletproof challenges padded to Padded_length=2.
      --
      -- For Simple_chain N1 base case both slots of the padded-length-2
      -- challenge array are the same dummy wrap challenges.
      wrapProofSg :: AffinePoint WrapField
      wrapProofSg = ProofFFI.pallasProofOpeningSg result.proof

      -- Wrap-hack padding slot: OCaml's `Wrap_hack.pad_challenges`
      -- prepends `Dummy.Ipa.Wrap.challenges_computed` = expanded wrap
      -- dummy raw chals. PS mirror: `dummyIpaChallenges.wrapExpanded`.
      msgForNextWrapDummyChals :: Vector WrapIPARounds WrapField
      msgForNextWrapDummyChals =
        map (fromBigInt <<< toBigInt) Dummy.dummyIpaChallenges.wrapExpanded

      -- Real slot (base case): OCaml's wrap prover reads
      -- `step_statement.proof_state.unfinalized_proofs[0].deferred_values.bulletproof_challenges`
      -- (the 128-bit raw prechals the step circuit stored) and prepares
      -- them via `Ipa.Wrap.compute_challenges` = expand via
      -- `Endo.Step_inner_curve.scalar = Pallas.endo_scalar` into WrapField.
      -- The wrap IVP's FOP reads the SAME raw prechals and expands them
      -- via `scalar_to_field` which uses the same endo. These are the
      -- values being hashed — NOT `dummyIpaChallenges.wrapExpanded`,
      -- which is derived from `Dummy.Ipa.Wrap.challenges` (a different
      -- Ro-derived vector used for Wrap_hack PADDING only).
      PerProofUnfinalized stepUnfRec0 =
        Vector.head realAdvice.publicUnfinalizedProofs

      msgForNextWrapWrapEndo :: WrapField
      msgForNextWrapWrapEndo =
        let
          Curves.EndoScalar e = Curves.endoScalar @Pallas.BaseField @WrapField
        in
          e

      msgForNextWrapRealChals :: Vector WrapIPARounds WrapField
      msgForNextWrapRealChals =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF.SizedF 128 WrapField)
                msgForNextWrapWrapEndo
          )
          stepUnfRec0.bulletproofChallenges

      msgForNextWrapDigest :: WrapField
      msgForNextWrapDigest =
        hashMessagesForNextWrapProof
          { sg: wrapProofSg
          , expandedChallenges: msgForNextWrapRealChals
          , dummyChallenges: msgForNextWrapDummyChals
          }

    let
      wrapPublicInput = assembleWrapMainInput
        { deferredValues: wrapDv
        , messagesForNextStepProofDigest: msgForNextStepDigest
        , messagesForNextWrapProofDigest: msgForNextWrapDigest
        }

      -- ===== Build WrapAdvice for base case =====
      --
      -- CRITICAL: `prevUnfinalizedProofs[0]` in the wrap advice must
      -- represent the SAME values that the step circuit packed into the
      -- step proof's public_input. We get those directly from
      -- `realAdvice.publicUnfinalizedProofs` (which is what the step
      -- circuit wrote at solve time), converting each Type2-SplitField-
      -- StepField field to Type2-WrapField via cross-field `Shifted`:
      --
      --   `fromShifted :: Type2 (SplitField (F StepField) Boolean) -> F WrapField`
      --     — instance at Shifted.purs:353, recovers the ORIGINAL wrap-field
      --     value the step circuit cross-field-coerced from.
      --
      --   `toShifted :: F WrapField -> Type2 (F WrapField)`
      --     — instance at Shifted.purs:389, repackages as same-field Type2
      --     for `BuildWrapAdviceInput`. wrap_main's `splitPerProofUnfinalized`
      --     re-splits these to `Type2 (SplitField (F WrapField) Boolean)`
      --     which feeds into the in-circuit `publicInputCommit` MSM.
      PerProofUnfinalized stepUnfRec = Vector.head realAdvice.publicUnfinalizedProofs

      stepPerProof
        :: PerProofUnfinalized WrapIPARounds (Type2 (F WrapField))
             (F WrapField)
             Boolean
      stepPerProof = PerProofUnfinalized
        { combinedInnerProduct: toShifted (fromShifted stepUnfRec.combinedInnerProduct :: F WrapField)
        , b: toShifted (fromShifted stepUnfRec.b :: F WrapField)
        , zetaToSrsLength: toShifted (fromShifted stepUnfRec.zetaToSrsLength :: F WrapField)
        , zetaToDomainSize: toShifted (fromShifted stepUnfRec.zetaToDomainSize :: F WrapField)
        , perm: toShifted (fromShifted stepUnfRec.perm :: F WrapField)
        , spongeDigest: F (fromBigInt (toBigInt (case stepUnfRec.spongeDigest of F x -> x)) :: WrapField)
        , beta: UnChecked (coerceViaBits (case stepUnfRec.beta of UnChecked v -> v))
        , gamma: UnChecked (coerceViaBits (case stepUnfRec.gamma of UnChecked v -> v))
        , alpha: UnChecked (coerceViaBits (case stepUnfRec.alpha of UnChecked v -> v))
        , zeta: UnChecked (coerceViaBits (case stepUnfRec.zeta of UnChecked v -> v))
        , xi: UnChecked (coerceViaBits (case stepUnfRec.xi of UnChecked v -> v))
        , bulletproofChallenges:
            map (\(UnChecked v) -> UnChecked (coerceViaBits v)) stepUnfRec.bulletproofChallenges
        , shouldFinalize: stepUnfRec.shouldFinalize
        }

      -- OCaml Req.Step_accs = messages_for_next_wrap_proof.challenge_polynomial_commitment.
      -- For the base case, `messages_for_next_wrap_proof` comes from the dummy
      -- step statement, so this is the dummy step sg (Vesta point). Its coords
      -- are in Vesta's base field = Fq = WrapField.
      -- This must match wrapDvInput.prevSgs (= stepSg = dummySgValues.ipa.step.sg)
      -- so the wrap IVP sponge and pallasProofOracles absorb the same prev
      -- challenge polys (which determines plonk.beta via ivp_assert_plonk_beta).
      dummyStepAccPoint :: WeierstrassAffinePoint VestaG (F WrapField)
      dummyStepAccPoint = WeierstrassAffinePoint
        { x: F stepSg.x, y: F stepSg.y }

      -- OCaml Req.Old_bulletproof_challenges returns Challenges_vector.Prepared.t
      -- = Tock.Field (= Fq = WrapField) vectors of size Wrap_bp_vec = 15,
      -- expanded via Ipa.Wrap.compute_challenges (Pallas.endo_scalar).
      -- For base case, messages_for_next_wrap_proof[0].old_bulletproof_challenges
      -- stores the bp chals of the prev wrap proof the step verified. For
      -- Simple_chain N1 base case that is the dummy wrap proof, and
      -- `dummyIpaChallenges.wrapExpanded` is exactly those chals expanded via
      -- the wrap endo. Different from wrapDvInput.prevChallenges (which is
      -- stepExpanded, size 16, step's natural field) because that feeds the
      -- STEP verifier's kimchi oracles, not the wrap IVP sponge.
      dummyWrapBpChals :: Vector WrapIPARounds (F WrapField)
      dummyWrapBpChals =
        map (F <<< fromBigInt <<< toBigInt) Dummy.dummyIpaChallenges.wrapExpanded

      -- OCaml Req.Evals returns `prev_evals` = evals extracted from each
      -- prev wrap proof's `openings.evals + ft_eval1` (step.ml:987-995).
      -- For the base case, the prev wrap proof IS the dummy wrap proof,
      -- whose `openings.evals` = `Dummy.evals` (dummy.ml:7-20) generated
      -- via `Ro.tock ()` = WrapField (Tock/Fq) values.
      -- PS mirror: `Dummy.roComputeResult.wrapDummyEvals` is built from
      -- the same tock() sequence and is typed as `AllEvals WrapField`.
      de_debug = Dummy.roComputeResult.wrapDummyEvals

      -- CRUCIAL FIX: publicEvals for the wrap advice must come from running
      -- vestaProofOracles on the DUMMY WRAP proof (what step.ml:402 does
      -- via `let x_hat = O.(p_eval_1 o, p_eval_2 o)`), NOT from Dummy.evals'
      -- own fresh Ro.tock() pulls. OCaml combines these at step.ml:1023-1036:
      -- the `evals` field comes from Dummy.evals (Ro.tock), but `public_input`
      -- uses the oracle x_hats. The oracle input here mirrors what the step
      -- prover internally passes to vestaProofOracles when verifying the
      -- dummy wrap proof in base case.
      dummyWrapXhat :: { zeta :: WrapField, omegaTimesZeta :: WrapField }
      dummyWrapXhat =
        let
          toFFI r = { sgX: r.sg.x, sgY: r.sg.y, challenges: Vector.toUnfoldable r.challenges }
          o = ProofFFI.vestaProofOracles wrapCR.verifierIndex
            { proof: dummyWrapProof
            , publicInput: baseCaseWrapPI
            , prevChallenges: map toFFI [ baseCaseDummyChalPoly, baseCaseDummyChalPoly ]
            }
        in
          { zeta: o.publicEvalZeta, omegaTimesZeta: o.publicEvalZetaOmega }

      realPrevEvalsW :: StepAllEvals (F WrapField)
      realPrevEvalsW =
        let
          de = Dummy.roComputeResult.wrapDummyEvals
          pe pe' = PointEval { zeta: F pe'.zeta, omegaTimesZeta: F pe'.omegaTimesZeta }
        in
          StepAllEvals
            { ftEval1: F de.ftEval1
            , publicEvals: PointEval
                { zeta: F dummyWrapXhat.zeta
                , omegaTimesZeta: F dummyWrapXhat.omegaTimesZeta
                }
            , zEvals: pe de.zEvals
            , witnessEvals: map pe de.witnessEvals
            , coeffEvals: map pe de.coeffEvals
            , sigmaEvals: map pe de.sigmaEvals
            , indexEvals: map pe de.indexEvals
            }

      wrapAdviceInput :: BuildWrapAdviceInput 1 (Slots1 1)
      wrapAdviceInput =
        { stepProof: result.proof
        , whichBranch: F zero
        , prevUnfinalizedProofs: stepPerProof :< Vector.nil
        , prevMessagesForNextStepProofHash:
            F (fromBigInt (toBigInt msgForNextStepDigest) :: WrapField)
        , prevStepAccs: dummyStepAccPoint :< Vector.nil
        , prevOldBpChals: slots1 (dummyWrapBpChals :< Vector.nil)
        , prevEvals: realPrevEvalsW :< Vector.nil
        , prevWrapDomainIndices: F (fromInt 1 :: WrapField) :< Vector.nil
        }

      wrapAdvice :: WrapAdvice 1 (Slots1 1)
      wrapAdvice = buildWrapAdvice wrapAdviceInput

      wrapProveCtx =
        { wrapMainConfig: wrapCtx.wrapMainConfig
        , crs: pallasProofCrs
        , publicInput: wrapPublicInput
        , advice: wrapAdvice
        , kimchiPrevChallenges:
            let
              -- Padding slot: Dummy.Ipa.Wrap.sg + Dummy.Ipa.Wrap.challenges_computed
              padEntry =
                { sgX: wrapSg.x
                , sgY: wrapSg.y
                , challenges: map (fromBigInt <<< toBigInt)
                    Dummy.dummyIpaChallenges.wrapExpanded
                }
              -- Real slot: b0's computed challenge_polynomial_commitment
              -- (= Ipa.Wrap.compute_sg(new_bp_chals)) + expand(step.unf[0].deferred.bp_chals)
              realEntry =
                { sgX: b0ChalPolyComm.x
                , sgY: b0ChalPolyComm.y
                , challenges: msgForNextWrapRealChals
                }
            in
              padEntry :< realEntry :< Vector.nil
        }

    -- DIAG: wrapDv.plonk.beta should match OCaml b1 plonk0.beta = 41619386...
    liftEffect $ Trace.field "diag.wrapDv.plonk.beta" (SizedF.toField wrapDv.plonk.beta)

    -- DIAG: dump wrapDummyEvals.indexEvals (the 6 selector evals that get
    -- absorbed at FOP step4_sponge's abs_ie_0..5). Row 445 divergence is at
    -- abs_ie_1/poseidon — these values determine what gets absorbed there.
    liftEffect do
      Trace.field "diag.wrapDummyEvals.ftEval1" de_debug.ftEval1
      Trace.field "diag.wrapDummyEvals.publicEvals.zeta" de_debug.publicEvals.zeta
      Trace.field "diag.wrapDummyEvals.publicEvals.omegaTimesZeta" de_debug.publicEvals.omegaTimesZeta
      Trace.field "diag.wrapDummyEvals.zEvals.zeta" de_debug.zEvals.zeta
      Trace.field "diag.wrapDummyEvals.zEvals.omegaTimesZeta" de_debug.zEvals.omegaTimesZeta
      for_ (Array.mapWithIndex Tuple (Vector.toUnfoldable de_debug.indexEvals :: Array _)) \(Tuple i pe) -> do
        Trace.field ("diag.wrapDummyEvals.indexEvals." <> show i <> ".zeta") pe.zeta
        Trace.field ("diag.wrapDummyEvals.indexEvals." <> show i <> ".omegaTimesZeta") pe.omegaTimesZeta
      for_ (Array.mapWithIndex Tuple (Vector.toUnfoldable de_debug.witnessEvals :: Array _)) \(Tuple i pe) -> do
        Trace.field ("diag.wrapDummyEvals.witnessEvals." <> show i <> ".zeta") pe.zeta
        Trace.field ("diag.wrapDummyEvals.witnessEvals." <> show i <> ".omegaTimesZeta") pe.omegaTimesZeta
      for_ (Array.mapWithIndex Tuple (Vector.toUnfoldable de_debug.coeffEvals :: Array _)) \(Tuple i pe) -> do
        Trace.field ("diag.wrapDummyEvals.coeffEvals." <> show i <> ".zeta") pe.zeta
        Trace.field ("diag.wrapDummyEvals.coeffEvals." <> show i <> ".omegaTimesZeta") pe.omegaTimesZeta
      for_ (Array.mapWithIndex Tuple (Vector.toUnfoldable de_debug.sigmaEvals :: Array _)) \(Tuple i pe) -> do
        Trace.field ("diag.wrapDummyEvals.sigmaEvals." <> show i <> ".zeta") pe.zeta
        Trace.field ("diag.wrapDummyEvals.sigmaEvals." <> show i <> ".omegaTimesZeta") pe.omegaTimesZeta

    -- Diagnostic: dump what kimchi's pallasProofOracles computed for beta
    -- directly from the step proof + prev_challenges. This is the RHS
    -- the wrap IVP's in-circuit sponge is expected to match.
    liftEffect do
      Trace.field "wrap.dbg.oracles_beta"
        (SizedF.toField stepOracles.beta :: StepField)
      Trace.field "wrap.dbg.oracles_gamma"
        (SizedF.toField stepOracles.gamma :: StepField)
      Trace.field "wrap.dbg.oracles_fq_digest" stepOracles.fqDigest
      -- Ground-truth CIP kimchi computes for PS's step proof. Compare
      -- to PS wrap circuit's `ipa.dbg.cip_absorb.0` (= Type1-shifted
      -- form of `stmt.combinedInnerProduct`). Differences here prove
      -- PS's `wrapComputeDeferredValues` is producing the wrong CIP.
      Trace.field "kimchi.cip" stepOracles.combinedInnerProduct
      -- Ground-truth sponge state after absorbing CIP and before u_t
      -- squeeze. Compare to PS wrap's `ipa.dbg.sponge_post.s{0,1,2}`.
      -- Divergence here means PS's circuit-sponge absorb differs from
      -- kimchi's native Poseidon absorb for the same CIP value.
      let
        kimchiCheckpoint = ProofFFI.pallasSpongeCheckpointBeforeChallenges
          stepCR.verifierIndex
          { proof: result.proof, publicInput: result.publicInputs }
      Trace.field "kimchi.sponge_post.s0" (Vector.index kimchiCheckpoint.state (unsafeFinite @3 0))
      Trace.field "kimchi.sponge_post.s1" (Vector.index kimchiCheckpoint.state (unsafeFinite @3 1))
      Trace.field "kimchi.sponge_post.s2" (Vector.index kimchiCheckpoint.state (unsafeFinite @3 2))
      Trace.string "kimchi.sponge_post.mode" kimchiCheckpoint.spongeMode
      Trace.int "kimchi.sponge_post.mode_count" kimchiCheckpoint.modeCount
      Trace.field "wrap.dbg.kimchi_vk_digest"
        (ProofFFI.pallasVerifierIndexDigest stepCR.verifierIndex)
      -- Trace each element of result.publicInputs for direct comparison
      -- with OCaml's step.proof.public_input.* (which already matches),
      -- and against what PS's PackedStepPublicInput would serialize to.
      for_ (Array.mapWithIndex Tuple result.publicInputs) \(Tuple i x) ->
        Trace.field ("wrap.dbg.step_pi." <> show i) x
      -- Trace step proof's w_comm. The wrap circuit's IVP absorbs
      -- these into its sponge; if they don't match the OCaml trace
      -- (`ivp.trace.wrap.w_comm.*`), then PS's step prover produced
      -- a different witness than OCaml's despite identical PI.
      let stepCommits = ProofFFI.pallasProofCommitments result.proof
      for_ (Array.mapWithIndex Tuple (Vector.toUnfoldable stepCommits.wComm :: Array _)) \(Tuple i pt) -> do
        Trace.field ("wrap.dbg.step_proof.w_comm." <> show i <> ".x") pt.x
        Trace.field ("wrap.dbg.step_proof.w_comm." <> show i <> ".y") pt.y

    wrapResult <- liftEffect $
      wrapSolveAndProve @1 @(Slots1 1)
        (\e -> Exc.throwException e)
        wrapProveCtx
        wrapCR

    -- Self-verify wrap_b0 proof against its own VK. If the proof doesn't
    -- verify here, neither the next step circuit nor the batch verifier
    -- will accept it. Mirrors step proof self-verify at line ~420.
    let
      wrapProofValid = ProofFFI.verifyOpeningProof
        wrapCR.verifierIndex
        { proof: wrapResult.proof, publicInput: wrapResult.publicInputs }
    liftEffect $ Trace.int "wrap.proof.self_verify" (if wrapProofValid then 1 else 0)
    when (not wrapProofValid)
      $ liftEffect
      $ Exc.throw "PS wrap proof FAILED kimchi batch_verify — wrap prover bug"

    liftEffect do
      Trace.int "wrap.proof.public_input_count" (Array.length wrapResult.publicInputs)
      -- Wrap proof opening values
      let wSg = ProofFFI.vestaProofOpeningSg wrapResult.proof
      Trace.field "wrap.proof.opening.sg.x" wSg.x
      Trace.field "wrap.proof.opening.sg.y" wSg.y
      let wDelta = ProofFFI.vestaProofOpeningDelta wrapResult.proof
      Trace.field "wrap.proof.opening.delta.x" wDelta.x
      Trace.field "wrap.proof.opening.delta.y" wDelta.y
      Trace.field "wrap.proof.opening.z1" (ProofFFI.vestaProofOpeningZ1 wrapResult.proof)
      Trace.field "wrap.proof.opening.z2" (ProofFFI.vestaProofOpeningZ2 wrapResult.proof)
      -- Wrap proof commitments
      let wComms = ProofFFI.vestaProofCommitments wrapResult.proof
      forWithIndex_ wComms.wComm \fi pt -> do
        let i = getFinite fi
        Trace.field ("wrap.proof.w_comm." <> show i <> ".x") pt.x
        Trace.field ("wrap.proof.w_comm." <> show i <> ".y") pt.y
      Trace.field "wrap.proof.z_comm.x" wComms.zComm.x
      Trace.field "wrap.proof.z_comm.y" wComms.zComm.y

    liftEffect $ Trace.string "simple_chain.end" "base_case_verified"

    -- =====================================================================
    -- INDUCTIVE CASE (b1): step proof with self=1, prev=0, verifying
    -- the real wrap proof b0 just produced above.
    -- =====================================================================

    let
      -- The b0 step proof's opening sg (Vesta point, WrapField coords).
      -- For b1, this is the wrap statement's
      -- `challenge_polynomial_commitment` (since must_verify=true).
      b0StepSg :: AffinePoint WrapField
      b0StepSg = ProofFFI.pallasProofOpeningSg result.proof

      -- wrapSg for b1: from b0 wrap statement's
      -- messages_for_next_step_proof.challenge_polynomial_commitments.
      -- For base case (must_verify=false), the step circuit overrode sg
      -- to Ipa.Wrap.compute_sg(new_bp_chals) = b0ChalPolyComm (NOT
      -- Dummy.Ipa.Wrap.sg — compute_sg over the base case's new bp_chals
      -- gives a fresh point).
      b1WrapSg :: AffinePoint StepField
      b1WrapSg = b0ChalPolyComm

      -- wrapPrevEvals for b1 = b0 step proof's polynomial evaluations.
      b1WrapPrevEvals :: AllEvals StepField
      b1WrapPrevEvals =
        { ftEval1: stepOracles.ftEval1
        , publicEvals:
            { zeta: stepOracles.publicEvalZeta
            , omegaTimesZeta: stepOracles.publicEvalZetaOmega
            }
        , zEvals: ProofFFI.proofZEvals result.proof
        , witnessEvals: ProofFFI.proofWitnessEvals result.proof
        , coeffEvals: ProofFFI.proofCoefficientEvals result.proof
        , sigmaEvals: ProofFFI.proofSigmaEvals result.proof
        , indexEvals: ProofFFI.proofIndexEvals result.proof
        }

      -- prevChalPolys for b1's oracles: padded accumulator.
      -- Slot 0 (padding): dummy
      -- Slot 1 (real): sg from b0 wrap statement's
      --   messages_for_next_step_proof.challenge_polynomial_commitments
      --   = Dummy.Ipa.Wrap.sg (for base case), paired with expanded
      --   old_bulletproof_challenges from b0 wrap statement.
      b1PrevChalPolys =
        let
          -- Real slot: sg = b0's expandProof-computed challenge_polynomial_commitment
          -- (= Ipa.Wrap.compute_sg(new_bp_chals)), NOT Dummy.Ipa.Wrap.sg.
          -- challenges = expand(step.unf[0].deferred.bp_chals, Pallas.endo_scalar)
          realEntry =
            { sg: b0ChalPolyComm
            , challenges: msgForNextWrapRealChals
            }
          dummyEntry = baseCaseDummyChalPoly
        in
          dummyEntry :< realEntry :< Vector.nil

      -- wrapOwnPaddedBpChals feeds hash_messages_for_next_wrap_proof per
      -- OCaml step.ml:330-336: the hash uses old_bulletproof_challenges =
      -- `prev_challenges` (step.ml:241-243) = `Vector.map
      -- Ipa.Wrap.compute_challenges statement.proof_state.messages_for_next_wrap_proof
      -- .old_bulletproof_challenges` where statement = wrap_b0.statement.
      -- wrap.ml:463-465 set that field to `Vector.map
      -- prev_statement.proof_state.unfinalized_proofs
      -- ~f:(fun t -> t.deferred_values.bulletproof_challenges)` where
      -- prev_statement = step_b0.statement for the base case. Then
      -- hash_messages_for_next_wrap_proof at wrap_hack.ml:46-59 calls
      -- pad_challenges (Vector.extend_front_exn to PaddedLength=2 with
      -- Dummy.Ipa.Wrap.challenges_computed as dummy).
      --
      -- So the padded Vector for Simple_chain N1 b1 is:
      --   [Dummy.Ipa.Wrap.challenges_computed        -- padding slot
      --   , step_b0.unfinalized[0].bp_chals expanded -- real slot
      --   ]
      -- where expanded = Ipa.Wrap.compute_challenges = expansion via
      -- Pallas.endo_scalar. PS already computes this as msgForNextWrapRealChals
      -- at line 582-589 (Vector WrapIPARounds WrapField).
      b1WrapOwnPaddedBpChals :: Vector PaddedLength (Vector WrapIPARounds WrapField)
      b1WrapOwnPaddedBpChals =
        Dummy.dummyIpaChallenges.wrapExpanded
          :< msgForNextWrapRealChals
          :< Vector.nil

    { advice: b1Advice, challengePolynomialCommitment: b1ChalPolyComm } <- liftEffect $ buildStepAdviceWithOracles
      { publicInput: F one
      , prevPublicInput: F zero
      , mostRecentWidth: 1
      , wrapDomainLog2
      , wrapVK: wrapCR.verifierIndex
      , wrapSg: b1WrapSg
      , stepSg: b0StepSg
      , wrapProof: wrapResult.proof
      , wrapPublicInput: wrapResult.publicInputs
      , prevChalPolys: b1PrevChalPolys

      , wrapPlonkRaw:
          { alpha: SizedF.unwrapF wrapDv.plonk.alpha
          , beta: SizedF.unwrapF wrapDv.plonk.beta
          , gamma: SizedF.unwrapF wrapDv.plonk.gamma
          , zeta: SizedF.unwrapF wrapDv.plonk.zeta
          }
      , wrapPrevEvals: b1WrapPrevEvals
      , wrapBranchData: wrapDv.branchData
      , wrapSpongeDigest: wrapDv.spongeDigestBeforeEvaluations
      , mustVerify: true
      , wrapOwnPaddedBpChals: b1WrapOwnPaddedBpChals
      -- b1 stepAdvicePrevEvals: the step FOP recomputes wrap_b0's deferred
      -- values from these evals and asserts they match fopState. For
      -- byte-correctness we need wrap_b0.prev_evals = step_b0.openings.evals
      -- + step_b0's x_hat (per wrap.ml:583-591). b1WrapPrevEvals is exactly
      -- this.
      , stepAdvicePrevEvals: b1WrapPrevEvals
      -- b1 fopState: from the freshly-computed wrapDv (= what wrap_b0's
      -- statement stores in its deferred_values). This MUST match what
      -- wrap_b0.publicInputs contains so the step circuit's packStatement
      -- reconstructs the same public input → same xhat → IVP beta matches.
      , fopState:
          { deferredValues:
              { plonk: wrapDv.plonk
              , combinedInnerProduct: wrapDv.combinedInnerProduct
              , xi: wrapDv.xi
              , bulletproofChallenges:
                  -- wrapDv.bulletproofPrechallenges has 16 StepIPARounds; UnfinalizedProof
                  -- StepIPARounds wants the same. Raw 128-bit SizedF values.
                  wrapDv.bulletproofPrechallenges
              , b: wrapDv.b
              }
          , shouldFinalize: false
          , spongeDigestBeforeEvaluations: F wrapDv.spongeDigestBeforeEvaluations
          }
      -- b1: kimchi prev_challenges.challenges per OCaml step.ml:913-920 +
      -- reduced_messages_for_next_proof_over_same_field.ml:41:
      -- expand `wrap_b0.statement.proof_state.deferred_values.bulletproof_challenges`
      -- via `Ipa.Step.compute_challenges` (= step endo_scalar, Vesta.ScalarField).
      -- In PS `wrapDv.bulletproofPrechallenges :: Vector StepIPARounds
      -- (SizedF 128 (F StepField))` are the raw values; expand via
      -- `toFieldPure` with step endo.
      , kimchiPrevChallengesExpanded:
          map
            (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
            wrapDv.bulletproofPrechallenges
      -- b1 prevChallengesForStepHash: per OCaml step.ml:519-525 this comes
      -- from wrap_b0.statement.messages_for_next_step_proof.old_bulletproof_challenges,
      -- which wrap_b0 forwarded from step_b0's output. step_b0's output
      -- old_bp_chals = extracted from step_b0's prev (= dummy wrap) =
      -- dummy wrap's deferred.bp_chals = Dummy.Ipa.Step.challenges. Expanded
      -- via Ipa.Step.compute_challenges = `dummyIpaChallenges.stepExpanded`.
      , prevChallengesForStepHash: Dummy.dummyIpaChallenges.stepExpanded
      }

    b1Result <- liftEffect $
      stepSolveAndProve @1 @34 @(F StepField) @(FVar StepField) @Unit @Unit @(F StepField) @(FVar StepField)
        (\e -> Exc.throw ("b1 stepSolveAndProve: " <> show e))
        ctx
        (simpleChainRule (F zero))
        stepCR
        b1Advice

    let
      b1StepProofValid = ProofFFI.verifyOpeningProof
        stepCR.verifierIndex
        { proof: b1Result.proof, publicInput: b1Result.publicInputs }
    liftEffect $ Trace.int "b1.step.proof.self_verify" (if b1StepProofValid then 1 else 0)
    when (not b1StepProofValid)
      $ liftEffect
      $ Exc.throw "b1 step proof FAILED self-verify"

    -- =====================================================================
    -- WRAP b1: wrap step_b1 (the inductive-case step proof above). Mirror
    -- of wrap_b0 orchestration at line 469-849 with b0 → b1 substitutions.
    -- AUDIT fields (prevStepAccs / prevOldBpChals / prevEvals /
    -- prevWrapDomainIndices) start as b0 dummies to isolate the first
    -- divergence; iterate from there with direct OCaml citations.
    -- =====================================================================
    let
      b1WrapProofSg :: AffinePoint WrapField
      b1WrapProofSg = ProofFFI.pallasProofOpeningSg b1Result.proof

      -- step_b1's kimchi prev_challenges[0] = (b0StepSg, expanded wrap_b0
      -- bp_chals) — matches what buildStepAdviceWithOracles populated via
      -- `input.stepSg` + `input.kimchiPrevChallengesExpanded` (Step.purs:1474).
      b1StepKimchiPrevChalsExpanded =
        map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
          wrapDv.bulletproofPrechallenges

      b1StepOracles :: OraclesResult StepField
      b1StepOracles = ProofFFI.pallasProofOracles stepCR.verifierIndex
        { proof: b1Result.proof
        , publicInput: b1Result.publicInputs
        , prevChallenges:
            [ { sgX: b0StepSg.x
              , sgY: b0StepSg.y
              , challenges: Vector.toUnfoldable b1StepKimchiPrevChalsExpanded
              }
            ]
        }

      b1StepAllEvals :: AllEvals StepField
      b1StepAllEvals =
        { ftEval1: b1StepOracles.ftEval1
        , publicEvals:
            { zeta: b1StepOracles.publicEvalZeta
            , omegaTimesZeta: b1StepOracles.publicEvalZetaOmega
            }
        , zEvals: ProofFFI.proofZEvals b1Result.proof
        , witnessEvals: ProofFFI.proofWitnessEvals b1Result.proof
        , coeffEvals: ProofFFI.proofCoefficientEvals b1Result.proof
        , sigmaEvals: ProofFFI.proofSigmaEvals b1Result.proof
        , indexEvals: ProofFFI.proofIndexEvals b1Result.proof
        }

      b1WrapDvInput :: WrapDeferredValuesInput 1
      b1WrapDvInput =
        { proof: b1Result.proof
        , verifierIndex: stepCR.verifierIndex
        , publicInput: b1Result.publicInputs
        , allEvals: b1StepAllEvals
        , pEval0Chunks: [ b1StepOracles.publicEvalZeta ]
        , domainLog2: stepDomainLog2
        , zkRows: 3
        , srsLengthLog2: 16
        , generator: (domainGenerator stepDomainLog2 :: StepField)
        , shifts: (domainShifts stepDomainLog2 :: Vector 7 StepField)
        , vanishesOnZk: ProofFFI.permutationVanishingPolynomial
            { domainLog2: stepDomainLog2, zkRows: 3, pt: b1StepOracles.zeta }
        , omegaForLagrange: \_ -> one
        , endo: stepEndoScalar
        , linearizationPoly: Linearization.pallas
        , prevSgs: b0StepSg :< Vector.nil
        , prevChallenges: b1StepKimchiPrevChalsExpanded :< Vector.nil
        , proofsVerifiedMask: false :< true :< Vector.nil
        }

      b1WrapDv = wrapComputeDeferredValues b1WrapDvInput

      b1MsgForNextStepDigest :: StepField
      b1MsgForNextStepDigest = unsafePartial $ fromJust $
        Array.index b1Result.publicInputs 32

      PerProofUnfinalized b1StepUnfRec0 =
        Vector.head b1Advice.publicUnfinalizedProofs

      b1MsgForNextWrapRealChals :: Vector WrapIPARounds WrapField
      b1MsgForNextWrapRealChals =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF.SizedF 128 WrapField)
                msgForNextWrapWrapEndo
          )
          b1StepUnfRec0.bulletproofChallenges

      b1MsgForNextWrapDigest :: WrapField
      b1MsgForNextWrapDigest =
        hashMessagesForNextWrapProof
          { sg: b1WrapProofSg
          , expandedChallenges: b1MsgForNextWrapRealChals
          , dummyChallenges: msgForNextWrapDummyChals
          }

      b1WrapPublicInput = assembleWrapMainInput
        { deferredValues: b1WrapDv
        , messagesForNextStepProofDigest: b1MsgForNextStepDigest
        , messagesForNextWrapProofDigest: b1MsgForNextWrapDigest
        }

      b1StepPerProof
        :: PerProofUnfinalized WrapIPARounds (Type2 (F WrapField))
             (F WrapField)
             Boolean
      b1StepPerProof = PerProofUnfinalized
        { combinedInnerProduct: toShifted (fromShifted b1StepUnfRec0.combinedInnerProduct :: F WrapField)
        , b: toShifted (fromShifted b1StepUnfRec0.b :: F WrapField)
        , zetaToSrsLength: toShifted (fromShifted b1StepUnfRec0.zetaToSrsLength :: F WrapField)
        , zetaToDomainSize: toShifted (fromShifted b1StepUnfRec0.zetaToDomainSize :: F WrapField)
        , perm: toShifted (fromShifted b1StepUnfRec0.perm :: F WrapField)
        , spongeDigest: F (fromBigInt (toBigInt (case b1StepUnfRec0.spongeDigest of F x -> x)) :: WrapField)
        , beta: UnChecked (coerceViaBits (case b1StepUnfRec0.beta of UnChecked v -> v))
        , gamma: UnChecked (coerceViaBits (case b1StepUnfRec0.gamma of UnChecked v -> v))
        , alpha: UnChecked (coerceViaBits (case b1StepUnfRec0.alpha of UnChecked v -> v))
        , zeta: UnChecked (coerceViaBits (case b1StepUnfRec0.zeta of UnChecked v -> v))
        , xi: UnChecked (coerceViaBits (case b1StepUnfRec0.xi of UnChecked v -> v))
        , bulletproofChallenges:
            map (\(UnChecked v) -> UnChecked (coerceViaBits v)) b1StepUnfRec0.bulletproofChallenges
        , shouldFinalize: b1StepUnfRec0.shouldFinalize
        }

      -- Oracles on wrap_b0 (prev wrap proof step_b1 verified). Needed
      -- for x_hat in b1 prev_evals per step.ml:402 + :1023-1036. Uses
      -- wrap_b0's own kimchi prev_challenges (what was passed to create
      -- wrap_b0's ProverProof).
      b1WrapB0Oracles :: OraclesResult WrapField
      b1WrapB0Oracles = ProofFFI.vestaProofOracles wrapCR.verifierIndex
        { proof: wrapResult.proof
        , publicInput: wrapResult.publicInputs
        , prevChallenges:
            [ { sgX: wrapSg.x
              , sgY: wrapSg.y
              , challenges:
                  Vector.toUnfoldable
                    ( map (fromBigInt <<< toBigInt)
                        Dummy.dummyIpaChallenges.wrapExpanded
                        :: Vector WrapIPARounds WrapField
                    )
              }
            , { sgX: b0ChalPolyComm.x
              , sgY: b0ChalPolyComm.y
              , challenges: Vector.toUnfoldable msgForNextWrapRealChals
              }
            ]
        }

      -- prev_evals[0] for wrap_b1 = wrap_b0's evals + x_hat from oracle
      -- (per step.ml:1023-1036 applied to step_b1 verifying wrap_b0).
      b1WrapPrevEvalsForAdvice :: StepAllEvals (F WrapField)
      b1WrapPrevEvalsForAdvice =
        let
          peWF pe' = PointEval
            { zeta: F pe'.zeta
            , omegaTimesZeta: F pe'.omegaTimesZeta
            }
        in
          StepAllEvals
            { ftEval1: F b1WrapB0Oracles.ftEval1
            , publicEvals: PointEval
                { zeta: F b1WrapB0Oracles.publicEvalZeta
                , omegaTimesZeta: F b1WrapB0Oracles.publicEvalZetaOmega
                }
            , zEvals: peWF (ProofFFI.proofZEvals wrapResult.proof)
            , witnessEvals: map peWF (ProofFFI.proofWitnessEvals wrapResult.proof)
            , coeffEvals: map peWF (ProofFFI.proofCoefficientEvals wrapResult.proof)
            , sigmaEvals: map peWF (ProofFFI.proofSigmaEvals wrapResult.proof)
            , indexEvals: map peWF (ProofFFI.proofIndexEvals wrapResult.proof)
            }

      b1WrapAdviceInput :: BuildWrapAdviceInput 1 (Slots1 1)
      b1WrapAdviceInput =
        { stepProof: b1Result.proof
        , whichBranch: F zero
        , prevUnfinalizedProofs: b1StepPerProof :< Vector.nil
        , prevMessagesForNextStepProofHash:
            F (fromBigInt (toBigInt b1MsgForNextStepDigest) :: WrapField)
        -- prevStepAccs[0] for b1: step_b1.messages_for_next_wrap_proof[0]
        -- .challenge_polynomial_commitment. Per step.ml:997-1008 this maps
        -- from prev proofs to `t.statement.proof_state.messages_for_next_wrap_proof`.
        -- For step_b1, t = wrap_b0; wrap.ml:461-462 writes its own
        -- messages_for_next_wrap_proof.cpc = step_b0.opening.sg. So
        -- wrap_b1's Req.Step_accs[0] = step_b0.opening.sg = b0StepSg.
        , prevStepAccs: WeierstrassAffinePoint { x: F b0StepSg.x, y: F b0StepSg.y } :< Vector.nil
        -- prevOldBpChals for b1: per wrap.ml:463-466 + step.ml:997-1008,
        -- step_b1.messages_for_next_wrap_proof[0].old_bp_chals =
        -- wrap_b0.messages_for_next_wrap_proof[0].old_bp_chals =
        -- step_b0.unfinalized[0].bulletproof_challenges (= msgForNextWrapRealChals,
        -- the SAME value wrap_b0's kimchi prev_challenges absorbed).
        -- NOT b1MsgForNextWrapRealChals (= step_b1's unfinalized bp chals).
        , prevOldBpChals: slots1 ((map F msgForNextWrapRealChals) :< Vector.nil)
        -- prevEvals: fixed to use wrap_b0's real evals + x_hat per
        -- step.ml:1023-1036 (first focused audit fix for wrap_b1).
        , prevEvals: b1WrapPrevEvalsForAdvice :< Vector.nil
        , prevWrapDomainIndices: F (fromInt 1 :: WrapField) :< Vector.nil
        }

      b1WrapAdvice :: WrapAdvice 1 (Slots1 1)
      b1WrapAdvice = buildWrapAdvice b1WrapAdviceInput

      b1WrapProveCtx =
        { wrapMainConfig: wrapCtx.wrapMainConfig
        , crs: pallasProofCrs
        , publicInput: b1WrapPublicInput
        , advice: b1WrapAdvice
        , kimchiPrevChallenges:
            let
              padEntry =
                { sgX: wrapSg.x
                , sgY: wrapSg.y
                , challenges: map (fromBigInt <<< toBigInt)
                    Dummy.dummyIpaChallenges.wrapExpanded
                }
              realEntry =
                { sgX: b1ChalPolyComm.x
                , sgY: b1ChalPolyComm.y
                , challenges: b1MsgForNextWrapRealChals
                }
            in
              padEntry :< realEntry :< Vector.nil
        }

    -- DIAG: compare what FOP will compare.
    liftEffect do
      let
        cipClaim :: WrapField
        cipClaim = case fromShifted b1StepUnfRec0.combinedInnerProduct :: F WrapField of F x -> x

        bClaim :: WrapField
        bClaim = case fromShifted b1StepUnfRec0.b :: F WrapField of F x -> x

        permClaim :: WrapField
        permClaim = case fromShifted b1StepUnfRec0.perm :: F WrapField of F x -> x

        spongeDigestClaim :: WrapField
        spongeDigestClaim = case b1StepUnfRec0.spongeDigest of F v -> Curves.fromBigInt (Curves.toBigInt v)
      Trace.field "b1wrap.dbg.cip_claim" cipClaim
      Trace.field "b1wrap.dbg.cip_oracle" b1WrapB0Oracles.combinedInnerProduct
      Trace.field "b1wrap.dbg.b_claim" bClaim
      Trace.field "b1wrap.dbg.perm_claim" permClaim
      Trace.field "b1wrap.dbg.spongeDigest_claim" spongeDigestClaim
      Trace.field "b1wrap.dbg.spongeDigest_oracle" b1WrapB0Oracles.fqDigest
      Trace.field "b1wrap.dbg.ftEval1_oracle" b1WrapB0Oracles.ftEval1
      Trace.field "b1wrap.dbg.v_oracle" b1WrapB0Oracles.v
      Trace.field "b1wrap.dbg.u_oracle" b1WrapB0Oracles.u
      Trace.field "b1wrap.dbg.v_chal_oracle" (SizedF.toField b1WrapB0Oracles.vChal)
      Trace.field "b1wrap.dbg.u_chal_oracle" (SizedF.toField b1WrapB0Oracles.uChal)
      Trace.field "b1wrap.dbg.zeta_oracle" b1WrapB0Oracles.zeta

    b1WrapResult <- liftEffect $
      wrapSolveAndProve @1 @(Slots1 1)
        (\e -> Exc.throwException e)
        b1WrapProveCtx
        wrapCR

    let
      b1WrapProofValid = ProofFFI.verifyOpeningProof
        wrapCR.verifierIndex
        { proof: b1WrapResult.proof, publicInput: b1WrapResult.publicInputs }
    liftEffect $ Trace.int "b1.wrap.proof.self_verify" (if b1WrapProofValid then 1 else 0)
    when (not b1WrapProofValid)
      $ liftEffect
      $ Exc.throw "b1 wrap proof FAILED self-verify"

    -- =====================================================================
    -- Continuation b2: step_b2 (self=2, prev=1, verifying wrap_b1) +
    -- wrap_b2 (wrapping step_b2). Same N=1 Simple_chain circuit — just
    -- one more iteration. No OCaml fixture comparison (no counter 4/5
    -- fixture); each proof only self-verifies via verifyOpeningProof.
    -- Structurally mirrors the b1 step+wrap blocks with every reference
    -- to wrap_b0 / step_b0 replaced by wrap_b1 / step_b1.
    -- =====================================================================
    let
      b1StepOpeningSg :: AffinePoint WrapField
      b1StepOpeningSg = ProofFFI.pallasProofOpeningSg b1Result.proof

      -- wrap_b1's prev_evals field (per wrap.ml:591 applied to wrap_b1
      -- wrapping step_b1) = step_b1's openings.evals + step_b1 x_hat +
      -- step_b1 ft_eval1. This is what step_b2's Per_proof_witness
      -- reads when verifying wrap_b1.
      b2WrapPrevEvals :: AllEvals StepField
      b2WrapPrevEvals =
        { ftEval1: b1StepOracles.ftEval1
        , publicEvals:
            { zeta: b1StepOracles.publicEvalZeta
            , omegaTimesZeta: b1StepOracles.publicEvalZetaOmega
            }
        , zEvals: ProofFFI.proofZEvals b1Result.proof
        , witnessEvals: ProofFFI.proofWitnessEvals b1Result.proof
        , coeffEvals: ProofFFI.proofCoefficientEvals b1Result.proof
        , sigmaEvals: ProofFFI.proofSigmaEvals b1Result.proof
        , indexEvals: ProofFFI.proofIndexEvals b1Result.proof
        }

      -- prevChalPolys for step_b2's oracles on wrap_b1.
      b2PrevChalPolys =
        let
          realEntry =
            { sg: b1ChalPolyComm
            , challenges: b1MsgForNextWrapRealChals
            }
          dummyEntry = baseCaseDummyChalPoly
        in
          dummyEntry :< realEntry :< Vector.nil

      b2WrapOwnPaddedBpChals :: Vector PaddedLength (Vector WrapIPARounds WrapField)
      b2WrapOwnPaddedBpChals =
        Dummy.dummyIpaChallenges.wrapExpanded
          :< b1MsgForNextWrapRealChals
          :< Vector.nil

    { advice: b2Advice, challengePolynomialCommitment: b2ChalPolyComm } <- liftEffect $ buildStepAdviceWithOracles
      { publicInput: F (fromInt 2 :: StepField)
      , prevPublicInput: F one
      , mostRecentWidth: 1
      , wrapDomainLog2
      , wrapVK: wrapCR.verifierIndex
      , wrapSg: b1ChalPolyComm
      , stepSg: b1StepOpeningSg
      , wrapProof: b1WrapResult.proof
      , wrapPublicInput: b1WrapResult.publicInputs
      , prevChalPolys: b2PrevChalPolys
      , wrapPlonkRaw:
          { alpha: SizedF.unwrapF b1WrapDv.plonk.alpha
          , beta: SizedF.unwrapF b1WrapDv.plonk.beta
          , gamma: SizedF.unwrapF b1WrapDv.plonk.gamma
          , zeta: SizedF.unwrapF b1WrapDv.plonk.zeta
          }
      , wrapPrevEvals: b2WrapPrevEvals
      , wrapBranchData: b1WrapDv.branchData
      , wrapSpongeDigest: b1WrapDv.spongeDigestBeforeEvaluations
      , mustVerify: true
      , wrapOwnPaddedBpChals: b2WrapOwnPaddedBpChals
      , stepAdvicePrevEvals: b2WrapPrevEvals
      , fopState:
          { deferredValues:
              { plonk: b1WrapDv.plonk
              , combinedInnerProduct: b1WrapDv.combinedInnerProduct
              , xi: b1WrapDv.xi
              , bulletproofChallenges: b1WrapDv.bulletproofPrechallenges
              , b: b1WrapDv.b
              }
          , shouldFinalize: false
          , spongeDigestBeforeEvaluations: F b1WrapDv.spongeDigestBeforeEvaluations
          }
      , kimchiPrevChallengesExpanded:
          map
            (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
            b1WrapDv.bulletproofPrechallenges
      -- b2 prevChallengesForStepHash: per OCaml step.ml:519-525 + step.ml:790-801,
      -- this comes via wrap_b1.messages_for_next_step_proof.old_bp_chals =
      -- step_b1.output.old_bp_chals (forwarded) = step_b1 extracted from its
      -- prev (= wrap_b0) via `t.statement.proof_state.deferred_values.
      -- bulletproof_challenges` = wrap_b0.deferred.bp_chals = wrapDv (from b0
      -- stage). Expanded via step endo scalar to StepField.
      , prevChallengesForStepHash:
          map
            (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
            wrapDv.bulletproofPrechallenges
      }

    b2Result <- liftEffect $
      stepSolveAndProve @1 @34 @(F StepField) @(FVar StepField) @Unit @Unit @(F StepField) @(FVar StepField)
        (\e -> Exc.throw ("b2 stepSolveAndProve: " <> show e))
        ctx
        (simpleChainRule (F one))
        stepCR
        b2Advice

    let
      b2StepProofValid = ProofFFI.verifyOpeningProof
        stepCR.verifierIndex
        { proof: b2Result.proof, publicInput: b2Result.publicInputs }
    liftEffect $ Trace.int "b2.step.proof.self_verify" (if b2StepProofValid then 1 else 0)
    when (not b2StepProofValid)
      $ liftEffect
      $ Exc.throw "b2 step proof FAILED self-verify"

    -- Now wrap_b2 (wrapping step_b2).
    let
      b2WrapProofSg :: AffinePoint WrapField
      b2WrapProofSg = ProofFFI.pallasProofOpeningSg b2Result.proof

      b2StepKimchiPrevChalsExpanded =
        map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
          b1WrapDv.bulletproofPrechallenges

      b2StepOracles :: OraclesResult StepField
      b2StepOracles = ProofFFI.pallasProofOracles stepCR.verifierIndex
        { proof: b2Result.proof
        , publicInput: b2Result.publicInputs
        , prevChallenges:
            [ { sgX: b1StepOpeningSg.x
              , sgY: b1StepOpeningSg.y
              , challenges: Vector.toUnfoldable b2StepKimchiPrevChalsExpanded
              }
            ]
        }

      b2StepAllEvals :: AllEvals StepField
      b2StepAllEvals =
        { ftEval1: b2StepOracles.ftEval1
        , publicEvals:
            { zeta: b2StepOracles.publicEvalZeta
            , omegaTimesZeta: b2StepOracles.publicEvalZetaOmega
            }
        , zEvals: ProofFFI.proofZEvals b2Result.proof
        , witnessEvals: ProofFFI.proofWitnessEvals b2Result.proof
        , coeffEvals: ProofFFI.proofCoefficientEvals b2Result.proof
        , sigmaEvals: ProofFFI.proofSigmaEvals b2Result.proof
        , indexEvals: ProofFFI.proofIndexEvals b2Result.proof
        }

      b2WrapDvInput :: WrapDeferredValuesInput 1
      b2WrapDvInput =
        { proof: b2Result.proof
        , verifierIndex: stepCR.verifierIndex
        , publicInput: b2Result.publicInputs
        , allEvals: b2StepAllEvals
        , pEval0Chunks: [ b2StepOracles.publicEvalZeta ]
        , domainLog2: stepDomainLog2
        , zkRows: 3
        , srsLengthLog2: 16
        , generator: (domainGenerator stepDomainLog2 :: StepField)
        , shifts: (domainShifts stepDomainLog2 :: Vector 7 StepField)
        , vanishesOnZk: ProofFFI.permutationVanishingPolynomial
            { domainLog2: stepDomainLog2, zkRows: 3, pt: b2StepOracles.zeta }
        , omegaForLagrange: \_ -> one
        , endo: stepEndoScalar
        , linearizationPoly: Linearization.pallas
        , prevSgs: b1StepOpeningSg :< Vector.nil
        , prevChallenges: b2StepKimchiPrevChalsExpanded :< Vector.nil
        , proofsVerifiedMask: false :< true :< Vector.nil
        }

      b2WrapDv = wrapComputeDeferredValues b2WrapDvInput

      b2MsgForNextStepDigest :: StepField
      b2MsgForNextStepDigest = unsafePartial $ fromJust $
        Array.index b2Result.publicInputs 32

      PerProofUnfinalized b2StepUnfRec0 =
        Vector.head b2Advice.publicUnfinalizedProofs

      b2MsgForNextWrapRealChals :: Vector WrapIPARounds WrapField
      b2MsgForNextWrapRealChals =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF.SizedF 128 WrapField)
                msgForNextWrapWrapEndo
          )
          b2StepUnfRec0.bulletproofChallenges

      b2MsgForNextWrapDigest :: WrapField
      b2MsgForNextWrapDigest =
        hashMessagesForNextWrapProof
          { sg: b2WrapProofSg
          , expandedChallenges: b2MsgForNextWrapRealChals
          , dummyChallenges: msgForNextWrapDummyChals
          }

      b2WrapPublicInput = assembleWrapMainInput
        { deferredValues: b2WrapDv
        , messagesForNextStepProofDigest: b2MsgForNextStepDigest
        , messagesForNextWrapProofDigest: b2MsgForNextWrapDigest
        }

      b2StepPerProof
        :: PerProofUnfinalized WrapIPARounds (Type2 (F WrapField))
             (F WrapField)
             Boolean
      b2StepPerProof = PerProofUnfinalized
        { combinedInnerProduct: toShifted (fromShifted b2StepUnfRec0.combinedInnerProduct :: F WrapField)
        , b: toShifted (fromShifted b2StepUnfRec0.b :: F WrapField)
        , zetaToSrsLength: toShifted (fromShifted b2StepUnfRec0.zetaToSrsLength :: F WrapField)
        , zetaToDomainSize: toShifted (fromShifted b2StepUnfRec0.zetaToDomainSize :: F WrapField)
        , perm: toShifted (fromShifted b2StepUnfRec0.perm :: F WrapField)
        , spongeDigest: F (fromBigInt (toBigInt (case b2StepUnfRec0.spongeDigest of F x -> x)) :: WrapField)
        , beta: UnChecked (coerceViaBits (case b2StepUnfRec0.beta of UnChecked v -> v))
        , gamma: UnChecked (coerceViaBits (case b2StepUnfRec0.gamma of UnChecked v -> v))
        , alpha: UnChecked (coerceViaBits (case b2StepUnfRec0.alpha of UnChecked v -> v))
        , zeta: UnChecked (coerceViaBits (case b2StepUnfRec0.zeta of UnChecked v -> v))
        , xi: UnChecked (coerceViaBits (case b2StepUnfRec0.xi of UnChecked v -> v))
        , bulletproofChallenges:
            map (\(UnChecked v) -> UnChecked (coerceViaBits v)) b2StepUnfRec0.bulletproofChallenges
        , shouldFinalize: b2StepUnfRec0.shouldFinalize
        }

      -- Oracles on wrap_b1 (for wrap_b2's prev_evals x_hat). Must use
      -- wrap_b1's OWN kimchi prev_challenges (what was passed to
      -- wrapSolveAndProve for b1 creation).
      b2WrapB1Oracles :: OraclesResult WrapField
      b2WrapB1Oracles = ProofFFI.vestaProofOracles wrapCR.verifierIndex
        { proof: b1WrapResult.proof
        , publicInput: b1WrapResult.publicInputs
        , prevChallenges:
            [ { sgX: wrapSg.x
              , sgY: wrapSg.y
              , challenges:
                  Vector.toUnfoldable
                    ( map (fromBigInt <<< toBigInt)
                        Dummy.dummyIpaChallenges.wrapExpanded
                        :: Vector WrapIPARounds WrapField
                    )
              }
            , { sgX: b1ChalPolyComm.x
              , sgY: b1ChalPolyComm.y
              , challenges: Vector.toUnfoldable b1MsgForNextWrapRealChals
              }
            ]
        }

      b2WrapPrevEvalsForAdvice :: StepAllEvals (F WrapField)
      b2WrapPrevEvalsForAdvice =
        let
          peWF pe' = PointEval
            { zeta: F pe'.zeta
            , omegaTimesZeta: F pe'.omegaTimesZeta
            }
        in
          StepAllEvals
            { ftEval1: F b2WrapB1Oracles.ftEval1
            , publicEvals: PointEval
                { zeta: F b2WrapB1Oracles.publicEvalZeta
                , omegaTimesZeta: F b2WrapB1Oracles.publicEvalZetaOmega
                }
            , zEvals: peWF (ProofFFI.proofZEvals b1WrapResult.proof)
            , witnessEvals: map peWF (ProofFFI.proofWitnessEvals b1WrapResult.proof)
            , coeffEvals: map peWF (ProofFFI.proofCoefficientEvals b1WrapResult.proof)
            , sigmaEvals: map peWF (ProofFFI.proofSigmaEvals b1WrapResult.proof)
            , indexEvals: map peWF (ProofFFI.proofIndexEvals b1WrapResult.proof)
            }

      b2WrapAdviceInput :: BuildWrapAdviceInput 1 (Slots1 1)
      b2WrapAdviceInput =
        { stepProof: b2Result.proof
        , whichBranch: F zero
        , prevUnfinalizedProofs: b2StepPerProof :< Vector.nil
        , prevMessagesForNextStepProofHash:
            F (fromBigInt (toBigInt b2MsgForNextStepDigest) :: WrapField)
        , prevStepAccs: WeierstrassAffinePoint { x: F b1StepOpeningSg.x, y: F b1StepOpeningSg.y } :< Vector.nil
        , prevOldBpChals: slots1 ((map F b1MsgForNextWrapRealChals) :< Vector.nil)
        , prevEvals: b2WrapPrevEvalsForAdvice :< Vector.nil
        , prevWrapDomainIndices: F (fromInt 1 :: WrapField) :< Vector.nil
        }

      b2WrapAdvice :: WrapAdvice 1 (Slots1 1)
      b2WrapAdvice = buildWrapAdvice b2WrapAdviceInput

      b2WrapProveCtx =
        { wrapMainConfig: wrapCtx.wrapMainConfig
        , crs: pallasProofCrs
        , publicInput: b2WrapPublicInput
        , advice: b2WrapAdvice
        , kimchiPrevChallenges:
            let
              padEntry =
                { sgX: wrapSg.x
                , sgY: wrapSg.y
                , challenges: map (fromBigInt <<< toBigInt)
                    Dummy.dummyIpaChallenges.wrapExpanded
                }
              realEntry =
                { sgX: b2ChalPolyComm.x
                , sgY: b2ChalPolyComm.y
                , challenges: b2MsgForNextWrapRealChals
                }
            in
              padEntry :< realEntry :< Vector.nil
        }

    b2WrapResult <- liftEffect $
      wrapSolveAndProve @1 @(Slots1 1)
        (\e -> Exc.throwException e)
        b2WrapProveCtx
        wrapCR

    let
      b2WrapProofValid = ProofFFI.verifyOpeningProof
        wrapCR.verifierIndex
        { proof: b2WrapResult.proof, publicInput: b2WrapResult.publicInputs }
    liftEffect $ Trace.int "b2.wrap.proof.self_verify" (if b2WrapProofValid then 1 else 0)
    when (not b2WrapProofValid)
      $ liftEffect
      $ Exc.throw "b2 wrap proof FAILED self-verify"

    -- =====================================================================
    -- Continuation b3: step_b3 (self=3, prev=2, verifying wrap_b2) +
    -- wrap_b3 (wrapping step_b3). Same N=1 Simple_chain circuit — one
    -- more iteration. Mechanical mirror of b2 with b1→b2 substitutions
    -- (one more hop). No OCaml fixture; each proof only self-verifies.
    -- =====================================================================
    let
      b2StepOpeningSg :: AffinePoint WrapField
      b2StepOpeningSg = ProofFFI.pallasProofOpeningSg b2Result.proof

      -- wrap_b2's prev_evals field = step_b2's openings + step_b2 x_hat +
      -- step_b2 ft_eval1 (from b2StepOracles).
      b3WrapPrevEvals :: AllEvals StepField
      b3WrapPrevEvals =
        { ftEval1: b2StepOracles.ftEval1
        , publicEvals:
            { zeta: b2StepOracles.publicEvalZeta
            , omegaTimesZeta: b2StepOracles.publicEvalZetaOmega
            }
        , zEvals: ProofFFI.proofZEvals b2Result.proof
        , witnessEvals: ProofFFI.proofWitnessEvals b2Result.proof
        , coeffEvals: ProofFFI.proofCoefficientEvals b2Result.proof
        , sigmaEvals: ProofFFI.proofSigmaEvals b2Result.proof
        , indexEvals: ProofFFI.proofIndexEvals b2Result.proof
        }

      b3PrevChalPolys =
        let
          realEntry =
            { sg: b2ChalPolyComm
            , challenges: b2MsgForNextWrapRealChals
            }
          dummyEntry = baseCaseDummyChalPoly
        in
          dummyEntry :< realEntry :< Vector.nil

      b3WrapOwnPaddedBpChals :: Vector PaddedLength (Vector WrapIPARounds WrapField)
      b3WrapOwnPaddedBpChals =
        Dummy.dummyIpaChallenges.wrapExpanded
          :< b2MsgForNextWrapRealChals
          :< Vector.nil

    { advice: b3Advice, challengePolynomialCommitment: b3ChalPolyComm } <- liftEffect $ buildStepAdviceWithOracles
      { publicInput: F (fromInt 3 :: StepField)
      , prevPublicInput: F (fromInt 2 :: StepField)
      , mostRecentWidth: 1
      , wrapDomainLog2
      , wrapVK: wrapCR.verifierIndex
      , wrapSg: b2ChalPolyComm
      , stepSg: b2StepOpeningSg
      , wrapProof: b2WrapResult.proof
      , wrapPublicInput: b2WrapResult.publicInputs
      , prevChalPolys: b3PrevChalPolys
      , wrapPlonkRaw:
          { alpha: SizedF.unwrapF b2WrapDv.plonk.alpha
          , beta: SizedF.unwrapF b2WrapDv.plonk.beta
          , gamma: SizedF.unwrapF b2WrapDv.plonk.gamma
          , zeta: SizedF.unwrapF b2WrapDv.plonk.zeta
          }
      , wrapPrevEvals: b3WrapPrevEvals
      , wrapBranchData: b2WrapDv.branchData
      , wrapSpongeDigest: b2WrapDv.spongeDigestBeforeEvaluations
      , mustVerify: true
      , wrapOwnPaddedBpChals: b3WrapOwnPaddedBpChals
      , stepAdvicePrevEvals: b3WrapPrevEvals
      , fopState:
          { deferredValues:
              { plonk: b2WrapDv.plonk
              , combinedInnerProduct: b2WrapDv.combinedInnerProduct
              , xi: b2WrapDv.xi
              , bulletproofChallenges: b2WrapDv.bulletproofPrechallenges
              , b: b2WrapDv.b
              }
          , shouldFinalize: false
          , spongeDigestBeforeEvaluations: F b2WrapDv.spongeDigestBeforeEvaluations
          }
      , kimchiPrevChallengesExpanded:
          map
            (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
            b2WrapDv.bulletproofPrechallenges
      -- b3 prevChallengesForStepHash: per step.ml:519-525, forwarded from
      -- step_b2's output old_bp_chals = step_b2 extracted from its prev
      -- (= wrap_b1) = wrap_b1.deferred.bp_chals = b1WrapDv (from b1 wrap stage).
      , prevChallengesForStepHash:
          map
            (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
            b1WrapDv.bulletproofPrechallenges
      }

    b3Result <- liftEffect $
      stepSolveAndProve @1 @34 @(F StepField) @(FVar StepField) @Unit @Unit @(F StepField) @(FVar StepField)
        (\e -> Exc.throw ("b3 stepSolveAndProve: " <> show e))
        ctx
        (simpleChainRule (F (fromInt 2 :: StepField)))
        stepCR
        b3Advice

    let
      b3StepProofValid = ProofFFI.verifyOpeningProof
        stepCR.verifierIndex
        { proof: b3Result.proof, publicInput: b3Result.publicInputs }
    liftEffect $ Trace.int "b3.step.proof.self_verify" (if b3StepProofValid then 1 else 0)
    when (not b3StepProofValid)
      $ liftEffect
      $ Exc.throw "b3 step proof FAILED self-verify"

    -- wrap_b3 (wrapping step_b3).
    let
      b3WrapProofSg :: AffinePoint WrapField
      b3WrapProofSg = ProofFFI.pallasProofOpeningSg b3Result.proof

      b3StepKimchiPrevChalsExpanded =
        map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
          b2WrapDv.bulletproofPrechallenges

      b3StepOracles :: OraclesResult StepField
      b3StepOracles = ProofFFI.pallasProofOracles stepCR.verifierIndex
        { proof: b3Result.proof
        , publicInput: b3Result.publicInputs
        , prevChallenges:
            [ { sgX: b2StepOpeningSg.x
              , sgY: b2StepOpeningSg.y
              , challenges: Vector.toUnfoldable b3StepKimchiPrevChalsExpanded
              }
            ]
        }

      b3StepAllEvals :: AllEvals StepField
      b3StepAllEvals =
        { ftEval1: b3StepOracles.ftEval1
        , publicEvals:
            { zeta: b3StepOracles.publicEvalZeta
            , omegaTimesZeta: b3StepOracles.publicEvalZetaOmega
            }
        , zEvals: ProofFFI.proofZEvals b3Result.proof
        , witnessEvals: ProofFFI.proofWitnessEvals b3Result.proof
        , coeffEvals: ProofFFI.proofCoefficientEvals b3Result.proof
        , sigmaEvals: ProofFFI.proofSigmaEvals b3Result.proof
        , indexEvals: ProofFFI.proofIndexEvals b3Result.proof
        }

      b3WrapDvInput :: WrapDeferredValuesInput 1
      b3WrapDvInput =
        { proof: b3Result.proof
        , verifierIndex: stepCR.verifierIndex
        , publicInput: b3Result.publicInputs
        , allEvals: b3StepAllEvals
        , pEval0Chunks: [ b3StepOracles.publicEvalZeta ]
        , domainLog2: stepDomainLog2
        , zkRows: 3
        , srsLengthLog2: 16
        , generator: (domainGenerator stepDomainLog2 :: StepField)
        , shifts: (domainShifts stepDomainLog2 :: Vector 7 StepField)
        , vanishesOnZk: ProofFFI.permutationVanishingPolynomial
            { domainLog2: stepDomainLog2, zkRows: 3, pt: b3StepOracles.zeta }
        , omegaForLagrange: \_ -> one
        , endo: stepEndoScalar
        , linearizationPoly: Linearization.pallas
        , prevSgs: b2StepOpeningSg :< Vector.nil
        , prevChallenges: b3StepKimchiPrevChalsExpanded :< Vector.nil
        , proofsVerifiedMask: false :< true :< Vector.nil
        }

      b3WrapDv = wrapComputeDeferredValues b3WrapDvInput

      b3MsgForNextStepDigest :: StepField
      b3MsgForNextStepDigest = unsafePartial $ fromJust $
        Array.index b3Result.publicInputs 32

      PerProofUnfinalized b3StepUnfRec0 =
        Vector.head b3Advice.publicUnfinalizedProofs

      b3MsgForNextWrapRealChals :: Vector WrapIPARounds WrapField
      b3MsgForNextWrapRealChals =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF.SizedF 128 WrapField)
                msgForNextWrapWrapEndo
          )
          b3StepUnfRec0.bulletproofChallenges

      b3MsgForNextWrapDigest :: WrapField
      b3MsgForNextWrapDigest =
        hashMessagesForNextWrapProof
          { sg: b3WrapProofSg
          , expandedChallenges: b3MsgForNextWrapRealChals
          , dummyChallenges: msgForNextWrapDummyChals
          }

      b3WrapPublicInput = assembleWrapMainInput
        { deferredValues: b3WrapDv
        , messagesForNextStepProofDigest: b3MsgForNextStepDigest
        , messagesForNextWrapProofDigest: b3MsgForNextWrapDigest
        }

      b3StepPerProof
        :: PerProofUnfinalized WrapIPARounds (Type2 (F WrapField))
             (F WrapField)
             Boolean
      b3StepPerProof = PerProofUnfinalized
        { combinedInnerProduct: toShifted (fromShifted b3StepUnfRec0.combinedInnerProduct :: F WrapField)
        , b: toShifted (fromShifted b3StepUnfRec0.b :: F WrapField)
        , zetaToSrsLength: toShifted (fromShifted b3StepUnfRec0.zetaToSrsLength :: F WrapField)
        , zetaToDomainSize: toShifted (fromShifted b3StepUnfRec0.zetaToDomainSize :: F WrapField)
        , perm: toShifted (fromShifted b3StepUnfRec0.perm :: F WrapField)
        , spongeDigest: F (fromBigInt (toBigInt (case b3StepUnfRec0.spongeDigest of F x -> x)) :: WrapField)
        , beta: UnChecked (coerceViaBits (case b3StepUnfRec0.beta of UnChecked v -> v))
        , gamma: UnChecked (coerceViaBits (case b3StepUnfRec0.gamma of UnChecked v -> v))
        , alpha: UnChecked (coerceViaBits (case b3StepUnfRec0.alpha of UnChecked v -> v))
        , zeta: UnChecked (coerceViaBits (case b3StepUnfRec0.zeta of UnChecked v -> v))
        , xi: UnChecked (coerceViaBits (case b3StepUnfRec0.xi of UnChecked v -> v))
        , bulletproofChallenges:
            map (\(UnChecked v) -> UnChecked (coerceViaBits v)) b3StepUnfRec0.bulletproofChallenges
        , shouldFinalize: b3StepUnfRec0.shouldFinalize
        }

      b3WrapB2Oracles :: OraclesResult WrapField
      b3WrapB2Oracles = ProofFFI.vestaProofOracles wrapCR.verifierIndex
        { proof: b2WrapResult.proof
        , publicInput: b2WrapResult.publicInputs
        , prevChallenges:
            [ { sgX: wrapSg.x
              , sgY: wrapSg.y
              , challenges:
                  Vector.toUnfoldable
                    ( map (fromBigInt <<< toBigInt)
                        Dummy.dummyIpaChallenges.wrapExpanded
                        :: Vector WrapIPARounds WrapField
                    )
              }
            , { sgX: b2ChalPolyComm.x
              , sgY: b2ChalPolyComm.y
              , challenges: Vector.toUnfoldable b2MsgForNextWrapRealChals
              }
            ]
        }

      b3WrapPrevEvalsForAdvice :: StepAllEvals (F WrapField)
      b3WrapPrevEvalsForAdvice =
        let
          peWF pe' = PointEval
            { zeta: F pe'.zeta
            , omegaTimesZeta: F pe'.omegaTimesZeta
            }
        in
          StepAllEvals
            { ftEval1: F b3WrapB2Oracles.ftEval1
            , publicEvals: PointEval
                { zeta: F b3WrapB2Oracles.publicEvalZeta
                , omegaTimesZeta: F b3WrapB2Oracles.publicEvalZetaOmega
                }
            , zEvals: peWF (ProofFFI.proofZEvals b2WrapResult.proof)
            , witnessEvals: map peWF (ProofFFI.proofWitnessEvals b2WrapResult.proof)
            , coeffEvals: map peWF (ProofFFI.proofCoefficientEvals b2WrapResult.proof)
            , sigmaEvals: map peWF (ProofFFI.proofSigmaEvals b2WrapResult.proof)
            , indexEvals: map peWF (ProofFFI.proofIndexEvals b2WrapResult.proof)
            }

      b3WrapAdviceInput :: BuildWrapAdviceInput 1 (Slots1 1)
      b3WrapAdviceInput =
        { stepProof: b3Result.proof
        , whichBranch: F zero
        , prevUnfinalizedProofs: b3StepPerProof :< Vector.nil
        , prevMessagesForNextStepProofHash:
            F (fromBigInt (toBigInt b3MsgForNextStepDigest) :: WrapField)
        , prevStepAccs: WeierstrassAffinePoint { x: F b2StepOpeningSg.x, y: F b2StepOpeningSg.y } :< Vector.nil
        , prevOldBpChals: slots1 ((map F b2MsgForNextWrapRealChals) :< Vector.nil)
        , prevEvals: b3WrapPrevEvalsForAdvice :< Vector.nil
        , prevWrapDomainIndices: F (fromInt 1 :: WrapField) :< Vector.nil
        }

      b3WrapAdvice :: WrapAdvice 1 (Slots1 1)
      b3WrapAdvice = buildWrapAdvice b3WrapAdviceInput

      b3WrapProveCtx =
        { wrapMainConfig: wrapCtx.wrapMainConfig
        , crs: pallasProofCrs
        , publicInput: b3WrapPublicInput
        , advice: b3WrapAdvice
        , kimchiPrevChallenges:
            let
              padEntry =
                { sgX: wrapSg.x
                , sgY: wrapSg.y
                , challenges: map (fromBigInt <<< toBigInt)
                    Dummy.dummyIpaChallenges.wrapExpanded
                }
              realEntry =
                { sgX: b3ChalPolyComm.x
                , sgY: b3ChalPolyComm.y
                , challenges: b3MsgForNextWrapRealChals
                }
            in
              padEntry :< realEntry :< Vector.nil
        }

    b3WrapResult <- liftEffect $
      wrapSolveAndProve @1 @(Slots1 1)
        (\e -> Exc.throwException e)
        b3WrapProveCtx
        wrapCR

    let
      b3WrapProofValid = ProofFFI.verifyOpeningProof
        wrapCR.verifierIndex
        { proof: b3WrapResult.proof, publicInput: b3WrapResult.publicInputs }
    liftEffect $ Trace.int "b3.wrap.proof.self_verify" (if b3WrapProofValid then 1 else 0)
    when (not b3WrapProofValid)
      $ liftEffect
      $ Exc.throw "b3 wrap proof FAILED self-verify"

    liftEffect $ Trace.string "simple_chain.end" "inductive_case_verified"
