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
import Data.Int.Bits as Int
import Data.Tuple (Tuple(..))
import Data.Fin (unsafeFinite)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw, throwException) as Exc
import Pickles.Dummy (computeDummySgValues, dummyIpaChallenges) as Dummy
import Pickles.Proof.Dummy (dummyWrapProof)
import Pickles.Prove.Step (dummyWrapTockPublicInput)
import Pickles.Dummy.SimpleChain (simpleChainDummyPlonk, simpleChainDummyPrevEvals)
import Pickles.Types (PaddedLength, StepField)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Prove.Step (StepRule, buildStepAdvice, buildStepAdviceWithOracles, extractWrapVKForStepHash, stepCompile, stepSolveAndProve)
import Pickles.Prove.Wrap (BuildWrapAdviceInput, WrapAdvice, buildWrapAdvice, buildWrapMainConfigN1, extractStepVKComms, wrapCompile, wrapSolveAndProve, zeroWrapAdvice)
import Pickles.Prove.Wrap (WrapCompileContext) as WP
import Pickles.ProofFFI (pallasComputeUT, pallasProofCommitments, pallasProofOpeningPrechallenges, pallasProofOpeningSg, pallasProofOracles, pallasProverIndexDomainLog2, pallasSpongeCheckpointBeforeChallenges, pallasSrsBlindingGenerator, pallasSrsLagrangeCommitmentAt, pallasVerifierIndexDigest, permutationVanishingPolynomial, proofCoefficientEvals, proofIndexEvals, proofSigmaEvals, proofWitnessEvals, proofZEvals, verifyOpeningProof, vestaSrsBlindingGenerator, vestaSrsLagrangeCommitmentAt) as ProofFFI
import Pickles.ProofFFI (OraclesResult)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure)
import Pickles.Types (PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, WrapField, WrapIPARounds)
import Pickles.VerificationKey (StepVK)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProof, hashMessagesForNextWrapProofPureGeneral)
import Pickles.Wrap.Slots (Slots1, slots1)
import Data.Maybe (Maybe(..), fromJust)
import Partial.Unsafe (unsafePartial)
import Node.Encoding (Encoding(..)) as Enc
import Node.FS.Sync (writeTextFile) as FS
import Node.Process as Process
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Snarky.Backend.Kimchi.Class (constraintSystemToJson) as Kimchi
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, fromInt, toBigInt)
import Snarky.Curves.Class as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Pickles.Trace as Trace
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Impl.Vesta as VestaImpl
import Snarky.Circuit.DSL (F(..), UnChecked(..), assertAny_, coerceViaBits, const_, equals_, exists, not_)
import Snarky.Types.Shifted (Type2, fromShifted, toShifted)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
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
simpleChainRule :: F StepField -> StepRule 1
simpleChainRule prevAppState self = do
  prev <- exists $ MT.lift $ pure prevAppState
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
      for_ [0, 1, 2, 3] \i -> do
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
    let dummySgValues = Dummy.computeDummySgValues lagrangeSrs vestaSrs
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
      stepCompile @1 @34 ctx (simpleChainRule (F (negate one))) placeholderAdvice

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
        , prevAppState: F (negate one)
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
    realAdvice <- liftEffect $ buildStepAdviceWithOracles
      { appState: F zero
      , prevAppState: F (negate one) -- OCaml `s_neg_one`
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
      }

    -- ===== Phase 4: run the step solver =====
    result <- liftEffect $
      stepSolveAndProve @1 @34
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
    let stepProofValid = ProofFFI.verifyOpeningProof
          stepCR.verifierIndex
          { proof: result.proof, publicInput: result.publicInputs }
    liftEffect $ Trace.int "step.proof.self_verify" (if stepProofValid then 1 else 0)
    when (not stepProofValid) $
      liftEffect $ Exc.throw "PS step proof FAILED kimchi batch_verify — step prover bug"

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
      let kimchiPrechals = ProofFFI.pallasProofOpeningPrechallenges
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
      let kimchiUT = ProofFFI.pallasComputeUT
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
        let Curves.EndoScalar e = Curves.endoScalar @Pallas.BaseField @WrapField
        in e

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
             (F WrapField) Boolean
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

      dummyStepAccPoint :: WeierstrassAffinePoint VestaG (F WrapField)
      dummyStepAccPoint = WeierstrassAffinePoint
        { x: F stepSg.x, y: F stepSg.y }

      dummyWrapBpChals :: Vector WrapIPARounds (F WrapField)
      dummyWrapBpChals =
        map (F <<< fromBigInt <<< toBigInt) Dummy.dummyIpaChallenges.wrapExpanded

      dummyStepAllEvalsW :: StepAllEvals (F WrapField)
      dummyStepAllEvalsW =
        let zpe = PointEval { zeta: F zero, omegaTimesZeta: F zero }
        in StepAllEvals
          { publicEvals: zpe
          , witnessEvals: Vector.replicate zpe
          , coeffEvals: Vector.replicate zpe
          , zEvals: zpe
          , sigmaEvals: Vector.replicate zpe
          , indexEvals: Vector.replicate zpe
          , ftEval1: F zero
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
        , prevEvals: dummyStepAllEvalsW :< Vector.nil
        , prevWrapDomainIndices: F zero :< Vector.nil
        }

      wrapAdvice :: WrapAdvice 1 (Slots1 1)
      wrapAdvice = buildWrapAdvice wrapAdviceInput

      wrapProveCtx =
        { wrapMainConfig: wrapCtx.wrapMainConfig
        , crs: pallasProofCrs
        , publicInput: wrapPublicInput
        , advice: wrapAdvice
        , kimchiPrevChallenges:
            let dummyAccEntry =
                  { sgX: wrapSg.x
                  , sgY: wrapSg.y
                  , challenges: map (fromBigInt <<< toBigInt)
                      Dummy.dummyIpaChallenges.wrapExpanded
                  }
            in dummyAccEntry :< dummyAccEntry :< Vector.nil
        }

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
      let kimchiCheckpoint = ProofFFI.pallasSpongeCheckpointBeforeChallenges
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

    liftEffect $ Trace.int "wrap.proof.public_input_count"
      (Array.length wrapResult.publicInputs)

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
      -- For Simple_chain base case (must_verify=false), the step circuit
      -- overrode sg to Ipa.Wrap.compute_sg(new_bp_chals) = Dummy.Ipa.Wrap.sg.
      -- So b1's wrapSg is the same as b0's.
      b1WrapSg :: AffinePoint StepField
      b1WrapSg = wrapSg

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

      -- wrapPlonkRaw for b1: the 128-bit raw plonk challenges from
      -- the b0 wrap statement. These are the step-field scalar challenges
      -- computed by wrapComputeDeferredValues.
      b1WrapPlonkRaw =
        { alpha: SizedF.unwrapF wrapDv.plonk.alpha
        , beta: SizedF.unwrapF wrapDv.plonk.beta
        , gamma: SizedF.unwrapF wrapDv.plonk.gamma
        , zeta: SizedF.unwrapF wrapDv.plonk.zeta
        }

      -- prevChalPolys for b1's oracles: padded accumulator.
      -- Slot 0 (padding): dummy
      -- Slot 1 (real): sg from b0 wrap statement's
      --   messages_for_next_step_proof.challenge_polynomial_commitments
      --   = Dummy.Ipa.Wrap.sg (for base case), paired with expanded
      --   old_bulletproof_challenges from b0 wrap statement.
      b1PrevChalPolys =
        let
          -- The expanded old_bp_chals from b0 wrap statement =
          -- expand(step.unf[0].deferred.bp_chals, Pallas.endo_scalar).
          -- For base case, step.unf[0].deferred.bp_chals = Dummy.Ipa.Step.challenges.
          -- We already computed these as msgForNextWrapRealChals.
          realEntry =
            { sg: b1WrapSg
            , challenges: msgForNextWrapRealChals
            }
          dummyEntry = baseCaseDummyChalPoly
        in
          dummyEntry :< realEntry :< Vector.nil

    b1Advice <- liftEffect $ buildStepAdviceWithOracles
      { appState: F one
      , prevAppState: F zero
      , mostRecentWidth: 1
      , wrapDomainLog2
      , wrapVK: wrapCR.verifierIndex
      , wrapSg: b1WrapSg
      , stepSg: b0StepSg
      , wrapProof: wrapResult.proof
      , wrapPublicInput: wrapResult.publicInputs
      , prevChalPolys: b1PrevChalPolys
      , wrapPlonkRaw: b1WrapPlonkRaw
      , wrapPrevEvals: b1WrapPrevEvals
      , wrapBranchData: wrapDv.branchData
      , wrapSpongeDigest: wrapDv.spongeDigestBeforeEvaluations
      , mustVerify: true
      }

    b1Result <- liftEffect $
      stepSolveAndProve @1 @34
        (\e -> Exc.throw ("b1 stepSolveAndProve: " <> show e))
        ctx
        (simpleChainRule (F zero))
        stepCR
        b1Advice

    let b1StepProofValid = ProofFFI.verifyOpeningProof
          stepCR.verifierIndex
          { proof: b1Result.proof, publicInput: b1Result.publicInputs }
    liftEffect $ Trace.int "b1.step.proof.self_verify" (if b1StepProofValid then 1 else 0)
    when (not b1StepProofValid) $
      liftEffect $ Exc.throw "b1 step proof FAILED self-verify"

    liftEffect $ Trace.string "simple_chain.end" "inductive_case_verified"
