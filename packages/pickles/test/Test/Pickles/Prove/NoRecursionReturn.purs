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
import Data.Const (Const)
import Data.Int.Bits as Int
import Data.Map as Map
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw, throwException) as Exc
import Data.Foldable (for_)
import Pickles.Dummy as Dummy
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI as ProofFFI
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Prove.Step (StepAdvice(..), StepRule, buildStepAdvice, extractWrapVKCommsAdvice, extractWrapVKForStepHash, stepCompile, stepSolveAndProve)
import Pickles.Prove.Wrap (BuildWrapAdviceInput, WrapAdvice, buildWrapAdvice, buildWrapMainConfig, extractStepVKComms, wrapCompile, wrapSolveAndProve, zeroWrapAdvice)
import Pickles.Prove.Wrap (WrapCompileContext) as WP
import Pickles.Step.Prevs (PrevsSpecNil)
import Pickles.Trace as Trace
import Pickles.Types (StepField, WrapField, WrapIPARounds)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Pickles.Wrap.Slots (NoSlots, noSlots)
import Pickles.Util.Fatal (fromJust')
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.CVar (getVariable)
import Snarky.Circuit.DSL (F(..), FVar, const_)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, toBigInt)
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Spec (SpecT, describe, it)

-- | The No_recursion_return rule: `output = 0`, N = 0 prev proofs,
-- | Output mode (input = Unit, output = Field).
-- | Reference: test_no_sideloaded.ml:100-107
noRecursionReturnRule :: StepRule 0 Unit Unit (F StepField) (FVar StepField) Unit Unit
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

    -- ===== Phase 2: compile the wrap circuit =====
    let stepDomainLog2' = ProofFFI.pallasProverIndexDomainLog2 stepCR.proverIndex
    let pallasProofCrs = pallasWrapSrs
    let
      wrapCtx :: WP.WrapCompileContext 1
      wrapCtx =
        { wrapMainConfig:
            buildWrapMainConfig vestaSrs stepCR.verifierIndex
              { stepWidth: 0, domainLog2: stepDomainLog2' }
        , crs: pallasProofCrs
        }
    let n0ZeroAdvice = (zeroWrapAdvice :: WrapAdvice 0 (Const Unit))
    wrapCR <- liftEffect $ wrapCompile @1 @NoSlots wrapCtx n0ZeroAdvice

    -- ===== Emit wrap CS + wrapVK =====
    -- OCaml compile.ml emits (in order): wrapCS.domain_log2,
    -- wrapCS.public_input_size, then the wrapVK point commitments.
    -- The wrap CS's domain_log2 is the kimchi prover-index's
    -- log_size_of_group; mirroring OCaml's `Kimchi.circuit_info` emit.
    let wrapDomainLog2' = ProofFFI.vestaProverIndexDomainLog2 wrapCR.proverIndex
    let wrapVkComms = extractWrapVKForStepHash wrapCR.verifierIndex
    liftEffect do
      Trace.int "compile.wrapCS.domain_log2" wrapDomainLog2'
      Trace.int "compile.wrapCS.public_input_size" (Array.length wrapCR.builtState.publicInputs)
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

    -- NOTE: `step_main_outer.vk.*`, `step_main_outer.app_state.*`,
    -- `step_main_outer.proof.*`, and `step_main_outer.digest` are
    -- emitted by the step_main circuit itself during step prove
    -- (`Pickles.Step.Main:667-724`), so no explicit emission here.

    -- ===== Phase 3: step prove =====
    -- N=0 has no prev proofs: reuse the placeholder advice for all
    -- `Vector len`-shaped fields (all empty at len=0), but swap in
    -- the REAL wrap VK commitments so `step_main`'s outer hash
    -- absorbs the compiled wrap key rather than `g0` placeholders.
    let
      StepAdvice placeholderAdviceRec = placeholderAdvice
      realAdvice = StepAdvice
        ( placeholderAdviceRec
            { wrapVerifierIndex = extractWrapVKCommsAdvice wrapCR.verifierIndex
            }
        )

    stepResult <- liftEffect $
      stepSolveAndProve @PrevsSpecNil @1 @Unit @Unit @(F StepField) @(FVar StepField) @Unit @Unit
        (\e -> Exc.throw ("stepSolveAndProve: " <> show e))
        ctx
        noRecursionReturnRule
        stepCR
        realAdvice

    liftEffect $ for_ (Array.mapWithIndex Tuple stepResult.publicInputs) \(Tuple i x) ->
      Trace.field ("step.proof.public_input." <> show i) x

    -- ===== Phase 4: wrap prove =====
    -- Run kimchi oracles on the fresh step proof. N=0 step has no
    -- prev proofs of its own, so `prevChallenges` is empty.
    let
      stepOracles = ProofFFI.pallasProofOracles stepCR.verifierIndex
        { proof: stepResult.proof
        , publicInput: stepResult.publicInputs
        , prevChallenges: []
        }

      stepAllEvals :: AllEvals StepField
      stepAllEvals =
        { ftEval1: stepOracles.ftEval1
        , publicEvals:
            { zeta: stepOracles.publicEvalZeta
            , omegaTimesZeta: stepOracles.publicEvalZetaOmega
            }
        , zEvals: ProofFFI.proofZEvals stepResult.proof
        , witnessEvals: ProofFFI.proofWitnessEvals stepResult.proof
        , coeffEvals: ProofFFI.proofCoefficientEvals stepResult.proof
        , sigmaEvals: ProofFFI.proofSigmaEvals stepResult.proof
        , indexEvals: ProofFFI.proofIndexEvals stepResult.proof
        }

      stepEndoScalar :: StepField
      stepEndoScalar =
        let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

      stepDomainLog2ForWrap = ProofFFI.pallasProverIndexDomainLog2 stepCR.proverIndex

      wrapDvInput :: WrapDeferredValuesInput 0
      wrapDvInput =
        { proof: stepResult.proof
        , verifierIndex: stepCR.verifierIndex
        , publicInput: stepResult.publicInputs
        , allEvals: stepAllEvals
        , pEval0Chunks: [ stepOracles.publicEvalZeta ]
        , domainLog2: stepDomainLog2ForWrap
        , zkRows: 3
        , srsLengthLog2: 16
        , generator: (domainGenerator stepDomainLog2ForWrap :: StepField)
        , shifts: (domainShifts stepDomainLog2ForWrap :: Vector.Vector 7 StepField)
        , vanishesOnZk: ProofFFI.permutationVanishingPolynomial
            { domainLog2: stepDomainLog2ForWrap, zkRows: 3, pt: stepOracles.zeta }
        , omegaForLagrange: \_ -> one
        , endo: stepEndoScalar
        , linearizationPoly: Linearization.pallas
        , prevSgs: Vector.nil
        , prevChallenges: Vector.nil
        -- N=0: both padded challenge slots are dummies (no real prev
        -- wrap proofs). Pack as [false, false] = 0.
        , proofsVerifiedMask: false :< false :< Vector.nil
        }

      wrapDv = wrapComputeDeferredValues wrapDvInput

      -- Step's one and only public input IS the outer digest
      -- (`step_main_outer.digest`); there are no FOP-packed fields
      -- at N=0. Grab it directly.
      msgForNextStepDigest :: StepField
      msgForNextStepDigest = fromJust'
        "NoRecursionReturn: step PI[0] must exist" $
        Array.index stepResult.publicInputs 0

      -- The NEW wrap proof's `messages_for_next_wrap_proof` hashes
      -- its own `sg` + padded-length-2 old bulletproof challenges.
      -- N=0 step → no prev wrap proofs → both padding slots use the
      -- wrap-endo dummy challenges (`Dummy.Ipa.Wrap.challenges_computed`
      -- in OCaml).
      wrapProofSg :: AffinePoint WrapField
      wrapProofSg = ProofFFI.pallasProofOpeningSg stepResult.proof

      msgForNextWrapDummyChals :: Vector.Vector WrapIPARounds WrapField
      msgForNextWrapDummyChals = Dummy.dummyIpaChallenges.wrapExpanded

      msgForNextWrapDigest :: WrapField
      msgForNextWrapDigest = hashMessagesForNextWrapProofPureGeneral
        { sg: wrapProofSg
        , paddedChallenges:
            msgForNextWrapDummyChals
              :< msgForNextWrapDummyChals
              :< Vector.nil
        }

      wrapPublicInput = assembleWrapMainInput
        { deferredValues: wrapDv
        , messagesForNextStepProofDigest: msgForNextStepDigest
        , messagesForNextWrapProofDigest: msgForNextWrapDigest
        }

      -- N=0 wrap advice: all prev-proof fields are Vector 0 = empty.
      wrapAdviceInput :: BuildWrapAdviceInput 0 NoSlots
      wrapAdviceInput =
        { stepProof: stepResult.proof
        , whichBranch: F zero
        , prevUnfinalizedProofs: Vector.nil
        , prevMessagesForNextStepProofHash:
            F (fromBigInt (toBigInt msgForNextStepDigest) :: WrapField)
        , prevStepAccs: Vector.nil
        , prevOldBpChals: noSlots
        , prevEvals: Vector.nil
        , prevWrapDomainIndices: Vector.nil
        }

      wrapAdvice :: WrapAdvice 0 NoSlots
      wrapAdvice = buildWrapAdvice wrapAdviceInput

      wrapProveCtx =
        { wrapMainConfig: wrapCtx.wrapMainConfig
        , crs: pallasProofCrs
        , publicInput: wrapPublicInput
        , advice: wrapAdvice
        -- Both PaddedLength=2 slots are padding (dummy sg + dummy chals).
        , kimchiPrevChallenges:
            let
              padEntry =
                { sgX: wrapSg.x
                , sgY: wrapSg.y
                , challenges: map (fromBigInt <<< toBigInt)
                    Dummy.dummyIpaChallenges.wrapExpanded
                }
            in
              padEntry :< padEntry :< Vector.nil
        }

    wrapResult <- liftEffect $
      wrapSolveAndProve @1 @NoSlots
        (\e -> Exc.throwException e)
        wrapProveCtx
        wrapCR

    liftEffect do
      -- `wrap.witness.col0.0..49` + `wrap.witness.pi.*` mirror OCaml
      -- `wrap.ml:517-526`. OCaml emits `Tock.Field.Vector.get
      -- auxiliary_inputs i` — the flat allocation-order vector of
      -- non-public witness variables that kimchi receives as its
      -- `auxiliary` input. PS allocates variables in a DIFFERENT
      -- order than OCaml (confirmed empirically: aux[0] differs
      -- despite identical gate structure). TODO: align allocation
      -- order — until then, col0 values diverge even though every
      -- other trace line (step_main_outer.*, ivp.trace.*,
      -- ipa.dbg.*, wrap.witness.pi.*, wrap.proof.opening.*) is
      -- byte-identical.
      let
        piLen = Array.length wrapResult.publicInputs
        auxEntries =
          Array.filter (\(Tuple vk _) -> getVariable vk > piLen)
            (Map.toUnfoldable wrapResult.assignments)
      for_ (Array.take 50 auxEntries) \(Tuple vk x) ->
        Trace.field ("wrap.witness.col0." <> show (getVariable vk - piLen - 1)) x
      for_ (Array.mapWithIndex Tuple wrapResult.publicInputs) \(Tuple i x) ->
        Trace.field ("wrap.witness.pi." <> show i) x
      let wrapSgOut = ProofFFI.vestaProofOpeningSg wrapResult.proof
      Trace.field "wrap.proof.opening.sg.x" wrapSgOut.x
      Trace.field "wrap.proof.opening.sg.y" wrapSgOut.y
      Trace.field "wrap.proof.opening.z1" (ProofFFI.vestaProofOpeningZ1 wrapResult.proof)
      Trace.field "wrap.proof.opening.z2" (ProofFFI.vestaProofOpeningZ2 wrapResult.proof)

    liftEffect $ Trace.string "no_recursion_return.end" "base_case_verified"
