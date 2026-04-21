-- | Reusable producer for the No_recursion_return base-case step + wrap
-- | proofs.
-- |
-- | Extracted from `Test.Pickles.Prove.NoRecursionReturn` so both that
-- | standalone test AND `Test.Pickles.Prove.TreeProofReturn` (which
-- | consumes a No_recursion_return proof as its slot-0 prev) can share
-- | the same prover. The producer emits the NRR trace lines (the
-- | `compile.*` VK blocks, `step.proof.public_input.*`,
-- | `wrap.witness.{col0,pi}.*`, `wrap.proof.opening.*`) to the active
-- | `PICKLES_TRACE_FILE`; callers wrap the producer in their own
-- | `begin`/`end` markers as their fixture dictates.
-- |
-- | The returned record exposes every artifact downstream tests need
-- | (both compile results, both prove results, the dummy wrap sg used
-- | as step_main's compile-time constant, and domain-log2 values).
-- | Tree_proof_return's slot-0 carrier injection reads from this.
module Test.Pickles.Prove.NoRecursionReturn.Producer
  ( NoRecursionReturnArtifacts
  , produceNoRecursionReturn
  ) where

import Prelude

import Control.Monad.State (evalState)
import Data.Array as Array
import Data.Const (Const)
import Data.Foldable (for_)
import Data.Map as Map
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw, throwException) as Exc
import Pickles.Dummy as Dummy
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI as ProofFFI
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, WrapDeferredValuesOutput, assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Prove.Step (StepAdvice(..), StepCompileResult, StepProveResult, StepRule, buildStepAdvice, extractWrapVKCommsAdvice, extractWrapVKForStepHash, stepCompile, stepSolveAndProve)
import Pickles.Prove.Wrap (BuildWrapAdviceInput, WrapAdvice, WrapCompileResult, WrapProveResult, buildWrapAdvice, buildWrapMainConfig, extractStepVKComms, wrapCompile, wrapSolveAndProve, zeroWrapAdvice)
import Pickles.Prove.Wrap (WrapCompileContext) as WP
import Pickles.Step.Prevs (PrevsSpecNil)
import Pickles.Trace as Trace
import Pickles.Types (StepField, WrapField, WrapIPARounds)
import Pickles.Util.Fatal (fromJust')
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Pickles.Wrap.Slots (NoSlots, noSlots)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.CVar (getVariable)
import Snarky.Circuit.DSL (F(..), FVar, const_)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, toBigInt)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | The No_recursion_return rule: `output = 0`, N = 0 prev proofs,
-- | Output mode (input = Unit, output = Field).
-- | Reference: test_no_sideloaded.ml:100-107
nrrRule :: StepRule 0 Unit Unit (F StepField) (FVar StepField) Unit Unit
nrrRule _ = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: const_ zero
  }

-- | Artifacts produced by running the No_recursion_return base case.
-- | `stepCR` / `wrapCR` are the compile results (proverIndex +
-- | verifierIndex + constraint system). `stepResult` / `wrapResult`
-- | are the prove results (proofs, witnesses, public inputs, assignments).
-- | `wrapSg` is the dummy wrap sg constant used in step_main.
type NoRecursionReturnArtifacts =
  { stepCR :: StepCompileResult
  , wrapCR :: WrapCompileResult
  , stepResult :: StepProveResult 1
  , wrapResult :: WrapProveResult
  , wrapSg :: AffinePoint StepField
  , stepSg :: AffinePoint WrapField -- dummy Step IPA sg (Vesta)
  , stepDomainLog2 :: Int
  , wrapDomainLog2 :: Int
  -- | Output of `wrapComputeDeferredValues` over NRR's step proof.
  -- | Downstream (Tree_proof_return slot-0 injection) reads this
  -- | for `wrapPlonkRaw`, `wrapBranchData`,
  -- | `wrapSpongeDigest`, etc.
  , wrapDv :: WrapDeferredValuesOutput
  -- | NRR's wrap public input (for feeding vestaProofOracles
  -- | downstream).
  , wrapPublicInput :: Array WrapField
  }

-- | Produce the No_recursion_return base-case step + wrap proofs.
-- |
-- | Emits trace lines matching the OCaml `dump_no_recursion_return.exe`
-- | fixture (modulo the `begin`/`end` markers, which are test-specific).
produceNoRecursionReturn
  :: { vestaSrs :: CRS VestaG
     , lagrangeSrs :: CRS PallasG
     , pallasProofCrs :: CRS PallasG
     }
  -> Aff NoRecursionReturnArtifacts
produceNoRecursionReturn { vestaSrs, lagrangeSrs, pallasProofCrs } = do
  -- Ro-derived Dummy.Ipa.Wrap.sg (step_main's compile-time constant).
  -- Unused at N=0 (no verify_one) but required by stepCompile.
  let
    -- Base-case dummies at max_proofs_verified=0. All padding slots are
    -- masked away at N=0 so the specific bit positions don't affect
    -- the witness; we just need SOMETHING of type BaseCaseDummies to
    -- satisfy stepCompile's type signature.
    baseCaseDummies = evalState (Dummy.computeBaseCaseDummies { maxProofsVerified: 0 }) Dummy.initialRo
    dummySgValues = Dummy.computeDummySgValues baseCaseDummies lagrangeSrs vestaSrs
    wrapSg = dummySgValues.ipa.wrap.sg
    -- OCaml default wrap_domains for N0 → h = 2^13 (common.ml:25-29).
    wrapDomainLog2 = 13

    srsData =
      { perSlotLagrangeAt: Vector.nil
      , blindingH:
          (coerce $ ProofFFI.vestaSrsBlindingGenerator lagrangeSrs)
            :: AffinePoint (F StepField)
      , perSlotFopDomainLog2: Vector.nil
      , perSlotKnownWrapKeys: Vector.nil
      }

    ctx =
      { srsData
      , dummySg: wrapSg
      , crs: vestaSrs
      }

    placeholderAdvice = buildStepAdvice @PrevsSpecNil
      { publicInput: unit
      , mostRecentWidth: 0
      , wrapDomainLog2
      , baseCaseDummies
      }

  -- ===== Phase 1: compile the step circuit =====
  stepCR <- liftEffect $
    stepCompile @PrevsSpecNil @1 @Unit @Unit @(F StepField) @(FVar StepField) @Unit @Unit
      ctx
      nrrRule
      placeholderAdvice

  -- ===== Emit step VK + compile metadata =====
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
  let
    wrapCtx :: WP.WrapCompileContext 1
    wrapCtx =
      { wrapMainConfig:
          buildWrapMainConfig vestaSrs stepCR.verifierIndex
            { stepWidth: 0, domainLog2: stepDomainLog2 }
      , crs: pallasProofCrs
      }
  wrapCR <- liftEffect $
    wrapCompile @1 @NoSlots wrapCtx (zeroWrapAdvice :: WrapAdvice 0 (Const Unit))

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

  -- ===== Phase 3: step prove =====
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
      nrrRule
      stepCR
      realAdvice

  liftEffect $ for_ (Array.mapWithIndex Tuple stepResult.publicInputs) \(Tuple i x) ->
    Trace.field ("step.proof.public_input." <> show i) x

  -- ===== Phase 4: wrap prove =====
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

    wrapDvInput :: WrapDeferredValuesInput 0
    wrapDvInput =
      { proof: stepResult.proof
      , verifierIndex: stepCR.verifierIndex
      , publicInput: stepResult.publicInputs
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
      , prevSgs: Vector.nil
      , prevChallenges: Vector.nil
      , proofsVerifiedMask: false :< false :< Vector.nil
      }

    wrapDv = wrapComputeDeferredValues wrapDvInput

    msgForNextStepDigest :: StepField
    msgForNextStepDigest =
      fromJust'
        "NoRecursionReturn.Producer: step PI[0] must exist" $
        Array.index stepResult.publicInputs 0

    wrapProofSg :: AffinePoint WrapField
    wrapProofSg = ProofFFI.pallasProofOpeningSg stepResult.proof

    msgForNextWrapDummyChals :: Vector WrapIPARounds WrapField
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

  pure
    { stepCR
    , wrapCR
    , stepResult
    , wrapResult
    , wrapSg
    , stepSg: dummySgValues.ipa.step.sg
    , stepDomainLog2
    , wrapDomainLog2
    , wrapDv
    , wrapPublicInput: wrapResult.publicInputs
    }
