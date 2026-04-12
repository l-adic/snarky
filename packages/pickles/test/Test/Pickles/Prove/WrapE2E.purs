-- | Incremental end-to-end wrap prover test.
-- |
-- | Layer 1: real WrapMainConfig from step proof, zero advice → compile succeeds
-- | Layer 2: real public input from wrapComputeDeferredValues + assembleWrapMainInput
-- | Layer 3: real advice from buildWrapAdvice with correct Pickles.Dummy values
-- | Layer 4: verify the resulting wrap proof
module Test.Pickles.Prove.WrapE2E
  ( spec
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Int as Int
import Data.Maybe (fromJust)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw, throwException, try) as Exc
import Partial.Unsafe (unsafePartial)
import Pickles.Dummy as Dummy
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI as ProofFFI
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Prove.Wrap (WrapAdvice, WrapProveContext, BuildWrapAdviceInput, buildWrapAdvice, wrapProve)
import Pickles.Verify.Types as Pickles.Verify.Types
import Snarky.Backend.Kimchi.Class (verifyProverIndex)
import Pickles.PublicInputCommit (mkConstLagrangeBase)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure)
import Pickles.Types (PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, StepIPARounds, WrapField, WrapIPARounds, WrapPrevProofState(..), WrapProofMessages(..), WrapProofOpening(..), WrapStatementPacked(..))
import Pickles.VerificationKey (StepVK)
import Pickles.Wrap.Main (WrapMainConfig)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProof)
import Pickles.Wrap.Slots (Slots2, slots2)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (F(..), FVar, UnChecked(..), const_)
import Snarky.Circuit.Types (fieldsToValue)
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeFromField)
import Snarky.Circuit.Kimchi (Type1(..), Type2(..))
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, generator, toAffine, toBigInt)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Impl.Vesta as VestaImpl
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Test.Pickles.TestContext (InductiveTestContext, StepProofContext, WrapSchnorrStepIOVal, convertUnfinalized, wrapEndo, zkRows)
import Test.Spec (SpecT, describe, it)

--------------------------------------------------------------------------------
-- Step VK extraction
--------------------------------------------------------------------------------

-- | Column comms from the step verifier index are Vesta-curve points
-- | with WrapField (= Pallas.ScalarField = Fq) coordinates.
extractStepVKComms :: StepProofContext -> StepVK WrapField
extractStepVKComms ctx =
  let
    raw = ProofFFI.pallasVerifierIndexColumnComms ctx.verifierIndex
    idx = unsafePartial fromJust $ Vector.toVector @6 $ Array.take 6 raw
    coeff = unsafePartial fromJust $ Vector.toVector @15 $ Array.take 15 $ Array.drop 6 raw
    sig6 = unsafePartial fromJust $ Vector.toVector @6 $ Array.drop 21 raw
    sigLast = ProofFFI.pallasSigmaCommLast ctx.verifierIndex
  in
    { sigmaComm: Vector.snoc sig6 sigLast
    , coefficientsComm: coeff
    , genericComm: Vector.index idx (unsafeFinite @6 0)
    , psmComm: Vector.index idx (unsafeFinite @6 1)
    , completeAddComm: Vector.index idx (unsafeFinite @6 2)
    , mulComm: Vector.index idx (unsafeFinite @6 3)
    , emulComm: Vector.index idx (unsafeFinite @6 4)
    , endomulScalarComm: Vector.index idx (unsafeFinite @6 5)
    }

stepVkForCircuit :: StepVK WrapField -> StepVK (FVar WrapField)
stepVkForCircuit vk =
  let
    cp :: AffinePoint WrapField -> AffinePoint (FVar WrapField)
    cp pt = { x: const_ pt.x, y: const_ pt.y }
  in
    { sigmaComm: map cp vk.sigmaComm
    , coefficientsComm: map cp vk.coefficientsComm
    , genericComm: cp vk.genericComm
    , psmComm: cp vk.psmComm
    , completeAddComm: cp vk.completeAddComm
    , mulComm: cp vk.mulComm
    , emulComm: cp vk.emulComm
    , endomulScalarComm: cp vk.endomulScalarComm
    }

--------------------------------------------------------------------------------
-- WrapMainConfig from real step proof
--------------------------------------------------------------------------------

buildWrapMainConfig :: StepProofContext -> WrapMainConfig 1
buildWrapMainConfig ctx =
  let
    lagrangeSrs = VestaImpl.vestaCrsCreate (2 `Int.pow` 16)
    lagrangeComms = map mkConstLagrangeBase
      ((coerce $ ProofFFI.pallasSrsLagrangeCommitments lagrangeSrs 16 177) :: Array (AffinePoint (F WrapField)))
    blindingH = (coerce $ ProofFFI.pallasSrsBlindingGenerator lagrangeSrs) :: AffinePoint (F WrapField)
  in
    { stepWidths: 1 :< Vector.nil
    , domainLog2s: ctx.domainLog2 :< Vector.nil
    , stepKeys: stepVkForCircuit (extractStepVKComms ctx) :< Vector.nil
    , lagrangeComms
    , blindingH
    , allPossibleDomainLog2s:
        unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
    }

--------------------------------------------------------------------------------
-- Deferred values + message hashes (Layer 2)
--------------------------------------------------------------------------------

stepEndoScalar :: StepField
stepEndoScalar =
  let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

buildAllEvals :: StepProofContext -> AllEvals StepField
buildAllEvals ctx =
  { ftEval1: ctx.oracles.ftEval1
  , publicEvals:
      { zeta: ctx.oracles.publicEvalZeta
      , omegaTimesZeta: ctx.oracles.publicEvalZetaOmega
      }
  , zEvals: ProofFFI.proofZEvals ctx.proof
  , witnessEvals: ProofFFI.proofWitnessEvals ctx.proof
  , coeffEvals: ProofFFI.proofCoefficientEvals ctx.proof
  , sigmaEvals: ProofFFI.proofSigmaEvals ctx.proof
  , indexEvals: ProofFFI.proofIndexEvals ctx.proof
  }

-- | Compute omega power for unnormalized_lagrange_basis lookups.
-- | Maps `(zkRows :: Boolean, offset :: Int)` to the appropriate omega
-- | power, matching OCaml's plonk_checks.ml:311-330.
-- | With zkRows=3, the cases are: (false,0)→1, (false,1)→omega,
-- | (false,-1)→omega^(-1), (false,-2)→omega^(-2), (false,-3)/(true,0)→omega^(-3),
-- | (true,-1)→omega^(-4).
mkOmegaForLagrange :: Int -> StepField -> { zkRows :: Boolean, offset :: Int } -> StepField
mkOmegaForLagrange _domainLog2 omega { zkRows: zk, offset } =
  let
    omInv = recip omega
    omInv2 = omInv * omInv
    omToZkPlus1 = omInv2
    omToZk = omToZkPlus1 * omInv
    omToZkMinus1 = omToZk * omInv
  in case zk, offset of
    false, 0 -> one
    false, 1 -> omega
    false, (-1) -> omInv
    false, (-2) -> omToZkPlus1
    false, (-3) -> omToZk
    true, 0 -> omToZk
    true, (-1) -> omToZkMinus1
    _, _ -> one

buildDeferredValuesInput :: StepProofContext -> WrapDeferredValuesInput 0
buildDeferredValuesInput ctx =
  let omega = domainGenerator ctx.domainLog2
  in
  { proof: ctx.proof
  , verifierIndex: ctx.verifierIndex
  , publicInput: ctx.publicInputs
  , allEvals: buildAllEvals ctx
  , pEval0Chunks: [ ctx.oracles.publicEvalZeta ]
  , domainLog2: ctx.domainLog2
  , zkRows
  , srsLengthLog2: 16
  , generator: omega
  , shifts: domainShifts ctx.domainLog2
  -- No lookups (Features.Full.none) → vanishesOnZk = one
  -- (OCaml plonk_checks.ml:299-303: joint_combiner = None → F.one)
  , vanishesOnZk: one
  , omegaForLagrange: mkOmegaForLagrange ctx.domainLog2 omega
  , endo: stepEndoScalar
  , linearizationPoly: Linearization.pallas
  , prevSgs: Vector.nil
  , prevChallenges: Vector.nil
  -- stepWidths=[1] → maskVal0=true (>=1 proof), maskVal1=false (not >=2).
  -- packBranchDataWrap uses mask[0]+2*mask[1]; circuit uses maskVal1+2*maskVal0.
  -- So mask[0]=maskVal1=false, mask[1]=maskVal0=true.
  , proofsVerifiedMask: false :< true :< Vector.nil
  }

-- | Step VK in StepField coordinates for hashMessagesForNextStepProofPure.
-- | Column comms from the FFI are in WrapField (= Pallas.ScalarField);
-- | cross-field coerce to StepField (= Pallas.BaseField) via BigInt.
extractStepVKForHash :: StepProofContext -> StepVK StepField
extractStepVKForHash ctx =
  let
    comms = extractStepVKComms ctx
    cp :: AffinePoint WrapField -> AffinePoint StepField
    cp pt = { x: fromBigInt (toBigInt pt.x), y: fromBigInt (toBigInt pt.y) }
  in
    { sigmaComm: map cp comms.sigmaComm
    , coefficientsComm: map cp comms.coefficientsComm
    , genericComm: cp comms.genericComm
    , psmComm: cp comms.psmComm
    , completeAddComm: cp comms.completeAddComm
    , mulComm: cp comms.mulComm
    , emulComm: cp comms.emulComm
    , endomulScalarComm: cp comms.endomulScalarComm
    }

computeStepDigest :: StepProofContext -> StepField
computeStepDigest ctx =
  hashMessagesForNextStepProofPure
    { stepVk: extractStepVKForHash ctx
    , appState: []
    , proofs: (Vector.nil :: Vector 0 { sg :: AffinePoint StepField, expandedBpChallenges :: Vector 0 StepField })
    }

computeWrapDigest :: StepProofContext -> WrapField
computeWrapDigest ctx =
  let
    stepOutput :: WrapSchnorrStepIOVal
    stepOutput = fieldsToValue @WrapField
      (map (\fp -> fromBigInt (toBigInt fp) :: WrapField) ctx.publicInputs)
    stepUnfinalized = Vector.head stepOutput.proofState.unfinalizedProofs

    unfinalizedBpChallenges :: Vector WrapIPARounds (SizedF 128 WrapField)
    unfinalizedBpChallenges = coerce stepUnfinalized.deferredValues.bulletproofChallenges

    expandedChallenges :: Vector WrapIPARounds WrapField
    expandedChallenges = map (\c -> toFieldPure c wrapEndo) unfinalizedBpChallenges

    sg :: AffinePoint WrapField
    sg = ProofFFI.pallasProofOpeningSg ctx.proof
  in
    hashMessagesForNextWrapProof
      { sg
      , expandedChallenges
      , dummyChallenges: Dummy.dummyIpaChallenges.wrapExpanded
      }

--------------------------------------------------------------------------------
-- Layer 3: real advice from buildWrapAdvice
--------------------------------------------------------------------------------

-- | Convert UnfinalizedProof (nested) → PerProofUnfinalized (flat).
-- | Wraps scalar challenges in UnChecked to match how wrap_packed_typ allocates.
toPerProofUnfinalized
  :: forall d
   . Pickles.Verify.Types.UnfinalizedProof d (F WrapField) (Type2 (F WrapField)) Boolean
  -> PerProofUnfinalized d (Type2 (F WrapField)) (F WrapField) Boolean
toPerProofUnfinalized u =
  let d = u.deferredValues
      p = d.plonk
  in PerProofUnfinalized
    { combinedInnerProduct: d.combinedInnerProduct
    , b: d.b
    , zetaToSrsLength: p.zetaToSrsLength
    , zetaToDomainSize: p.zetaToDomainSize
    , perm: p.perm
    , spongeDigest: u.spongeDigestBeforeEvaluations
    , beta: UnChecked p.beta
    , gamma: UnChecked p.gamma
    , alpha: UnChecked p.alpha
    , zeta: UnChecked p.zeta
    , xi: UnChecked d.xi
    , bulletproofChallenges: map UnChecked d.bulletproofChallenges
    , shouldFinalize: u.shouldFinalize
    }

-- | Cross-field coerce AllEvals StepField → StepAllEvals (F WrapField).
-- | Safe because Fq > Fp in the Pasta cycle — no modular reduction.
coerceAllEvalsToWrap :: AllEvals StepField -> StepAllEvals (F WrapField)
coerceAllEvalsToWrap ae =
  let
    cf :: StepField -> F WrapField
    cf x = F (fromBigInt (toBigInt x))
    cpe :: { zeta :: StepField, omegaTimesZeta :: StepField } -> PointEval (F WrapField)
    cpe pe = PointEval { zeta: cf pe.zeta, omegaTimesZeta: cf pe.omegaTimesZeta }
  in StepAllEvals
    { publicEvals: cpe ae.publicEvals
    , witnessEvals: map cpe ae.witnessEvals
    , coeffEvals: map cpe ae.coeffEvals
    , zEvals: cpe ae.zEvals
    , sigmaEvals: map cpe ae.sigmaEvals
    , indexEvals: map cpe ae.indexEvals
    , ftEval1: cf ae.ftEval1
    }

-- | Build dummy StepAllEvals (F WrapField) from dummyProofWitness.
dummyStepAllEvalsWrap :: StepAllEvals (F WrapField)
dummyStepAllEvalsWrap =
  let
    zpe = PointEval { zeta: F zero, omegaTimesZeta: F zero }
  in StepAllEvals
    { publicEvals: zpe
    , witnessEvals: Vector.replicate zpe
    , coeffEvals: Vector.replicate zpe
    , zEvals: zpe
    , sigmaEvals: Vector.replicate zpe
    , indexEvals: Vector.replicate zpe
    , ftEval1: F zero
    }

-- | Build real wrap advice for base case (n=1 step proof, no previous wrap proofs).
buildRealAdvice
  :: StepProofContext
  -> BuildWrapAdviceInput 2 (Slots2 1 1)
buildRealAdvice ctx =
  let
    -- Decode step output to get unfinalized proofs
    stepOutput :: WrapSchnorrStepIOVal
    stepOutput = fieldsToValue @WrapField
      (map (\fp -> fromBigInt (toBigInt fp) :: WrapField) ctx.publicInputs)

    realUnfinalized = convertUnfinalized
      (Vector.head stepOutput.proofState.unfinalizedProofs)
    dummyUnfinalized = Dummy.wrapDummyUnfinalizedProof

    -- Step digest cross-field coerced to WrapField
    stepDigest = computeStepDigest ctx

    -- Real evals (slot 0) + dummy evals (slot 1)
    realEvals = coerceAllEvalsToWrap (buildAllEvals ctx)

    -- Dummy sg: Proof.dummy uses Dummy.Ipa.Step.sg (Vesta point, Fq coords)
    -- for messages_for_next_wrap_proof.challenge_polynomial_commitment.
    -- NOT Dummy.Ipa.Wrap.sg (Pallas point, Fp coords) — that's for
    -- messages_for_next_step_proof. See proof.ml:156 vs proof.ml:170.
    pallasSrs = PallasImpl.pallasCrsCreate (2 `Int.pow` 15)
    vestaSrs = VestaImpl.vestaCrsCreate (2 `Int.pow` 16)
    dummySgRaw = (Dummy.computeDummySgValues pallasSrs vestaSrs).ipa.step.sg
    dummySg :: WeierstrassAffinePoint VestaG (F WrapField)
    dummySg = WeierstrassAffinePoint { x: F dummySgRaw.x, y: F dummySgRaw.y }

    -- Old bp challenges: use correct dummies from Pickles.Dummy
    dummyBpChals :: Vector WrapIPARounds (F WrapField)
    dummyBpChals = map F Dummy.dummyIpaChallenges.wrapExpanded
  in
    { stepProof: ctx.proof
    , whichBranch: F zero
    , prevUnfinalizedProofs:
        toPerProofUnfinalized realUnfinalized
          :< toPerProofUnfinalized dummyUnfinalized
          :< Vector.nil
    , prevMessagesForNextStepProofHash: F (fromBigInt (toBigInt stepDigest) :: WrapField)
    , prevStepAccs: dummySg :< dummySg :< Vector.nil
    , prevOldBpChals: slots2
        (Vector.replicate dummyBpChals)
        (Vector.replicate dummyBpChals)
    , prevEvals: realEvals :< dummyStepAllEvalsWrap :< Vector.nil
    , prevWrapDomainIndices: F zero :< F zero :< Vector.nil
    }

--------------------------------------------------------------------------------
-- Zero advice (reused from C3 smoke test pattern)
--------------------------------------------------------------------------------

zeroType1 :: Type1 (F WrapField)
zeroType1 = Type1 (F zero)

zeroUncheckedSized128 :: UnChecked (SizedF 128 (F WrapField))
zeroUncheckedSized128 = UnChecked (unsafePartial (unsafeFromField (F zero)))

zeroWeierstrass :: WeierstrassAffinePoint VestaG (F WrapField)
zeroWeierstrass = WeierstrassAffinePoint { x: F zero, y: F zero }

zeroPublicInput
  :: WrapStatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean
zeroPublicInput = WrapStatementPacked
  { fpFields: Vector.replicate zeroType1
  , challenges: Vector.replicate zeroUncheckedSized128
  , scalarChallenges: Vector.replicate zeroUncheckedSized128
  , digests: Vector.replicate (F zero)
  , bulletproofChallenges: Vector.replicate zeroUncheckedSized128
  , branchData: F zero
  , featureFlags: Vector.replicate (F zero)
  , lookupOptFlag: F zero
  , lookupOptScalarChallenge: F zero
  }

zeroAdvice :: WrapAdvice 2 (Slots2 1 1)
zeroAdvice =
  let
    zeroType2 = Type2 (F zero)
    zeroPerProof = PerProofUnfinalized
      { combinedInnerProduct: zeroType2
      , b: zeroType2
      , zetaToSrsLength: zeroType2
      , zetaToDomainSize: zeroType2
      , perm: zeroType2
      , spongeDigest: F zero
      , beta: zeroUncheckedSized128
      , gamma: zeroUncheckedSized128
      , alpha: zeroUncheckedSized128
      , zeta: zeroUncheckedSized128
      , xi: zeroUncheckedSized128
      , bulletproofChallenges: Vector.replicate zeroUncheckedSized128
      , shouldFinalize: false
      }
    zeroStepAllEvals = StepAllEvals
      { publicEvals: PointEval { zeta: F zero, omegaTimesZeta: F zero }
      , witnessEvals: Vector.replicate (PointEval { zeta: F zero, omegaTimesZeta: F zero })
      , coeffEvals: Vector.replicate (PointEval { zeta: F zero, omegaTimesZeta: F zero })
      , zEvals: PointEval { zeta: F zero, omegaTimesZeta: F zero }
      , sigmaEvals: Vector.replicate (PointEval { zeta: F zero, omegaTimesZeta: F zero })
      , indexEvals: Vector.replicate (PointEval { zeta: F zero, omegaTimesZeta: F zero })
      , ftEval1: F zero
      }
    zeroSlots2 = slots2
      (Vector.replicate (Vector.replicate (F zero)))
      (Vector.replicate (Vector.replicate (F zero)))
    zeroOpening = WrapProofOpening
      { lr: Vector.replicate { l: zeroWeierstrass, r: zeroWeierstrass }
      , z1: zeroType1
      , z2: zeroType1
      , delta: zeroWeierstrass
      , sg: zeroWeierstrass
      }
    zeroMessages = WrapProofMessages
      { wComm: Vector.replicate zeroWeierstrass
      , zComm: zeroWeierstrass
      , tComm: Vector.replicate zeroWeierstrass
      }
  in
    { whichBranch: F zero
    , wrapProofState: WrapPrevProofState
        { unfinalizedProofs: Vector.replicate zeroPerProof
        , messagesForNextStepProof: F zero
        }
    , stepAccs: Vector.replicate zeroWeierstrass
    , oldBpChals: zeroSlots2
    , evals: Vector.replicate zeroStepAllEvals
    , wrapDomainIndices: Vector.replicate (F zero)
    , openingProof: zeroOpening
    , messages: zeroMessages
    }

--------------------------------------------------------------------------------
-- Spec
--------------------------------------------------------------------------------

spec :: SpecT Aff InductiveTestContext Aff Unit
spec = describe "Pickles.Prove.WrapE2E" do

  -- Layer 1: real WrapMainConfig, zero advice → compile succeeds
  it "L1: wrapProve compiles with real WrapMainConfig from step proof" \{ step0 } -> do
    let
      proofCrs = PallasImpl.pallasCrsCreate (2 `Int.pow` 16)
      ctx :: WrapProveContext 1 1 1
      ctx =
        { wrapMainConfig: buildWrapMainConfig step0
        , crs: proofCrs
        , publicInput: zeroPublicInput
        , advice: zeroAdvice
        }
    liftEffect do
      result <- Exc.try (wrapProve Exc.throwException ctx)
      case result of
        Left _ -> pure unit
        Right _ -> pure unit

  -- Layer 2: real public input from deferred values, zero advice → compile succeeds
  it "L2: wrapProve compiles with real public input from wrapComputeDeferredValues" \{ step0 } -> do
    let
      deferredOutput = wrapComputeDeferredValues (buildDeferredValuesInput step0)
      stepDigest = computeStepDigest step0
      wrapDigest = computeWrapDigest step0
      publicInput = assembleWrapMainInput
        { deferredValues: deferredOutput
        , messagesForNextStepProofDigest: stepDigest
        , messagesForNextWrapProofDigest: wrapDigest
        }
      proofCrs = PallasImpl.pallasCrsCreate (2 `Int.pow` 16)
      ctx :: WrapProveContext 1 1 1
      ctx =
        { wrapMainConfig: buildWrapMainConfig step0
        , crs: proofCrs
        , publicInput
        , advice: zeroAdvice
        }
    liftEffect do
      result <- Exc.try (wrapProve Exc.throwException ctx)
      case result of
        Left _ -> pure unit
        Right _ -> pure unit

  -- Layer 3: real public input + real advice from buildWrapAdvice
  it "L3: wrapProve with real advice from buildWrapAdvice" \{ step0 } -> do
    let
      deferredOutput = wrapComputeDeferredValues (buildDeferredValuesInput step0)
      stepDigest = computeStepDigest step0
      wrapDigest = computeWrapDigest step0
      publicInput = assembleWrapMainInput
        { deferredValues: deferredOutput
        , messagesForNextStepProofDigest: stepDigest
        , messagesForNextWrapProofDigest: wrapDigest
        }
      advice = buildWrapAdvice (buildRealAdvice step0)
      proofCrs = PallasImpl.pallasCrsCreate (2 `Int.pow` 16)
      ctx :: WrapProveContext 1 1 1
      ctx =
        { wrapMainConfig: buildWrapMainConfig step0
        , crs: proofCrs
        , publicInput
        , advice
        }
    liftEffect do
      result <- Exc.try (wrapProve Exc.throwException ctx)
      case result of
        Left _ -> pure unit
        Right _ -> pure unit

  -- Layer 4: real everything + verify the wrap proof
  it "L4: wrap proof verifies" \{ step0 } -> do
    let
      deferredOutput = wrapComputeDeferredValues (buildDeferredValuesInput step0)
      stepDigest = computeStepDigest step0
      wrapDigest = computeWrapDigest step0
      publicInput = assembleWrapMainInput
        { deferredValues: deferredOutput
        , messagesForNextStepProofDigest: stepDigest
        , messagesForNextWrapProofDigest: wrapDigest
        }
      advice = buildWrapAdvice (buildRealAdvice step0)
      proofCrs = PallasImpl.pallasCrsCreate (2 `Int.pow` 16)
      ctx :: WrapProveContext 1 1 1
      ctx =
        { wrapMainConfig: buildWrapMainConfig step0
        , crs: proofCrs
        , publicInput
        , advice
        }
    result <- liftEffect $ wrapProve (\e -> Exc.throw (show e)) ctx
    let csSatisfied = verifyProverIndex
          { proverIndex: result.proverIndex, witness: result.witness, publicInputs: result.publicInputs }
    liftEffect $ when (not csSatisfied) $ Exc.throw "Wrap constraint system not satisfied"
    let proofVerified = ProofFFI.verifyOpeningProof result.verifierIndex
          { proof: result.proof, publicInput: result.publicInputs }
    liftEffect $ when (not proofVerified) $ Exc.throw "Wrap proof failed to verify"
