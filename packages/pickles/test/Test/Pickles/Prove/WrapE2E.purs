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
import Data.Foldable (for_)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Sponge as Pickles.Sponge
import RandomOracle.Sponge as RandomOracle.Sponge
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.PackedStatement as Pickles.PackedStatement
import Pickles.ProofFFI as ProofFFI
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Prove.Wrap (WrapAdvice, WrapProveContext, BuildWrapAdviceInput, buildWrapAdvice, wrapProve)
import Pickles.Verify.Types as Pickles.Verify.Types
import Snarky.Backend.Kimchi.Class (verifyProverIndex)
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure)
import Pickles.Types (PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, StepIPARounds, VerificationKey(..), WrapField, WrapIPARounds, WrapPrevProofState(..), WrapProofMessages(..), WrapProofOpening(..), WrapStatementPacked(..))
import Pickles.VerificationKey (StepVK)
import Pickles.Wrap.Main (WrapMainConfig)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProof)
import Pickles.Wrap.Slots (Slots2, slots2)
import Safe.Coerce (coerce)
import Data.Array as Array
import Snarky.Circuit.DSL (F(..), FVar, UnChecked(..), const_)
import Snarky.Circuit.Types (class CircuitType, fieldsToValue, sizeInFields)
import Type.Proxy (Proxy(..))
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeFromField)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (Type1(..), Type2(..), fromShifted)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, fromInt, generator, toAffine, toBigInt)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Impl.Vesta as VestaImpl
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Control.Monad.Trans.Class (lift) as MT
import Data.Tuple (Tuple(..))
import Pickles.Step.Advice (class StepWitnessM)
import Pickles.Step.Circuit (WrapStatementPublicInput)
import Pickles.Step.Main (RuleOutput, stepMainPadded)
import Pickles.Dummy (dummyStepAdvice)
import Pickles.ProofFFI (proofOracles)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (SolverT, compile, makeSolver, makeSolver', runSolverT)
import Snarky.Backend.Prover (emptyProverState)
import Snarky.Backend.Compile as Snarky.Backend.Compile
import Snarky.Backend.Prover as Snarky.Backend.Prover
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (createCRS, createProverIndex, createVerifierIndex)
import Snarky.Circuit.DSL (class CircuitM, Snarky, assertAny_, equals_, exists, not_)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (EndoBase(..), endoBase)
import Snarky.Curves.Pasta (PallasG)
import Data.Newtype (un)
import Data.Array (concatMap)
import Pickles.Linearization.FFI (proverIndexDomainLog2)
import Pickles.ProofFFI (createProof)
import Test.Pickles.TestContext (InductiveTestContext, StepAdvice, StepProofContext, StepProverM, WrapSchnorrStepIOVal, computeStepIvpTranscript, convertUnfinalized, runStepProverM, wrapEndo, zkRows)
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
    -- Index-based lookup closes over the SRS and lets the wrap circuit's
    -- x_hat walk fetch bases on demand — matches OCaml
    -- `step_verifier.ml`'s `lagrange_commitment srs i` closure and removes
    -- the need to pre-size a `numPublic` buffer. Must use the step proof's
    -- own domain log2 (`ctx.domainLog2`) so the Lagrange basis matches the
    -- domain the step proof was committed in.
    lagrangeAt = mkConstLagrangeBaseLookup \i ->
      (coerce (ProofFFI.pallasSrsLagrangeCommitmentAt lagrangeSrs ctx.domainLog2 i)) :: AffinePoint (F WrapField)
    blindingH = (coerce $ ProofFFI.pallasSrsBlindingGenerator lagrangeSrs) :: AffinePoint (F WrapField)
  in
    { stepWidths: 1 :< Vector.nil
    , domainLog2s: ctx.domainLog2 :< Vector.nil
    , stepKeys: stepVkForCircuit (extractStepVKComms ctx) :< Vector.nil
    , lagrangeAt
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
-- Padded step proof creator (67-field public input)
--
-- Mirrors OCaml's pickles.ml:647 which compiles the step circuit with
-- `Max_proofs_verified = N2` so the step proof has Padded_length proofs
-- worth of public input fields (1 real + 1 dummy, 67 total for n=1).
--------------------------------------------------------------------------------

-- | Inline simple chain rule: verifies that `appState = prev + 1` or appState = 0.
-- | For the base case where appState = 0, the rule allocates prev = 0 and accepts.
paddedSimpleChainRule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m (RuleOutput 1 StepField)
paddedSimpleChainRule appState = do
  prev <- exists $ MT.lift $ pure (F zero :: F StepField)
  isBaseCase <- equals_ (const_ zero) appState
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: proofMustVerify :< Vector.nil
    }

-- | Create a padded step proof with 67-field public input, matching
-- | OCaml's production Pickles step compilation (Max_proofs_verified = N2).
-- | Uses stepMainPadded @1 with a trivial simple-chain rule, solved with
-- | StepProverM + a self-consistent advice whose `publicUnfinalizedProofs`
-- | plonk/digest are derived from a pure-PS replay of the step circuit's
-- | IVP sponge transcript, so `ivp_assert_plonk_*` holds during proving.
createPaddedStepProofContext :: Aff StepProofContext
createPaddedStepProofContext = do
  -- Lagrange SRS for IVP public input commitment (mislabeled types: takes CRS PallasG)
  lagrangeSrs <- liftEffect PallasImpl.createCRS
  -- Proof CRS for step proof creation (VestaG curve)
  proofCrs <- liftEffect $ createCRS @StepField
  let
    -- Step (FOP) domain log2 = 16 (OCaml dump_circuit_impl.ml:3723 step_domains).
    fopDomainLog2 = 16
    -- Lagrange basis domain log2: the wrap proof domain (14 for N1).
    wrapDomainLog2 = 14
    -- Lookup closure: fetches lagrange commitments by index on demand from
    -- the cached Pallas SRS. Matches OCaml `step_verifier.ml:360-368`'s
    -- `lagrange_commitment ~domain srs i` closure shape, so callers never
    -- need to decide a `numPublic` count.
    stepSrsData =
      { lagrangeAt:
          mkConstLagrangeBaseLookup \i ->
            (coerce (ProofFFI.vestaSrsLagrangeCommitmentAt lagrangeSrs wrapDomainLog2 i))
              :: AffinePoint (F StepField)
      , blindingH: (coerce $ ProofFFI.vestaSrsBlindingGenerator lagrangeSrs) :: AffinePoint (F StepField)
      , fopDomainLog2
      }
    dummyWrapSgStep :: AffinePoint StepField
    dummyWrapSgStep = { x: zero, y: zero }

    -- Build the advice that will drive the step solver. Starts from the
    -- pure-dummy `dummyStepAdvice` and overrides
    -- `publicUnfinalizedProofs[0]`'s plonk challenges and sponge digest
    -- with values obtained by replaying the step circuit's IVP sponge
    -- transcript in pure PS over the exact inputs the circuit will see.
    --
    -- The step circuit uses `advice.fopProofStates[i]` (Type1) to build
    -- the in-circuit wrap statement that's committed to x_hat, and
    -- `advice.publicUnfinalizedProofs[i]` (Type2) for the IVP sponge
    -- assertion. Those two fields are independent, so patching only the
    -- Type2 side to match the transcript keeps packStatement stable.
    advice =
      let
        advice0 = dummyStepAdvice
        fopState0 = Vector.index advice0.fopProofStates (unsafeFinite @1 0)
        fopDv = fopState0.deferredValues
        fopP = fopDv.plonk
        -- The step circuit supplies its FopProofState `combinedInnerProduct`,
        -- `b`, `perm`, `zetaToSrsLength`, `zetaToDomainSize` fields as raw
        -- field elements (bare `f`, not `Type1 f`) via
        -- `fromShifted dv.<field>` in `StepProverM.getStepPerProofWitnesses`
        -- (`TestContext.purs:282-286`). `allocatePerProofWitness` then wraps
        -- those raw scalars in `Type1` before `packStatement`, so the Vec5
        -- of shifted scalars that `publicInputCommit` sees holds the
        -- unshifted (2·t + c) value, not the advice's Type1-wrapped t.
        unshiftT1 :: Type1 (F StepField) -> F StepField
        unshiftT1 = fromShifted
        -- `Branch_data.pack` (composition_types.ml:201) packs as
        -- `4 * domain_log2 + mask[0] + 2 * mask[1]`. The step prover's
        -- `getStepPerProofWitnesses` hardcodes `mask0=false, mask1=true,
        -- domainLog2=16`, so the circuit packs this value as
        -- `4*16 + 0 + 2*1 = 66`. We mirror it here so the x_hat input
        -- the pure transcript commits to matches what the circuit packs.
        branchMask0 :: Int
        branchMask0 = 0
        branchMask1 :: Int
        branchMask1 = 1
        branchDomainLog2 :: Int
        branchDomainLog2 = 16
        dummyBranchData :: SizedF 10 (F StepField)
        dummyBranchData = SizedF.wrapF $ unsafePartial $ fromJust
          $ SizedF.fromField @10
            ( fromInt (4 * branchDomainLog2 + branchMask0 + 2 * branchMask1)
                :: StepField
            )

        VerificationKey vkRec = advice0.wrapVerifierIndex
        unwrapVkF (WeierstrassAffinePoint pt) = pt
        sigma7F = map unwrapVkF vkRec.sigma

        -- Drop the `F` wrapper on curve-point coordinates so the advice's
        -- `AffinePoint (F StepField)` becomes `AffinePoint StepField` —
        -- the plain shape `hashMessagesForNextStepProofPure` consumes.
        unwrapFpt :: AffinePoint (F StepField) -> AffinePoint StepField
        unwrapFpt = coerce

        sigma7 :: Vector 7 (AffinePoint StepField)
        sigma7 = map unwrapFpt sigma7F

        -- Reshape the advice's VK commitments into `StepVK StepField`
        -- (bare, not `F`-wrapped). The 6 index commitments correspond to
        -- generic/psm/complete_add/mul/emul/endomul_scalar in that order.
        stepVkFromAdvice :: StepVK StepField
        stepVkFromAdvice =
          let
            coeff15 = map (unwrapFpt <<< unwrapVkF) vkRec.coeff
            idx6 = map (unwrapFpt <<< unwrapVkF) vkRec.index
            at i = Vector.index idx6 (unsafeFinite @6 i)
          in
            { sigmaComm: sigma7
            , coefficientsComm: coeff15
            , genericComm: at 0
            , psmComm: at 1
            , completeAddComm: at 2
            , mulComm: at 3
            , emulComm: at 4
            , endomulScalarComm: at 5
            }

        -- Expanded step IPA challenges for the one "real" slot. For
        -- `dummyStepAdvice` these are `map F dummyIpaChallenges.stepExpanded`.
        expandedStepChals :: Vector StepIPARounds StepField
        expandedStepChals =
          map (\(F x) -> x)
            (Vector.index advice0.prevChallenges (unsafeFinite @1 0))

        realPrevSg :: AffinePoint StepField
        realPrevSg = unwrapFpt
          (Vector.index advice0.sgOld (unsafeFinite @1 0) :: AffinePoint (F StepField))

        -- Pure analog of `hashMessagesForNextStepProofOpt` (step_main.ml
        -- `Step_verifier.hash_messages_for_next_step_proof_opt`). For a
        -- base case where `proofMask = [true]` the opt_sponge is
        -- equivalent to a regular sponge absorbing the one real proof,
        -- matching `hashMessagesForNextStepProofPure`.
        msgStep :: StepField
        msgStep = hashMessagesForNextStepProofPure
          { stepVk: stepVkFromAdvice
          , appState: [ zero :: StepField ]
          , proofs:
              ( { sg: realPrevSg
                , expandedBpChallenges: expandedStepChals
                }
              ) :< Vector.nil
          }
        -- `WrapStatementPublicInput` is the same nested-Tuple shape as
        -- `packStatement`'s return, so both the legacy and new step
        -- circuits commit x_hat over values in this layout.
        dummyPublicInput :: WrapStatementPublicInput StepIPARounds (F StepField)
        dummyPublicInput = Tuple
          ( unshiftT1 fopDv.combinedInnerProduct
              :< unshiftT1 fopDv.b
              :< unshiftT1 fopP.zetaToSrsLength
              :< unshiftT1 fopP.zetaToDomainSize
              :< unshiftT1 fopP.perm
              :< Vector.nil
          )
          ( Tuple (fopP.beta :< fopP.gamma :< Vector.nil)
              ( Tuple (fopP.alpha :< fopP.zeta :< fopDv.xi :< Vector.nil)
                  ( Tuple
                      -- [sponge_digest, msg_for_next_wrap, msg_for_next_step]
                      -- mirroring packStatement (Verify.purs:357). msgWrap
                      -- comes from advice (all-zero in the dummy); msgStep
                      -- is the Poseidon hash computed above.
                      ( fopState0.spongeDigestBeforeEvaluations
                          :< Vector.index advice0.messagesForNextWrapProof (unsafeFinite @1 0)
                          :< F msgStep
                          :< Vector.nil
                      )
                      (Tuple fopDv.bulletproofChallenges dummyBranchData)
                  )
              )
          )
        -- The step circuit pads `advice.sgOld` (length n=1) to
        -- `Wrap_hack.Padded_length.n = 2` by prepending `dummyWrapSgStep`
        -- at the front (see `stepMain.purs:283-293`). Replicate exactly
        -- that for the transcript so the pure sponge absorbs the same
        -- two points.
        sgOldPadded :: Vector 2 (AffinePoint StepField)
        sgOldPadded = dummyWrapSgStep :< realPrevSg :< Vector.nil
        transcript = computeStepIvpTranscript
          { vk:
              { sigma: Vector.take @6 sigma7F
              , sigmaLast: Vector.last sigma7F
              , coeff: map unwrapVkF vkRec.coeff
              , index: map unwrapVkF vkRec.index
              }
          , sgOld: sgOldPadded
          , publicInput: dummyPublicInput
          , wComm: (Vector.index advice0.messages (unsafeFinite @1 0)).wComm
          , zComm: (Vector.index advice0.messages (unsafeFinite @1 0)).zComm
          , tComm: (Vector.index advice0.messages (unsafeFinite @1 0)).tComm
          , lagrangeAt: stepSrsData.lagrangeAt
          , blindingH: stepSrsData.blindingH
          }
        origPUP = Vector.index advice0.publicUnfinalizedProofs (unsafeFinite @1 0)
        PerProofUnfinalized origPUPr = origPUP
        patchedPUP = PerProofUnfinalized $ origPUPr
          { beta = UnChecked (SizedF.wrapF transcript.beta)
          , gamma = UnChecked (SizedF.wrapF transcript.gamma)
          , alpha = UnChecked (SizedF.wrapF transcript.alphaChal)
          , zeta = UnChecked (SizedF.wrapF transcript.zetaChal)
          , spongeDigest = F transcript.digest
          }
      in
        advice0 { publicUnfinalizedProofs = patchedPUP :< Vector.nil }

    circuit
      :: forall t m
       . CircuitM StepField (KimchiConstraint StepField) t m
      => StepWitnessM 1 StepIPARounds WrapIPARounds PallasG StepField m
      => Unit
      -> Snarky (KimchiConstraint StepField) t m (Vector 67 (FVar StepField))
    circuit _ = stepMainPadded @1 @1 @34 paddedSimpleChainRule stepSrsData dummyWrapSgStep

  builtState :: CircuitBuilderState (KimchiGate StepField) (AuxState StepField)
    <- liftEffect $ compile
      (Proxy @Unit)
      (Proxy @(Vector 67 (F StepField)))
      (Proxy @(KimchiConstraint StepField))
      circuit
      (Kimchi.initialState :: CircuitBuilderState (KimchiGate StepField) (AuxState StepField))

  let
    solverCircuit
      :: forall t
       . CircuitM StepField (KimchiConstraint StepField) t (StepProverM 1 StepIPARounds WrapIPARounds StepField)
      => Unit
      -> Snarky (KimchiConstraint StepField) t (StepProverM 1 StepIPARounds WrapIPARounds StepField) (Vector 67 (FVar StepField))
    solverCircuit = circuit

    rawSolver
      :: SolverT StepField (KimchiConstraint StepField)
           (StepProverM 1 StepIPARounds WrapIPARounds StepField)
           Unit
           (Vector 67 (F StepField))
    rawSolver = makeSolver'
      (emptyProverState { debug = true })
      (Proxy @(KimchiConstraint StepField))
      solverCircuit

  eRes <- liftEffect $ runStepProverM advice (runSolverT rawSolver unit)
  case eRes of
    Left e -> liftEffect $ Exc.throw ("Padded step solver: " <> show e)
    Right (Tuple _ assignments) -> do
      let
        kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
        { constraintSystem, constraints } = makeConstraintSystem @StepField
          { constraints: kimchiRows
          , publicInputs: builtState.publicInputs
          , unionFind: (un AuxState builtState.aux).wireState.unionFind
          }
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables constraints
          , publicInputs: builtState.publicInputs
          }
        endo = let EndoBase e = endoBase @StepField @WrapField in e
        proverIndex = createProverIndex @StepField @VestaG { endo, constraintSystem, crs: proofCrs }
        verifierIndex = createVerifierIndex @StepField @VestaG proverIndex
        proof = createProof { proverIndex, witness }
        oracles = proofOracles verifierIndex { proof, publicInput: publicInputs }
        domainLog2 = proverIndexDomainLog2 proverIndex
      pure { proverIndex, verifierIndex, witness, publicInputs, domainLog2, proof, oracles }

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

  -- Diagnostic: check padded step public input has exactly 67 fields
  it "L3.5a: padded step public input field count matches wrap circuit's packed statement" \_ -> do
    paddedStep <- createPaddedStepProofContext
    let
      nStepFields = Array.length paddedStep.publicInputs
      nPackedFields = sizeInFields (Proxy :: Proxy WrapField)
        (Proxy :: Proxy (Pickles.PackedStatement.PackedStepPublicInput 2 WrapIPARounds (F WrapField) Boolean))
    liftEffect $ when (nStepFields /= nPackedFields) $
      Exc.throw $ "Field count mismatch: padded step=" <> show nStepFields <> " wrap packed=" <> show nPackedFields

  -- Diagnostic: check index digest matches FFI
  it "L3.5b: step VK index digest matches FFI" \{ step0 } -> do
    let
      comms = extractStepVKComms step0
      -- Hash in IVP order: sigma(6), sigmaLast, coeff(15), index(6)
      sigma6 = Vector.take @6 comms.sigmaComm
      sigmaLast = Vector.index comms.sigmaComm (unsafeFinite @7 6)
      pts = (Vector.toUnfoldable sigma6 :: Array _)
        <> [sigmaLast]
        <> (Vector.toUnfoldable comms.coefficientsComm :: Array _)
        <> [ comms.genericComm, comms.psmComm, comms.completeAddComm
           , comms.mulComm, comms.emulComm, comms.endomulScalarComm ]
      -- Hash via Poseidon sponge (same as IVP does)
      digest = Pickles.Sponge.evalPureSpongeM
        (RandomOracle.Sponge.create (RandomOracle.Sponge.initialState :: Vector 3 WrapField))
        do
          for_ pts \pt -> do
            Pickles.Sponge.absorb pt.x
            Pickles.Sponge.absorb pt.y
          Pickles.Sponge.squeeze
      -- Compare with FFI digest
      ffiDigest = ProofFFI.pallasVerifierIndexDigest step0.verifierIndex
    -- Cross-field: ffiDigest is Fp-typed but should be the same integer as our Fq digest
    liftEffect $ when (toBigInt digest /= toBigInt ffiDigest) $
      Exc.throw $ "Index digest mismatch: PS=" <> show (toBigInt digest) <> " FFI=" <> show (toBigInt ffiDigest)

  -- Layer 4: real everything + verify the wrap proof.
  -- Uses a PADDED step proof (67 public input fields) from stepMainPadded,
  -- matching OCaml's Pickles.compile which hardcodes Max_proofs_verified = N2.
  -- The shared `step0` from createInductiveTestContext has only 34 fields
  -- (legacy stepCircuit, n=1) which is incompatible with the wrap circuit's IVP.
  it "L4: wrap proof verifies" \_ -> do
    paddedStep <- createPaddedStepProofContext
    let
      deferredOutput = wrapComputeDeferredValues (buildDeferredValuesInput paddedStep)
      stepDigest = computeStepDigest paddedStep
      wrapDigest = computeWrapDigest paddedStep
      publicInput = assembleWrapMainInput
        { deferredValues: deferredOutput
        , messagesForNextStepProofDigest: stepDigest
        , messagesForNextWrapProofDigest: wrapDigest
        }
      advice = buildWrapAdvice (buildRealAdvice paddedStep)
      proofCrs = PallasImpl.pallasCrsCreate (2 `Int.pow` 16)
      ctx :: WrapProveContext 1 1 1
      ctx =
        { wrapMainConfig: buildWrapMainConfig paddedStep
        , crs: proofCrs
        , publicInput
        , advice
        }
    result <- liftEffect $ wrapProve (\e -> Exc.throw (show e)) ctx
    let proofVerified = ProofFFI.verifyOpeningProof result.verifierIndex
          { proof: result.proof, publicInput: result.publicInputs }
    liftEffect $ when (not proofVerified) $ Exc.throw "Wrap proof failed to verify"
