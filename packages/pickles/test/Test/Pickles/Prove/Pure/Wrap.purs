-- | Level 1 smoke test for `Pickles.Prove.Pure.Wrap.wrapComputeDeferredValues`.
-- |
-- | Mirrors the smoke-test pattern from `Test.Pickles.Prove.Pure.Step`:
-- | feed the function a mix of real FFI-sourced step-proof data (from
-- | `step0 :: StepProofContext`) and dummy zeros for the fields the
-- | smoke test doesn't care about, then force every output field by
-- | pattern-matching into unused bindings.
-- |
-- | Bugs it catches:
-- |
-- | * The `Vector.toVector @StepIPARounds` length assertion on the
-- |   opening prechallenges (= kimchi's `opening_prechallenges`). If
-- |   the IPA rounds count drifts from the PS type-level constant, the
-- |   test crashes at the exact line.
-- | * FFI glue bugs (`pallasProofOracles` with a non-empty
-- |   `prevChallenges` list, `pallasProofOpeningPrechallenges`, etc.)
-- |   where a JS wrapper hands back `undefined` for a field that PS
-- |   then accesses.
-- | * Missing typeclass instances the compiler lets through but that
-- |   bomb at runtime (we rely on `PrimeField` / `PoseidonField` /
-- |   `HasEndo` / `Shifted` dispatch for the step field inside
-- |   `Common.derivePlonk` / `Common.ftEval0`).
-- |
-- | Silent on semantic correctness. `prevChallenges` are empty
-- | (`n = 0`), so `combined_inner_product` and `ft_eval0` do not
-- | match any OCaml fixture. Tracking that against a real fixture
-- | is follow-up work.
module Test.Pickles.Prove.Pure.Wrap
  ( spec
  ) where

import Prelude

import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI (OraclesResult, Proof, proofCoefficientEvals, proofIndexEvals, proofSigmaEvals, proofWitnessEvals, proofZEvals)
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, WrapDeferredValuesOutput, assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure)
import Pickles.Types (StepField, WrapField, WrapStatementPacked(..))
import Pickles.VerificationKey (StepVK)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Snarky.Curves.Class (EndoScalar(..), endoScalar)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.TestContext (InductiveTestContext, StepProofContext)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Build `AllEvals StepField` for a real step proof.
realStepAllEvals
  :: Proof Vesta.G StepField
  -> OraclesResult StepField
  -> AllEvals StepField
realStepAllEvals proof oracles =
  { ftEval1: oracles.ftEval1
  , publicEvals:
      { zeta: oracles.publicEvalZeta
      , omegaTimesZeta: oracles.publicEvalZetaOmega
      }
  , zEvals: proofZEvals proof
  , witnessEvals: proofWitnessEvals proof
  , coeffEvals: proofCoefficientEvals proof
  , sigmaEvals: proofSigmaEvals proof
  , indexEvals: proofIndexEvals proof
  }

stepEndoScalar :: StepField
stepEndoScalar =
  let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

zeroAffine :: forall f. Semiring f => AffinePoint f
zeroAffine = { x: zero, y: zero }

-- | Minimal zero `StepVK` for the hash smoke test. All commitments
-- | collapse to (0, 0). Semantic correctness is not the point — we
-- | only want `hashMessagesForNextStepProofPure` to traverse the full
-- | serialization path.
zeroStepVk :: StepVK StepField
zeroStepVk =
  { sigmaComm: Vector.replicate zeroAffine
  , coefficientsComm: Vector.replicate zeroAffine
  , genericComm: zeroAffine
  , psmComm: zeroAffine
  , completeAddComm: zeroAffine
  , mulComm: zeroAffine
  , emulComm: zeroAffine
  , endomulScalarComm: zeroAffine
  }

--------------------------------------------------------------------------------
-- Build the full WrapDeferredValuesInput from a StepProofContext
--------------------------------------------------------------------------------

-- | Build smoke-test input with `n = 0` previous proofs. No prev sgs,
-- | no prev bp challenges — matches `actual_proofs_verified = N0`.
buildSmokeInput :: StepProofContext -> WrapDeferredValuesInput 0
buildSmokeInput ctx =
  let
    emptyPrevSgs :: Vector 0 { x :: WrapField, y :: WrapField }
    emptyPrevSgs = Vector.nil

    emptyPrevChallenges :: Vector 0 (Vector _ StepField)
    emptyPrevChallenges = Vector.nil

    proofsVerifiedMask :: Vector 2 Boolean
    proofsVerifiedMask = Vector.replicate false
  in
    { proof: ctx.proof
    , verifierIndex: ctx.verifierIndex
    , publicInput: ctx.publicInputs

    , allEvals: realStepAllEvals ctx.proof ctx.oracles
    , pEval0Chunks: [ ctx.oracles.publicEvalZeta ]

    , domainLog2: ctx.domainLog2
    , zkRows: 3
    , srsLengthLog2: 16
    , generator: domainGenerator ctx.domainLog2
    , shifts: domainShifts ctx.domainLog2
    , vanishesOnZk: one
    , omegaForLagrange: \_ -> one

    , endo: stepEndoScalar
    , linearizationPoly: Linearization.pallas

    , prevSgs: emptyPrevSgs
    , prevChallenges: emptyPrevChallenges

    , proofsVerifiedMask
    }

--------------------------------------------------------------------------------
-- Spec
--------------------------------------------------------------------------------

spec :: SpecT Aff InductiveTestContext Aff Unit
spec = describe "Pickles.Prove.Pure.Wrap" do
  describe "wrapComputeDeferredValues" do
    it "base case: evaluates every output field on real step-proof FFI data" \{ step0 } -> do
      let
        input :: WrapDeferredValuesInput 0
        input = buildSmokeInput step0

        output :: WrapDeferredValuesOutput
        output = wrapComputeDeferredValues input

      -- Cheap equality to drag `spongeDigestBeforeEvaluations` through
      -- evaluation (it comes straight from the oracle result).
      output.spongeDigestBeforeEvaluations `shouldEqual` step0.oracles.fqDigest

      -- Force the remaining output fields by pattern-matching them
      -- into unused bindings. Any thunk that crashes when forced (the
      -- `Vector.toVector @StepIPARounds` length assertion on opening
      -- prechallenges, FFI `undefined` dereferences, missing typeclass
      -- instances) will surface here.
      let
        _plonk = output.plonk
        _cip = output.combinedInnerProduct
        _xi = output.xi
        _bpChals = output.bulletproofPrechallenges
        _b = output.b
        _branchData = output.branchData
        _xHat = output.xHatEvals
        _oracles = output.oracles
        _newBp = output.newBulletproofChallenges
      pure unit

  describe "assembleWrapMainInput" do
    it "base case: packs deferred values + digests into WrapStatementPacked" \{ step0 } -> do
      let
        deferredInput :: WrapDeferredValuesInput 0
        deferredInput = buildSmokeInput step0

        deferredOutput :: WrapDeferredValuesOutput
        deferredOutput = wrapComputeDeferredValues deferredInput

        -- Step-field digest of the (empty-prev) messages_for_next_step_proof.
        -- Uses the real `hashMessagesForNextStepProofPure` code path with
        -- zero-valued step VK + empty app_state + no prev proofs.
        stepDigest :: StepField
        stepDigest = hashMessagesForNextStepProofPure
          { stepVk: zeroStepVk
          , appState: []
          , proofs: (Vector.nil :: Vector 0 { sg :: AffinePoint StepField, expandedBpChallenges :: Vector 0 StepField })
          }

        -- Wrap-field digest of the (empty-padded) messages_for_next_wrap_proof.
        -- `paddedChallenges` of length 0 collapses to hashing just `sg`.
        wrapDigest :: WrapField
        wrapDigest = hashMessagesForNextWrapProofPureGeneral
          { sg: (zeroAffine :: AffinePoint WrapField)
          , paddedChallenges: (Vector.nil :: Vector 0 (Vector 0 WrapField))
          }

        packed = assembleWrapMainInput
          { deferredValues: deferredOutput
          , messagesForNextStepProofDigest: stepDigest
          , messagesForNextWrapProofDigest: wrapDigest
          }

        WrapStatementPacked r = packed

      -- Force every field of the packed statement by pattern-matching
      -- into unused bindings. Cross-field `toShifted` / `fromShifted`
      -- / `coerceViaBits` / `fromBigInt (toBigInt ...)` all fire
      -- through the projections below.
      let
        _fpFields = r.fpFields
        _challenges = r.challenges
        _scalarChallenges = r.scalarChallenges
        _digests = r.digests
        _bpChalsPacked = r.bulletproofChallenges
        _branchData = r.branchData
        _featureFlags = r.featureFlags
        _lookupFlag = r.lookupOptFlag
        _lookupSc = r.lookupOptScalarChallenge
      pure unit
