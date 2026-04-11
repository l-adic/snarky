-- | Level 1 smoke test for `Pickles.Prove.Pure.Step.expandProof`.
-- |
-- | This test does NOT verify cryptographic correctness. It feeds
-- | `expandProof` a mix of real FFI-sourced wrap-proof data (from the
-- | shared `wrap0 :: WrapProofContext`) and dummy zeros for the
-- | step-side / purely-computational fields, then forces every
-- | output field of the result.
-- |
-- | The specific bugs it catches:
-- |
-- | * The three `unsafePartial $ fromJust $ Vector.toVector @N arr`
-- |   length assertions inside `expandProof` — Phase 5 opening
-- |   prechallenges at `WrapIPARounds`, Phase 8 `tComm` at 7, Phase 8
-- |   opening `lr` at `WrapIPARounds`. If any of these drift from
-- |   what kimchi actually produces, the test crashes at the exact
-- |   line.
-- | * FFI glue bugs where a JS wrapper hands back `undefined` for a
-- |   field that PS then accesses.
-- | * Missing typeclass instances the compiler lets through but that
-- |   bomb at runtime (we rely on `PrimeField` / `PoseidonField` /
-- |   `HasEndo` / `Shifted` dispatch across both step and wrap fields
-- |   inside `Common.derivePlonk` and `Common.ftEval0`).
-- |
-- | The test is silent on semantic correctness. For that we'd need
-- | an OCaml fixture (Level 2) or a full step-prover round-trip
-- | (Level 3); both are follow-ups.
module Test.Pickles.Prove.Pure.Step
  ( spec
  ) where

import Prelude

import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Pickles.Dummy (roComputeResult)
import Pickles.Linearization (pallas, vesta) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI (OraclesResult, Proof, proofCoefficientEvals, proofSigmaEvals, proofWitnessEvals, proofZEvals)
import Pickles.Prove.Pure.Step (ExpandProofInput, ExpandProofOutput, expandProof)
import Pickles.Types (PointEval(..), StepAllEvals(..), StepField, StepIPARounds, WrapField, WrapIPARounds)
import Pickles.Verify.Types (BranchData, PlonkMinimal)
import Pickles.VerificationKey (StepVK)
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Curves.Class (EndoScalar(..), endoScalar)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.TestContext (InductiveTestContext, WrapProofContext)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

--------------------------------------------------------------------------------
-- Dummy-value helpers (zeros / identity elements for non-FFI fields)
--------------------------------------------------------------------------------

zeroAffine :: forall f. Semiring f => AffinePoint f
zeroAffine = { x: zero, y: zero }

zeroBareEval :: forall f. Semiring f => { zeta :: f, omegaTimesZeta :: f }
zeroBareEval = { zeta: zero, omegaTimesZeta: zero }

-- | All-zero `AllEvals` (used for step-side data the smoke test
-- | doesn't care about — downstream of `expandDeferred`'s pure arith).
zeroAllEvals :: forall f. Semiring f => AllEvals f
zeroAllEvals =
  { ftEval1: zero
  , publicEvals: zeroBareEval
  , zEvals: zeroBareEval
  , indexEvals: Vector.replicate zeroBareEval
  , witnessEvals: Vector.replicate zeroBareEval
  , coeffEvals: Vector.replicate zeroBareEval
  , sigmaEvals: Vector.replicate zeroBareEval
  }

zeroPlonkMinimal :: PlonkMinimal (F StepField)
zeroPlonkMinimal =
  { alpha: unsafePartial (SizedF.unsafeFromField (F zero))
  , beta: unsafePartial (SizedF.unsafeFromField (F zero))
  , gamma: unsafePartial (SizedF.unsafeFromField (F zero))
  , zeta: unsafePartial (SizedF.unsafeFromField (F zero))
  }

zeroBranchData :: BranchData StepField Boolean
zeroBranchData =
  { domainLog2: zero
  , proofsVerifiedMask: false :< false :< Vector.nil
  }

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

stepEndoScalar :: StepField
stepEndoScalar =
  let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

wrapEndoScalar :: WrapField
wrapEndoScalar =
  let EndoScalar e = (endoScalar :: EndoScalar WrapField) in e

-- | Zero `StepAllEvals (F StepField)` for the `stepProofPrevEvals`
-- | field (the wrap proof's embedded step-proof evals in OCaml).
-- | Note: `StepAllEvals` uses the `Pickles.Types.PointEval` newtype,
-- | not the bare-record `Pickles.Linearization.FFI.PointEval` that
-- | `AllEvals` uses — different types.
zeroStepPrevEvals :: StepAllEvals (F StepField)
zeroStepPrevEvals =
  let
    ev :: PointEval (F StepField)
    ev = PointEval { zeta: F zero, omegaTimesZeta: F zero }
  in
    StepAllEvals
      { publicEvals: ev
      , witnessEvals: Vector.replicate ev
      , coeffEvals: Vector.replicate ev
      , zEvals: ev
      , sigmaEvals: Vector.replicate ev
      , indexEvals: Vector.replicate ev
      , ftEval1: F zero
      }

--------------------------------------------------------------------------------
-- Real wrap-proof evals (via vestaProof* FFI getters)
--------------------------------------------------------------------------------

-- | Build an `AllEvals WrapField` from a real wrap proof + its
-- | oracles. `indexEvals` are left as zeros because the FFI doesn't
-- | surface them as a direct getter; they feed only pure PS code in
-- | `expandProof`, so zero values don't mask a length assertion.
realWrapAllEvals
  :: Proof Pallas.G WrapField
  -> OraclesResult WrapField
  -> AllEvals WrapField
realWrapAllEvals proof oracles =
  { ftEval1: oracles.ftEval1
  , publicEvals:
      { zeta: oracles.publicEvalZeta
      , omegaTimesZeta: oracles.publicEvalZetaOmega
      }
  , zEvals: proofZEvals proof
  , witnessEvals: proofWitnessEvals proof
  , coeffEvals: proofCoefficientEvals proof
  , sigmaEvals: proofSigmaEvals proof
  , indexEvals: Vector.replicate zeroBareEval
  }

--------------------------------------------------------------------------------
-- Build the full ExpandProofInput from a WrapProofContext
--------------------------------------------------------------------------------

buildSmokeInput :: WrapProofContext -> ExpandProofInput 1 2
buildSmokeInput ctx =
  let
    -- Dummy step IPA challenges, wrapped in F for the Verify.Types shape.
    stepRawBp :: Vector StepIPARounds (SizedF 128 (F StepField))
    stepRawBp = map SizedF.wrapF roComputeResult.stepChalRaw

    oldStepPrev :: Vector 1 (Vector StepIPARounds (SizedF 128 (F StepField)))
    oldStepPrev = stepRawBp :< Vector.nil

    -- Wrap-side prev bp challenges, padded to Wrap_hack.Padded_length.n = 2.
    zeroWrapChalVec :: Vector WrapIPARounds WrapField
    zeroWrapChalVec = Vector.replicate zero

    wrapPadded :: Vector 2 (Vector WrapIPARounds WrapField)
    wrapPadded = zeroWrapChalVec :< zeroWrapChalVec :< Vector.nil

    stepPrevChalsValues :: Vector StepIPARounds (F StepField)
    stepPrevChalsValues = Vector.replicate (F zero)
  in
    { mustVerify: false

    -- Step-side `expandDeferred` inputs. All downstream of pure PS
    -- code, so zero values suffice.
    , zkRows: 3
    , srsLengthLog2: 15
    , allEvals: zeroAllEvals
    , pEval0Chunks: [ zero ]
    , oldBulletproofChallenges: oldStepPrev
    , plonkMinimal: zeroPlonkMinimal
    , rawBulletproofChallenges: stepRawBp
    , branchData: zeroBranchData
    , spongeDigestBeforeEvaluations: zero
    , stepDomainLog2: 15
    , stepGenerator: domainGenerator 15
    , stepShifts: domainShifts 15
    , stepVanishesOnZk: one
    , stepOmegaForLagrange: \_ -> one
    , endo: stepEndoScalar
    , linearizationPoly: Linearization.pallas

    -- Step-side hash inputs.
    , dlogIndex: zeroStepVk
    , appStateFields: []
    , stepPrevSgs: zeroAffine :< Vector.nil

    -- Wrap-side hash inputs.
    , wrapChallengePolynomialCommitment: zeroAffine
    , wrapPaddedPrevChallenges: wrapPadded

    -- Wrap-proof oracles (real FFI data).
    , wrapVerifierIndex: ctx.verifierIndex
    , wrapProof: ctx.proof
    , tockPublicInput: ctx.publicInputs

    -- Phase 5: new bp challenges + b (real wrap domain).
    , wrapDomainLog2: ctx.domainLog2
    , wrapEndo: wrapEndoScalar

    -- Phase 7: wrap-field Type2 deferred values.
    , wrapAllEvals: realWrapAllEvals ctx.proof ctx.oracles
    , wrapPEval0Chunks: [ ctx.oracles.publicEvalZeta ]
    , wrapShifts: domainShifts ctx.domainLog2
    , wrapZkRows: 3
    , wrapSrsLengthLog2: 15
    , wrapVanishesOnZk: one
    , wrapOmegaForLagrange: \_ -> one
    , wrapLinearizationPoly: Linearization.vesta

    -- Phase 8: perProofWitness extras.
    , stepProofPrevEvals: zeroStepPrevEvals
    , stepPrevChallenges: stepPrevChalsValues :< Vector.nil
    , stepPrevSgsPadded: zeroAffine :< Vector.nil
    }

--------------------------------------------------------------------------------
-- Spec
--------------------------------------------------------------------------------

spec :: SpecT Aff InductiveTestContext Aff Unit
spec = describe "Pickles.Prove.Pure.Step.expandProof" do
  it "base case: evaluates every output field on real wrap-proof FFI data" \{ wrap0 } -> do
    let
      input :: ExpandProofInput 1 2
      input = buildSmokeInput wrap0

      output :: ExpandProofOutput
      output = expandProof input

    -- Cheap equality to drag `actualWrapDomain` through evaluation.
    output.actualWrapDomain `shouldEqual` wrap0.domainLog2

    -- Force the remaining output fields by pattern-matching them
    -- into unused bindings. Any thunk that crashes when forced (the
    -- three `unsafePartial $ fromJust $ Vector.toVector @N` length
    -- assertions, FFI `undefined` dereferences, missing typeclass
    -- instances, etc.) will surface here.
    let
      _sg = output.sg
      _unfinalized = output.unfinalized
      _xHat = output.xHat
      _perProofWitness = output.perProofWitness
      _prevStmt = output.prevStatementWithHashes
      _oracles = output.oracles
      _newBp = output.newBulletproofChallenges
    pure unit
