module Test.Pickles.Step.FinalizeOtherProof
  ( spec
  , realDataSpec
  ) where

-- | Tests for the FinalizeOtherProof circuit.
-- |
-- | Two test scenarios:
-- | 1. Base case: dummy inputs with shouldFinalize = false (bootstrapping)
-- | 2. Real data: Schnorr proof data with shouldFinalize = true (all checks)
-- |
-- | STAGED: This test is set up to generate a real Wrap proof (Pallas)
-- | and verify it in the Step circuit (Vesta). The cross-field mappings
-- | are currently placeholders for implementation by an expert.

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Pickles.Dummy (dummyFinalizeOtherProofParams, dummyProofWitness, stepDummyFopProofState)
import Pickles.PlonkChecks.XiCorrect (emptyPrevChallengeDigest)
import Pickles.ShiftOps (FopShiftOps)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofInput, finalizeOtherProofCircuit)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Types (StepField, StepIPARounds)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, assert_)
import Snarky.Circuit.Kimchi (Type1)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Test.Pickles.TestContext (InductiveTestContext, buildStepFinalizeInput, buildStepFinalizeParams)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied_)
import Test.Spec (Spec, SpecT, describe, it)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Value type for test input (Step-side finalize: verifying Wrap proof → d = WrapIPARounds)
type FinalizeOtherProofTestInput =
  FinalizeOtherProofInput 0 StepIPARounds (F StepField) (Type1 (F StepField)) Boolean

-- | Variable type for circuit
type FinalizeOtherProofTestInputVar =
  FinalizeOtherProofInput 0 StepIPARounds (FVar StepField) (Type1 (FVar StepField)) (BoolVar StepField)

-------------------------------------------------------------------------------
-- | Tests
-------------------------------------------------------------------------------

spec
  :: TestConfig StepField (KimchiGate StepField) (AuxState StepField)
  -> Spec Unit
spec cfg = describe "Pickles.Step.FinalizeOtherProof" do
  it "skeleton circuit is satisfiable with dummy inputs (base case)" do
    let
      input :: FinalizeOtherProofTestInput
      input =
        { unfinalized: stepDummyFopProofState { proofsVerified: 2 }
        , witness: dummyProofWitness
        , mask: Vector.nil
        , prevChallenges: Vector.nil
        , domainLog2Var: zero
        }

      dummyTestCircuit
        :: forall t
         . CircuitM StepField (KimchiConstraint StepField) t Identity
        => FinalizeOtherProofTestInputVar
        -> Snarky (KimchiConstraint StepField) t Identity Unit
      dummyTestCircuit x =
        let
          ops :: FopShiftOps StepField t Identity (Type1 (FVar StepField))
          ops = StepOtherField.fopShiftOps
        in
          void $ finalizeOtherProofCircuit ops dummyFinalizeOtherProofParams x

    void $ circuitTest' @StepField
      cfg
      (NEA.singleton { testFunction: satisfied_, input: Exact (NEA.singleton input) })
      dummyTestCircuit

-------------------------------------------------------------------------------
-- | Real data test (All-checks with Wrap proof)
-------------------------------------------------------------------------------

realDataSpec :: TestConfig StepField (KimchiGate StepField) (AuxState StepField) -> SpecT Aff InductiveTestContext Aff Unit
realDataSpec cfg =
  describe "Pickles.Step.FinalizeOtherProof (real data)" do
    it "all checks pass with real Wrap proof data" \{ step0, wrap0 } -> do
      let
        params = buildStepFinalizeParams step0
        input = buildStepFinalizeInput { prevChallengeDigest: emptyPrevChallengeDigest, sgPointEvals: [], stepCtx: step0, wrapCtx: wrap0 }
      let
        circuit
          :: forall t
           . CircuitM StepField (KimchiConstraint StepField) t Identity
          => FinalizeOtherProofTestInputVar
          -> Snarky (KimchiConstraint StepField) t Identity Unit
        circuit x = do
          let
            ops :: FopShiftOps StepField t Identity (Type1 (FVar StepField))
            ops = StepOtherField.fopShiftOps
          r <- finalizeOtherProofCircuit ops params x
          assert_ r.cipCorrect

      void $ circuitTest' @StepField
        cfg
        (NEA.singleton { testFunction: satisfied_, input: Exact (NEA.singleton input) })
        circuit
