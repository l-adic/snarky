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

import Data.Identity (Identity)
import Effect.Aff (Aff)
import Pickles.IPA as IPA
import Pickles.PlonkChecks.XiCorrect (emptyPrevChallengeDigest)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.Dummy (dummyFinalizeOtherProofParams, dummyProofWitness, dummyUnfinalizedProof)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofInput, finalizeOtherProofCircuit)
import Pickles.Types (StepField, WrapField, WrapIPARounds)
import Record as Record
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, assert_)
import Snarky.Circuit.Kimchi (Type2)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Test.Pickles.TestContext (InductiveTestContext, buildStepFinalizeInput, buildStepFinalizeParams)
import Test.Snarky.Circuit.Utils (TestConfig, circuitTestInputs', satisfied_)
import Test.Spec (Spec, SpecT, describe, it)

kimchiTestConfig :: forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)
kimchiTestConfig = { checker: eval, postCondition: Kimchi.postCondition, initState: Kimchi.initialState }

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Value type for test input (Step-side finalize: verifying Wrap proof → d = WrapIPARounds)
type FinalizeOtherProofTestInput =
  FinalizeOtherProofInput WrapIPARounds (F StepField) (Type2 (F StepField) Boolean) Boolean

-- | Variable type for circuit
type FinalizeOtherProofTestInputVar =
  FinalizeOtherProofInput WrapIPARounds (FVar StepField) (Type2 (FVar StepField) (BoolVar StepField)) (BoolVar StepField)

-------------------------------------------------------------------------------
-- | Tests
-------------------------------------------------------------------------------

spec :: Spec Unit
spec = describe "Pickles.Step.FinalizeOtherProof" do
  it "skeleton circuit is satisfiable with dummy inputs (base case)" do
    let
      input :: FinalizeOtherProofTestInput
      input =
        { unfinalized: dummyUnfinalizedProof @WrapIPARounds @StepField @WrapField @(Type2 (F StepField) Boolean)
        , witness: dummyProofWitness
        , prevChallengeDigest: zero
        }

      dummyTestCircuit
        :: forall t
         . CircuitM StepField (KimchiConstraint StepField) t Identity
        => FinalizeOtherProofTestInputVar
        -> Snarky (KimchiConstraint StepField) t Identity Unit
      dummyTestCircuit x =
        let
          ops :: IPA.IpaScalarOps StepField t Identity (Type2 (FVar StepField) (BoolVar StepField))
          ops = IPA.type2ScalarOps
        in
          void $ evalSpongeM initialSpongeCircuit (finalizeOtherProofCircuit ops dummyFinalizeOtherProofParams x)

    void $ circuitTestInputs' @StepField
      (Record.merge kimchiTestConfig { testFunction: satisfied_ })
      [ input ]
      dummyTestCircuit

-------------------------------------------------------------------------------
-- | Real data test (All-checks with Wrap proof)
-------------------------------------------------------------------------------

realDataSpec :: SpecT Aff InductiveTestContext Aff Unit
realDataSpec =
  describe "Pickles.Step.FinalizeOtherProof (real data)" do
    it "all checks pass with real Wrap proof data" \{ wrap0 } -> do
      let
        params = buildStepFinalizeParams wrap0
        input = buildStepFinalizeInput { prevChallengeDigest: emptyPrevChallengeDigest, wrapCtx: wrap0 }
      let
        circuit
          :: forall t
           . CircuitM StepField (KimchiConstraint StepField) t Identity
          => FinalizeOtherProofTestInputVar
          -> Snarky (KimchiConstraint StepField) t Identity Unit
        circuit x = do
          let
            ops :: IPA.IpaScalarOps StepField t Identity (Type2 (FVar StepField) (BoolVar StepField))
            ops = IPA.type2ScalarOps
          { finalized } <- evalSpongeM initialSpongeCircuit (finalizeOtherProofCircuit ops params x)
          assert_ finalized

      void $ circuitTestInputs' @StepField
        (Record.merge kimchiTestConfig { testFunction: satisfied_ })
        [ input ]
        circuit
