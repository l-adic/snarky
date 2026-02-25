module Test.Pickles.StepE2E
  ( spec
  ) where

-- | End-to-end test for the Step circuit with a real application circuit.
-- |
-- | This test embeds the Schnorr verification circuit as the application logic
-- | within the Step combinator. For the base case (Step0), we use dummy
-- | unfinalized proofs with `shouldFinalize = false`.
-- |
-- | This validates:
-- | 1. Step combinator correctly composes with a non-trivial application circuit
-- | 2. The bootstrapping assertion works with real circuit constraints
-- | 3. The full composed circuit is satisfiable

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Schnorr.Gen (genValidSignature)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Class (liftEffect)
import Pickles.IPA (type2ScalarOps)
import Pickles.Step.Advice (class StepWitnessM)
import Pickles.Step.Circuit (stepCircuit)
import Pickles.Step.Dummy (dummyFinalizeOtherProofParams)
import Pickles.Types (StepField, WrapIPARounds)
import Snarky.Circuit.DSL (class CircuitM, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Pasta (PallasG)
import Test.Pickles.TestContext (StepAdvice, StepProverM, StepSchnorrInput, StepSchnorrInputVar, dummyStepAdvice, genDummyUnfinalizedProof, runStepProverM, stepSchnorrAppCircuit)
import Test.QuickCheck.Gen (Gen, randomSampleOne)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTestM', satisfied_)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Test Circuit
-------------------------------------------------------------------------------

-- | The composed Step circuit with Schnorr as application logic (base case).
stepSchnorrCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepWitnessM 1 WrapIPARounds m StepField
  => StepSchnorrInputVar
  -> Snarky (KimchiConstraint StepField) t m Unit
stepSchnorrCircuit input = do
  _ <- stepCircuit type2ScalarOps dummyFinalizeOtherProofParams (stepSchnorrAppCircuit false) input
  pure unit

-------------------------------------------------------------------------------
-- | Generator for valid Step+Schnorr inputs
-------------------------------------------------------------------------------

genStepSchnorrInput :: Gen StepSchnorrInput
genStepSchnorrInput = do
  schnorrInput <- genValidSignature (Proxy @PallasG) (Proxy @4)
  unfinalizedProof <- genDummyUnfinalizedProof
  pure
    { appInput: schnorrInput
    , previousProofInputs: unit :< Vector.nil
    , unfinalizedProofs: unfinalizedProof :< Vector.nil
    , prevChallengeDigests: zero :< Vector.nil
    }

-- | Generate random advice paired with the solver wrapper.
-- | Each test input needs its own random advice to avoid VarBaseMul collisions.
genStepSchnorrAdvice :: Gen (StepAdvice 1 WrapIPARounds StepField)
genStepSchnorrAdvice = dummyStepAdvice

spec
  :: TestConfig StepField (KimchiGate StepField) (AuxState StepField)
  -> Spec Unit
spec cfg = describe "Step E2E with Schnorr" do
  it "Step circuit with Schnorr application is satisfiable (base case)" do
    advice <- liftEffect $ randomSampleOne genStepSchnorrAdvice

    void $ circuitTestM' @StepField (runStepProverM advice)
      cfg
      (NEA.singleton { testFunction: satisfied_, input: QuickCheck 10 genStepSchnorrInput })
      (stepSchnorrCircuit :: forall t. CircuitM StepField (KimchiConstraint StepField) t (StepProverM 1 WrapIPARounds StepField) => StepSchnorrInputVar -> Snarky (KimchiConstraint StepField) t (StepProverM 1 WrapIPARounds StepField) Unit)