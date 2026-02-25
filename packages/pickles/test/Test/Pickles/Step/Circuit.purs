module Test.Pickles.Step.Circuit
  ( spec
  , realDataSpec
  ) where

-- | Tests for the Step circuit combinator.
-- |
-- | Tests verify that the Step circuit is satisfiable with:
-- | 1. Dummy proofs (base case for bootstrapping Pickles recursion)
-- | 2. Real Wrap proof data (Step → Wrap → Step cycle)

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Schnorr.Gen (genValidSignature)
import Data.Vector (nil, (:<))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles.IPA (type2ScalarOps)
import Pickles.PlonkChecks.XiCorrect (emptyPrevChallengeDigest)
import Pickles.Step.Advice (class StepWitnessM)
import Pickles.Step.Circuit (AppCircuitInput, AppCircuitOutput, StepInput, stepCircuit)
import Pickles.Step.Dummy (dummyFinalizeOtherProofParams)
import Pickles.Types (StepField, StepIPARounds, WrapIPARounds)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, false_)
import Snarky.Circuit.Kimchi (Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Pasta (PallasG)
import Test.Pickles.TestContext (InductiveTestContext, SchnorrInputVar, StepProverM, StepSchnorrInput, buildStepFinalizeInput, buildStepFinalizeParams, buildStepProverWitness, dummyStepAdvice, genDummyUnfinalizedProof, runStepProverM, stepSchnorrAppCircuit)
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTestM', satisfied_)
import Test.Spec (Spec, SpecT, describe, it)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Value type for test input
type StepTestInput =
  StepInput 1 Unit Unit StepIPARounds WrapIPARounds (F StepField) (Type2 (F StepField) Boolean) Boolean

-- | Variable type for circuit
type StepTestInputVar =
  StepInput 1 Unit Unit StepIPARounds WrapIPARounds (FVar StepField) (Type2 (FVar StepField) (BoolVar StepField)) (BoolVar StepField)

-------------------------------------------------------------------------------
-- | Application Circuit
-------------------------------------------------------------------------------

-- | Trivial app circuit for base case: returns mustVerify=false
trivialAppCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => AppCircuitInput 1 Unit Unit
  -> Snarky (KimchiConstraint StepField) t m (AppCircuitOutput 1 Unit Unit StepField)
trivialAppCircuit _ = pure
  { mustVerify: false_ :< nil
  , publicOutput: unit
  , auxiliaryOutput: unit
  }

-------------------------------------------------------------------------------
-- | Test Circuit
-------------------------------------------------------------------------------

-- | The circuit under test: runs stepCircuit and discards output
testCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepWitnessM 1 WrapIPARounds m StepField
  => StepTestInputVar
  -> Snarky (KimchiConstraint StepField) t m Unit
testCircuit input = do
  let ops = type2ScalarOps
  _ <- stepCircuit ops dummyFinalizeOtherProofParams trivialAppCircuit input
  pure unit

-------------------------------------------------------------------------------
-- | Tests
-------------------------------------------------------------------------------

spec :: TestConfig StepField (KimchiGate StepField) (AuxState StepField) -> Spec Unit
spec cfg = describe "Pickles.Step.Circuit" do
  it "Step circuit is satisfiable with dummy proofs (base case)" do
    unfinalizedProof <- liftEffect $ randomSampleOne genDummyUnfinalizedProof
    advice <- liftEffect $ randomSampleOne dummyStepAdvice

    let
      input :: StepTestInput
      input =
        { appInput: unit
        , previousProofInputs: unit :< nil
        , unfinalizedProofs: unfinalizedProof :< nil
        , prevChallengeDigests: zero :< nil
        }

    let
      testCircuit'
        :: forall t
         . CircuitM StepField (KimchiConstraint StepField) t (StepProverM 1 WrapIPARounds StepField)
        => StepTestInputVar
        -> Snarky (KimchiConstraint StepField) t (StepProverM 1 WrapIPARounds StepField) Unit
      testCircuit' = testCircuit
    void $ circuitTestM' @StepField
      (runStepProverM advice)
      cfg
      (NEA.singleton { testFunction: satisfied_, input: Exact (NEA.singleton input) })
      testCircuit'

-------------------------------------------------------------------------------
-- | Real data test (Step → Wrap → Step cycle)
-------------------------------------------------------------------------------
type StepSchnorrInputVar =
  StepInput 1 SchnorrInputVar Unit StepIPARounds WrapIPARounds (FVar StepField) (Type2 (FVar StepField) (BoolVar StepField)) (BoolVar StepField)

realDataSpec :: TestConfig StepField (KimchiGate StepField) (AuxState StepField) -> SpecT Aff InductiveTestContext Aff Unit
realDataSpec cfg =
  describe "Pickles.Step.Circuit (real data)" do
    it "Step circuit verifies real Wrap proof (Step → Wrap → Step)" \{ wrap0 } -> do
      schnorrInput <- liftEffect $ randomSampleOne $ genValidSignature (Proxy @PallasG) (Proxy @4)
      let
        params = buildStepFinalizeParams wrap0
        fopInput = buildStepFinalizeInput
          { prevChallengeDigest: emptyPrevChallengeDigest
          , wrapCtx: wrap0
          }

        input :: StepSchnorrInput
        input =
          { appInput: schnorrInput
          , previousProofInputs: unit :< nil
          , unfinalizedProofs: fopInput.unfinalized :< nil
          , prevChallengeDigests: fopInput.prevChallengeDigest :< nil
          }
        witnessData = buildStepProverWitness wrap0
      let
        realCircuit
          :: forall t m
           . CircuitM StepField (KimchiConstraint StepField) t m
          => StepWitnessM 1 WrapIPARounds m StepField
          => StepSchnorrInputVar
          -> Snarky (KimchiConstraint StepField) t m Unit
        realCircuit i = do
          _ <- stepCircuit type2ScalarOps params (stepSchnorrAppCircuit true) i
          pure unit

      let
        realCircuit'
          :: forall t
           . CircuitM StepField (KimchiConstraint StepField) t (StepProverM 1 WrapIPARounds StepField)
          => StepSchnorrInputVar
          -> Snarky (KimchiConstraint StepField) t (StepProverM 1 WrapIPARounds StepField) Unit
        realCircuit' = realCircuit
      void $ circuitTestM' @StepField
        (runStepProverM witnessData)
        cfg
        (NEA.singleton { testFunction: satisfied_, input: Exact (NEA.singleton input) })
        realCircuit'
