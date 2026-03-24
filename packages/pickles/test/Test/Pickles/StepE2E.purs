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

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Maybe (fromJust)
import Data.Schnorr.Gen (genValidSignature)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Pickles.Dummy (dummyFinalizeOtherProofParams, dummyStepAdvice, stepDummyUnfinalizedProof) as Dummy
import Pickles.PublicInputCommit (CorrectionMode(..))
import Pickles.Step.Advice (class StepWitnessM)
import Pickles.Step.Circuit (WrapStatementPublicInput)
import Pickles.Step.Circuit (stepCircuit)
import Pickles.Types (StepField, StepIPARounds, WrapIPARounds)
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky)
import Snarky.Circuit.DSL (sizeInFields)
import Snarky.Circuit.Kimchi (groupMapParams) as Kimchi
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (curveParams, generator, toAffine)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.TestContext (StepAdvice, StepProverM, StepSchnorrInput, StepSchnorrInputVar, runStepProverM, stepSchnorrAppCircuit)
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
  => StepWitnessM 1 StepIPARounds WrapIPARounds m StepField
  => StepSchnorrInputVar
  -> Snarky (KimchiConstraint StepField) t m Unit
stepSchnorrCircuit input = do
  let
    pallasGen :: AffinePoint (F StepField)
    pallasGen = coerce (unsafePartial fromJust $ toAffine (generator :: PallasG) :: AffinePoint StepField)
    numPublic = sizeInFields (Proxy @StepField) (Proxy @(WrapStatementPublicInput StepIPARounds (F StepField)))
    params = Record.merge Dummy.dummyFinalizeOtherProofParams
      { curveParams: curveParams (Proxy @PallasG)
      , lagrangeComms: Array.replicate numPublic pallasGen
      , blindingH: pallasGen
      , groupMapParams: Kimchi.groupMapParams (Proxy @PallasG)
      , correctionMode: PureCorrections
      , useOptSponge: false
      }
  _ <- stepCircuit @StepIPARounds params (stepSchnorrAppCircuit false) input
  pure unit

-------------------------------------------------------------------------------
-- | Generator for valid Step+Schnorr inputs
-------------------------------------------------------------------------------

genStepSchnorrInput :: Gen StepSchnorrInput
genStepSchnorrInput = do
  schnorrInput <- genValidSignature (Proxy @PallasG) (Proxy @4)
  pure
    { appInput: schnorrInput
    , previousProofInputs: unit :< Vector.nil
    , unfinalizedProofs: Dummy.stepDummyUnfinalizedProof :< Vector.nil
    , prevChallengeDigests: zero :< Vector.nil
    }

-- | Dummy advice using production library values (from Pickles.Dummy).
genStepSchnorrAdvice :: Gen (StepAdvice 1 StepIPARounds WrapIPARounds StepField)
genStepSchnorrAdvice = pure Dummy.dummyStepAdvice

spec
  :: TestConfig StepField (KimchiGate StepField) (AuxState StepField)
  -> Spec Unit
spec cfg = describe "Step E2E with Schnorr" do
  it "Step circuit with Schnorr application is satisfiable (base case)" do
    advice <- liftEffect $ randomSampleOne genStepSchnorrAdvice

    let
      stepSchnorrCircuit'
        :: forall t
         . CircuitM StepField (KimchiConstraint StepField) t (StepProverM 1 StepIPARounds WrapIPARounds StepField)
        => StepSchnorrInputVar
        -> Snarky (KimchiConstraint StepField) t (StepProverM 1 StepIPARounds WrapIPARounds StepField) Unit
      stepSchnorrCircuit' = stepSchnorrCircuit
    void $ circuitTestM' @StepField (runStepProverM advice)
      cfg
      (NEA.singleton { testFunction: satisfied_, input: QuickCheck 10 genStepSchnorrInput })
      stepSchnorrCircuit'
