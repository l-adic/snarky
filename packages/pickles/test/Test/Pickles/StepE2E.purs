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

import Data.Schnorr.Gen (genValidSignature)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Class (liftEffect)
import Pickles.IPA (type2ScalarOps)
import Pickles.Step.Advice (class StepWitnessM)
import Pickles.Step.Circuit (stepCircuit)
import Pickles.Step.Dummy (dummyFinalizeOtherProofParams, dummyProofWitness, dummyUnfinalizedProof)
import Pickles.Types (StepField, WrapIPARounds)
import Pickles.Verify.Types (UnfinalizedProof)
import Snarky.Backend.Compile (compile, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F, Snarky)
import Snarky.Circuit.Kimchi (Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Test.Pickles.TestContext (StepProverM, StepSchnorrInput, StepSchnorrInputVar, runStepProverM, stepSchnorrAppCircuit)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpec', satisfied_)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Test Circuit
-------------------------------------------------------------------------------

-- | The composed Step circuit with Schnorr as application logic (base case).
stepSchnorrCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepWitnessM 1 m StepField
  => StepSchnorrInputVar
  -> Snarky (KimchiConstraint StepField) t m Unit
stepSchnorrCircuit input = do
  _ <- stepCircuit type2ScalarOps dummyFinalizeOtherProofParams (stepSchnorrAppCircuit false) input
  pure unit

-------------------------------------------------------------------------------
-- | Generator for valid Step+Schnorr inputs
-------------------------------------------------------------------------------

genStepSchnorrInput :: Gen StepSchnorrInput
genStepSchnorrInput =
  let
    unfinalizedProof :: UnfinalizedProof WrapIPARounds (F StepField) (Type2 (F StepField) Boolean) Boolean
    unfinalizedProof = dummyUnfinalizedProof @WrapIPARounds @StepField @Pallas.ScalarField
  in
    genValidSignature (Proxy @PallasG) (Proxy @4) <#> \schnorrInput ->
      { appInput: schnorrInput
      , previousProofInputs: unit :< Vector.nil
      , unfinalizedProofs: unfinalizedProof :< Vector.nil
      , prevChallengeDigests: zero :< Vector.nil
      }

spec :: Spec Unit
spec = describe "Step E2E with Schnorr" do
  it "Step circuit with Schnorr application is satisfiable (base case)" do

    builtState <- liftEffect $ compile
      (Proxy @StepSchnorrInput)
      (Proxy @Unit)
      (Proxy @(KimchiConstraint StepField))
      stepSchnorrCircuit
      Kimchi.initialState

    let dummyWitnesses = dummyProofWitness :< Vector.nil

    circuitSpec' 10 (runStepProverM dummyWitnesses)
      { builtState
      , checker: Kimchi.eval
      , solver: makeSolver (Proxy @(KimchiConstraint StepField))
          (stepSchnorrCircuit :: forall t. CircuitM StepField (KimchiConstraint StepField) t (StepProverM 1 StepField) => StepSchnorrInputVar -> Snarky (KimchiConstraint StepField) t (StepProverM 1 StepField) Unit)
      , testFunction: satisfied_
      , postCondition: Kimchi.postCondition
      }
      genStepSchnorrInput