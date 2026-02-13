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

import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Schnorr.Gen (VerifyInput, genValidSignature)
import Data.Vector ((:<))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.IPA (type2ScalarOps)
import Pickles.Step.Circuit (AppCircuitInput, AppCircuitOutput, StepInput, stepCircuit)
import Pickles.Step.Dummy (dummyFinalizeOtherProofParams, dummyProofWitness, dummyUnfinalizedProof)
import Pickles.Verify.Types (UnfinalizedProof)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, assert_, const_, false_)
import Snarky.Circuit.Kimchi (Type2)
import Snarky.Circuit.Schnorr (SignatureVar(..), pallasScalarOps, verifies)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (generator, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied_)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

type StepField = Vesta.ScalarField

-- | The Schnorr verification input (application circuit input)
type SchnorrInput = VerifyInput 4 (F StepField)

-- | Full Step circuit input: Schnorr input + dummy previous proof data
type StepSchnorrInput =
  StepInput 1 SchnorrInput Unit (F StepField) (Type2 (F StepField) Boolean) Boolean

-- | Variable version for circuit
type StepSchnorrInputVar =
  StepInput 1
    (VerifyInput 4 (FVar StepField))
    Unit
    (FVar StepField)
    (Type2 (FVar StepField) (BoolVar StepField))
    (BoolVar StepField)

-------------------------------------------------------------------------------
-- | Schnorr Application Circuit
-------------------------------------------------------------------------------

-- | The application circuit: Schnorr verification.
schnorrAppCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => AppCircuitInput 1 (VerifyInput 4 (FVar StepField)) Unit
  -> Snarky (KimchiConstraint StepField) t m (AppCircuitOutput 1 Unit Unit StepField)
schnorrAppCircuit { appInput: { signature: { r: sigR, s: sigS }, publicKey, message } } = do
  let
    genPointVar :: AffinePoint (FVar StepField)
    genPointVar =
      let
        { x, y } = unsafePartial fromJust $ toAffine (generator @_ @Pallas.G)
      in
        { x: const_ x, y: const_ y }
    signature = SignatureVar { r: sigR, s: sigS }

  -- Use pallasScalarOps (@51 bits) for Schnorr over Vesta.ScalarField
  -- Note: pallasScalarOps provides scalar arithmetic for Pallas.ScalarField
  -- which is the same as Vesta.BaseField.
  isValid <- verifies (pallasScalarOps @51) genPointVar { signature, publicKey, message }

  -- For base case, we assert the signature is valid.
  assert_ isValid

  pure
    { mustVerify: false_ :< Vector.nil
    , publicOutput: unit
    , auxiliaryOutput: unit
    }

-------------------------------------------------------------------------------
-- | Test Circuit
-------------------------------------------------------------------------------

-- | The composed Step circuit with Schnorr as application logic.
stepSchnorrCircuit
  :: forall t
   . CircuitM StepField (KimchiConstraint StepField) t Identity
  => StepSchnorrInputVar
  -> Snarky (KimchiConstraint StepField) t Identity Unit
stepSchnorrCircuit input = do
  let ops = type2ScalarOps
  _ <- stepCircuit ops dummyFinalizeOtherProofParams schnorrAppCircuit input
  pure unit

-------------------------------------------------------------------------------
-- | Generator for valid Step+Schnorr inputs
-------------------------------------------------------------------------------

-- | Generator for valid Step+Schnorr inputs
genStepSchnorrInput :: Gen StepSchnorrInput
genStepSchnorrInput =
  let
    unfinalizedProof :: UnfinalizedProof (F StepField) (Type2 (F StepField) Boolean) Boolean
    unfinalizedProof = dummyUnfinalizedProof @StepField @Pallas.ScalarField
  in
    genValidSignature (Proxy @Pallas.G) (Proxy @4) <#> \schnorrInput ->
      { appInput: schnorrInput
      , previousProofInputs: unit :< Vector.nil
      , unfinalizedProofs: unfinalizedProof :< Vector.nil
      , proofWitnesses: dummyProofWitness :< Vector.nil
      , prevChallengeDigests: zero :< Vector.nil
      }

spec :: Spec Unit
spec = describe "Step E2E with Schnorr" do
  it "Step circuit with Schnorr application is satisfiable (base case)" do
    circuitSpecPure' 10
      { builtState: compilePure
          (Proxy @StepSchnorrInput)
          (Proxy @Unit)
          (Proxy @(KimchiConstraint StepField))
          stepSchnorrCircuit
          Kimchi.initialState
      , checker: Kimchi.eval
      , solver: makeSolver (Proxy @(KimchiConstraint StepField)) stepSchnorrCircuit
      , testFunction: satisfied_
      , postCondition: Kimchi.postCondition
      }
      genStepSchnorrInput