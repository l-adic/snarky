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
import Pickles.Step.Circuit (AppCircuitInput, AppCircuitOutput, StepInput, stepCircuit)
import Pickles.Step.Dummy (dummyFinalizeOtherProofParams, dummyUnfinalizedProof, dummyWrapProofWitness)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, assert_, false_)
import Snarky.Circuit.Schnorr (SignatureVar(..), pallasScalarOps, verifies)
import Snarky.Circuit.Types (F)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (generator, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (Type1)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied_)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

type StepField = Vesta.ScalarField

-- | The Schnorr verification input (application circuit input)
type SchnorrInput = VerifyInput 4 (F StepField) Boolean

-- | Full Step circuit input: Schnorr input + dummy previous proof data
type StepSchnorrInput =
  StepInput 1 SchnorrInput Unit (F StepField) (Type1 (F StepField)) Boolean

-- | Variable version for circuit
type StepSchnorrInputVar =
  StepInput 1
    (VerifyInput 4 (FVar StepField) (BoolVar StepField))
    Unit
    (FVar StepField)
    (Type1 (FVar StepField))
    (BoolVar StepField)

-------------------------------------------------------------------------------
-- | Schnorr Application Circuit
-------------------------------------------------------------------------------

-- | Schnorr verification as an application circuit for Step.
-- |
-- | Takes a Schnorr verification input and returns:
-- | - mustVerify = [false] (base case, no previous proofs)
-- | - publicOutput = Unit
-- | - auxiliaryOutput = Unit
schnorrAppCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => AppCircuitInput 1 (VerifyInput 4 (FVar StepField) (BoolVar StepField)) Unit
  -> Snarky (KimchiConstraint StepField) t m (AppCircuitOutput 1 Unit Unit StepField)
schnorrAppCircuit { appInput } = do
  -- Run Schnorr verification
  let
    genPointVar :: AffinePoint (FVar StepField)
    genPointVar =
      let
        { x, y } = unsafePartial fromJust $ toAffine (generator @_ @Pallas.G)
      in
        { x: const_ x, y: const_ y }
    signature = SignatureVar { r: appInput.signature.r, s: appInput.signature.s }

  verifies (pallasScalarOps @51) genPointVar
    { signature, publicKey: appInput.publicKey, message: appInput.message } >>= assert_

  -- Return Step circuit output
  -- For base case: mustVerify = false (no previous proofs to verify)
  pure
    { mustVerify: false_ :< Vector.nil
    , publicOutput: unit
    , auxiliaryOutput: unit
    }

-------------------------------------------------------------------------------
-- | Step Circuit with Schnorr
-------------------------------------------------------------------------------

-- | The composed Step circuit with Schnorr as application logic.
stepSchnorrCircuit
  :: forall t
   . CircuitM StepField (KimchiConstraint StepField) t Identity
  => StepSchnorrInputVar
  -> Snarky (KimchiConstraint StepField) t Identity Unit
stepSchnorrCircuit input = do
  _ <- stepCircuit dummyFinalizeOtherProofParams schnorrAppCircuit input
  pure unit

-------------------------------------------------------------------------------
-- | Tests
-------------------------------------------------------------------------------

-- | Generator for valid Step+Schnorr inputs
genStepSchnorrInput :: Gen StepSchnorrInput
genStepSchnorrInput =
  genValidSignature (Proxy @Pallas.G) (Proxy @4) <#> \schnorrInput ->
    { appInput: schnorrInput
    , previousProofInputs: unit :< Vector.nil
    , unfinalizedProofs: dummyUnfinalizedProof :< Vector.nil
    , wrapProofWitnesses: dummyWrapProofWitness :< Vector.nil
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
