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

import Data.Identity (Identity)
import Data.Schnorr.Gen (VerifyInput, genValidSignature)
import Data.Vector (nil, (:<))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles.IPA (type2ScalarOps)
import Pickles.PlonkChecks.XiCorrect (emptyPrevChallengeDigest)
import Pickles.Step.Circuit (AppCircuitInput, AppCircuitOutput, StepInput, stepCircuit)
import Pickles.Step.Dummy (dummyFinalizeOtherProofParams, dummyUnfinalizedProof, dummyWrapProofWitness)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofParams)
import Pickles.Verify.Types (UnfinalizedProof)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, assert_, false_, true_)
import Snarky.Circuit.Kimchi (Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Curves.Vesta as Vesta
import Test.Pickles.StepInputBuilder (buildFinalizeInput, buildFinalizeParams)
import Test.Pickles.TestContext (createWrapProofContext, schnorrCircuit)
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied_)
import Test.Spec (Spec, SpecT, beforeAll, describe, it)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

type StepField = Vesta.ScalarField

-- | Value type for test input
type StepTestInput =
  StepInput 1 Unit Unit (F StepField) (Type2 (F StepField) Boolean) Boolean

-- | Variable type for circuit
type StepTestInputVar =
  StepInput 1 Unit Unit (FVar StepField) (Type2 (FVar StepField) (BoolVar StepField)) (BoolVar StepField)

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
  :: forall t
   . CircuitM StepField (KimchiConstraint StepField) t Identity
  => StepTestInputVar
  -> Snarky (KimchiConstraint StepField) t Identity Unit
testCircuit input = do
  let ops = type2ScalarOps
  _ <- stepCircuit ops dummyFinalizeOtherProofParams trivialAppCircuit input
  pure unit

-------------------------------------------------------------------------------
-- | Tests
-------------------------------------------------------------------------------

spec :: Spec Unit
spec = describe "Pickles.Step.Circuit" do
  it "Step circuit is satisfiable with dummy proofs (base case)" do
    let
      unfinalizedProof :: UnfinalizedProof (F StepField) (Type2 (F StepField) Boolean) Boolean
      unfinalizedProof = dummyUnfinalizedProof @StepField @Pallas.ScalarField

      input :: StepTestInput
      input =
        { appInput: unit
        , previousProofInputs: unit :< nil
        , unfinalizedProofs: unfinalizedProof :< nil
        , wrapProofWitnesses: dummyWrapProofWitness :< nil
        , prevChallengeDigests: zero :< nil
        }

    circuitSpecPureInputs
      { builtState: compilePure
          (Proxy @StepTestInput)
          (Proxy @Unit)
          (Proxy @(KimchiConstraint StepField))
          testCircuit
          Kimchi.initialState
      , checker: Kimchi.eval
      , solver: makeSolver (Proxy @(KimchiConstraint StepField)) testCircuit
      , testFunction: satisfied_
      , postCondition: Kimchi.postCondition
      }
      [ input ]

-------------------------------------------------------------------------------
-- | Real data test (Step → Wrap → Step cycle)
-------------------------------------------------------------------------------

type SchnorrInput = VerifyInput 4 (F StepField)
type SchnorrInputVar = VerifyInput 4 (FVar StepField)

-- | Real Step input: Schnorr verification as the app circuit
type RealStepTestInput =
  StepInput 1 SchnorrInput Unit (F StepField) (Type2 (F StepField) Boolean) Boolean

type RealStepTestInputVar =
  StepInput 1 SchnorrInputVar Unit (FVar StepField) (Type2 (FVar StepField) (BoolVar StepField)) (BoolVar StepField)

-- | App circuit that verifies a Schnorr signature and returns mustVerify=true
schnorrAppCircuit
  :: forall t
   . CircuitM StepField (KimchiConstraint StepField) t Identity
  => AppCircuitInput 1 SchnorrInputVar Unit
  -> Snarky (KimchiConstraint StepField) t Identity (AppCircuitOutput 1 Unit Unit StepField)
schnorrAppCircuit { appInput } = do
  verified <- schnorrCircuit appInput
  assert_ verified
  pure
    { mustVerify: true_ :< nil
    , publicOutput: unit
    , auxiliaryOutput: unit
    }

type StepCircuitTestContext =
  { params :: FinalizeOtherProofParams StepField
  , input :: RealStepTestInput
  }

createStepCircuitTestContext :: Aff StepCircuitTestContext
createStepCircuitTestContext = do
  wrapCtx <- createWrapProofContext
  schnorrInput <- liftEffect $ randomSampleOne $ genValidSignature (Proxy @PallasG) (Proxy @4)
  let
    params = buildFinalizeParams wrapCtx
    fopInput = buildFinalizeInput { prevChallengeDigest: emptyPrevChallengeDigest, wrapCtx }

    input :: RealStepTestInput
    input =
      { appInput: schnorrInput
      , previousProofInputs: unit :< nil
      , unfinalizedProofs: fopInput.unfinalized :< nil
      , wrapProofWitnesses: fopInput.witness :< nil
      , prevChallengeDigests: fopInput.prevChallengeDigest :< nil
      }
  pure { params, input }

realDataSpec :: SpecT Aff Unit Aff Unit
realDataSpec = beforeAll createStepCircuitTestContext $
  describe "Pickles.Step.Circuit (real data)" do
    it "Step circuit verifies real Wrap proof (Step → Wrap → Step)" \{ params, input } -> do
      let
        realCircuit
          :: forall t
           . CircuitM StepField (KimchiConstraint StepField) t Identity
          => RealStepTestInputVar
          -> Snarky (KimchiConstraint StepField) t Identity Unit
        realCircuit i = do
          let ops = type2ScalarOps
          _ <- stepCircuit ops params schnorrAppCircuit i
          pure unit

      circuitSpecPureInputs
        { builtState: compilePure
            (Proxy @RealStepTestInput)
            (Proxy @Unit)
            (Proxy @(KimchiConstraint StepField))
            realCircuit
            Kimchi.initialState
        , checker: Kimchi.eval
        , solver: makeSolver (Proxy @(KimchiConstraint StepField)) realCircuit
        , testFunction: satisfied_
        , postCondition: Kimchi.postCondition
        }
        [ input ]