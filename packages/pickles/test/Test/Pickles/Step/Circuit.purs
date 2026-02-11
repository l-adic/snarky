module Test.Pickles.Step.Circuit
  ( spec
  ) where

-- | Tests for the Step circuit combinator.
-- |
-- | Tests verify that the Step circuit is satisfiable with dummy proofs
-- | (base case for bootstrapping Pickles recursion).

import Prelude

import Data.Identity (Identity)
import Data.Vector (nil, (:<))
import Pickles.IPA (type2ScalarOps)
import Pickles.Step.Circuit (AppCircuitInput, AppCircuitOutput, StepInput, stepCircuit)
import Pickles.Step.Dummy (dummyFinalizeOtherProofParams, dummyUnfinalizedProof, dummyWrapProofWitness)
import Pickles.Verify.Types (UnfinalizedProof)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, false_)
import Snarky.Circuit.Kimchi (Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied_)
import Test.Spec (Spec, describe, it)
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