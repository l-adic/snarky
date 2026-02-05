module Test.Pickles.Step.FinalizeOtherProof
  ( spec
  ) where

-- | Tests for the FinalizeOtherProof circuit.
-- |
-- | Tests verify that the skeleton circuit is satisfiable with dummy inputs.
-- | This is the base case for bootstrapping Pickles recursion.

import Prelude

import Data.Identity (Identity)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.Dummy (dummyFinalizeOtherProofParams, dummyUnfinalizedProof, dummyWrapProofWitness)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofInput, finalizeOtherProofCircuit)
import Pickles.Step.Types (BulletproofChallenges)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky)
import Snarky.Circuit.Types (F)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Vesta as Vesta
import Snarky.Types.Shifted (Type1)
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied_)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

type StepField = Vesta.ScalarField

-- | Value type for test input
type FinalizeOtherProofTestInput =
  FinalizeOtherProofInput (F StepField) (Type1 (F StepField)) Boolean

-- | Variable type for circuit
type FinalizeOtherProofTestInputVar =
  FinalizeOtherProofInput (FVar StepField) (Type1 (FVar StepField)) (BoolVar StepField)

-- | Output type from circuit (we only check satisfiability, not output values)
type FinalizeOtherProofTestOutput =
  { finalized :: Boolean
  , challenges :: BulletproofChallenges (F StepField)
  }

-------------------------------------------------------------------------------
-- | Test Circuit
-------------------------------------------------------------------------------

-- | The circuit under test: runs finalizeOtherProofCircuit and discards output
testCircuit
  :: forall t
   . CircuitM StepField (KimchiConstraint StepField) t Identity
  => FinalizeOtherProofTestInputVar
  -> Snarky (KimchiConstraint StepField) t Identity Unit
testCircuit input = do
  _ <- evalSpongeM initialSpongeCircuit (finalizeOtherProofCircuit dummyFinalizeOtherProofParams input)
  pure unit

-------------------------------------------------------------------------------
-- | Tests
-------------------------------------------------------------------------------

spec :: Spec Unit
spec = describe "Pickles.Step.FinalizeOtherProof" do
  it "skeleton circuit is satisfiable with dummy inputs (base case)" do
    let
      input :: FinalizeOtherProofTestInput
      input =
        { unfinalized: dummyUnfinalizedProof
        , witness: dummyWrapProofWitness
        }

    circuitSpecPureInputs
      { builtState: compilePure
          (Proxy @FinalizeOtherProofTestInput)
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
