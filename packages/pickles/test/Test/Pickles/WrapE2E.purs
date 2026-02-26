module Test.Pickles.WrapE2E
  ( spec
  ) where

-- | End-to-end tests for the Wrap circuit.
-- |
-- | The Wrap circuit runs on Pallas.ScalarField (Fq) and verifies
-- | a Step proof (Vesta commitments) via incrementallyVerifyProof.
-- |
-- | This module:
-- | 1. Reuses the Schnorr Step proof from E2E
-- | 2. Constructs WrapCircuitInput from the Step proof + oracles
-- | 3. Runs the Wrap circuit for satisfiability
-- | 4. Generates an actual Wrap proof (Pallas proof)

import Prelude

import Data.Array.NonEmpty as NEA
import Effect.Aff (Aff)
import Pickles.IPA (type1ScalarOps)
import Pickles.Types (StepIPARounds, WrapIPARounds)
import Pickles.Wrap.Advice (class WrapWitnessM)
import Pickles.Wrap.Circuit (WrapInputVar, wrapCircuit)
import Snarky.Circuit.DSL (class CircuitM, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Pallas as Pallas
import Test.Pickles.TestContext (InductiveTestContext, StepProofContext, WrapProverM, buildWrapCircuitInput, buildWrapCircuitParams, buildWrapProverWitness, runWrapProverM)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTestM', satisfied_)
import Test.Spec (SpecT, describe, it)

-------------------------------------------------------------------------------
-- | Tests
-------------------------------------------------------------------------------

-- | Test that the Wrap circuit is satisfiable with real Step proof data.
wrapCircuitSatisfiableTest :: TestConfig Pallas.ScalarField (KimchiGate Pallas.ScalarField) (AuxState Pallas.ScalarField) -> StepProofContext -> Aff Unit
wrapCircuitSatisfiableTest cfg ctx = do
  let
    params = buildWrapCircuitParams ctx
    circuitInput = buildWrapCircuitInput ctx
    witnessData = buildWrapProverWitness ctx

    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => WrapWitnessM StepIPARounds WrapIPARounds m Pallas.ScalarField
      => WrapInputVar StepIPARounds
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
    circuit = wrapCircuit @1 @StepIPARounds type1ScalarOps params

  let
    circuit'
      :: forall t
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t (WrapProverM StepIPARounds WrapIPARounds Pallas.ScalarField)
      => WrapInputVar StepIPARounds
      -> Snarky (KimchiConstraint Pallas.ScalarField) t (WrapProverM StepIPARounds WrapIPARounds Pallas.ScalarField) Unit
    circuit' = circuit
  void $ circuitTestM' @Pallas.ScalarField (runWrapProverM witnessData)
    cfg
    (NEA.singleton { testFunction: satisfied_, input: Exact (NEA.singleton circuitInput) })
    circuit'

-------------------------------------------------------------------------------
-- | Spec
-------------------------------------------------------------------------------

spec :: TestConfig Pallas.ScalarField (KimchiGate Pallas.ScalarField) (AuxState Pallas.ScalarField) -> SpecT Aff InductiveTestContext Aff Unit
spec cfg =
  describe "Wrap E2E" do
    it "Wrap circuit satisfiable on real Step proof" \{ step0 } -> wrapCircuitSatisfiableTest cfg step0
