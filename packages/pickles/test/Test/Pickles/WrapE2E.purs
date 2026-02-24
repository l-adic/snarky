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

import Effect.Aff (Aff)
import Pickles.IPA (type1ScalarOps)
import Pickles.Types (StepIPARounds, WrapIPARounds)
import Pickles.Wrap.Advice (class WrapWitnessM)
import Pickles.Wrap.Circuit (WrapInputVar, wrapCircuit)
import Record as Record
import Snarky.Circuit.DSL (class CircuitM, Snarky)
import Snarky.Circuit.Kimchi (groupMapParams)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Pickles.TestContext (InductiveTestContext, StepProofContext, WrapProverM, buildWrapCircuitInput, buildWrapCircuitParams, buildWrapProverWitness, runWrapProverM)
import Test.Snarky.Circuit.Utils (TestConfig, circuitTestInputsM', satisfied_)
import Test.Spec (SpecT, describe, it)
import Type.Proxy (Proxy(..))

kimchiTestConfig :: forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)
kimchiTestConfig = { checker: eval, postCondition: Kimchi.postCondition, initState: Kimchi.initialState }

-------------------------------------------------------------------------------
-- | Tests
-------------------------------------------------------------------------------

-- | Test that the Wrap circuit is satisfiable with real Step proof data.
wrapCircuitSatisfiableTest :: StepProofContext -> Aff Unit
wrapCircuitSatisfiableTest ctx = do
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
    circuit = wrapCircuit @1 @StepIPARounds type1ScalarOps (groupMapParams $ Proxy @Vesta.G) params

  void $ circuitTestInputsM' @Pallas.ScalarField (runWrapProverM witnessData)
    (Record.merge kimchiTestConfig { testFunction: satisfied_ })
    [ circuitInput ]
    (circuit :: forall t. CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t (WrapProverM StepIPARounds WrapIPARounds Pallas.ScalarField) => WrapInputVar StepIPARounds -> Snarky (KimchiConstraint Pallas.ScalarField) t (WrapProverM StepIPARounds WrapIPARounds Pallas.ScalarField) Unit)

-------------------------------------------------------------------------------
-- | Spec
-------------------------------------------------------------------------------

spec :: SpecT Aff InductiveTestContext Aff Unit
spec =
  describe "Wrap E2E" do
    it "Wrap circuit satisfiable on real Step proof" \{ step0 } -> wrapCircuitSatisfiableTest step0
