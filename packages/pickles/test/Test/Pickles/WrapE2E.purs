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

import Data.Array as Array
import Data.Reflectable (class Reflectable, reifyType)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Pickles.IPA (type1ScalarOps)
import Pickles.Types (StepIPARounds, WrapField, WrapIPARounds)
import Pickles.Wrap.Advice (class WrapWitnessM)
import Pickles.Wrap.Circuit (WrapInput, wrapCircuit)
import Snarky.Backend.Compile (SolverT, compile, makeSolver, runSolverT)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky)
import Snarky.Circuit.Kimchi (Type1, groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (KimchiRow, toKimchiRows)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Pickles.TestContext (StepCase(..), StepProofContext, WrapProverM, buildWrapCircuitInput, buildWrapCircuitParams, buildWrapClaimedDigest, buildWrapProverWitness, createStepProofContext, createTestContext', runWrapProverM)
import Test.Snarky.Circuit.Utils (circuitSpecInputs, satisfied_)
import Test.Spec (SpecT, beforeAll, describe, it)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Tests
-------------------------------------------------------------------------------

-- | Test that the Wrap circuit is satisfiable with real Step proof data.
wrapCircuitSatisfiableTest :: StepProofContext -> Aff Unit
wrapCircuitSatisfiableTest ctx =
  reifyType (Array.length ctx.publicInputs) go
  where
  go :: forall nPublic. Reflectable nPublic Int => Proxy nPublic -> Aff Unit
  go _ = do
    let
      params = buildWrapCircuitParams @nPublic ctx
      claimedDigest = buildWrapClaimedDigest ctx
      circuitInput = buildWrapCircuitInput @nPublic ctx
      witnessData = buildWrapProverWitness ctx

      circuit
        :: forall t m
         . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
        => WrapWitnessM StepIPARounds m Pallas.ScalarField
        => WrapInput nPublic 0 StepIPARounds WrapIPARounds (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField)) (BoolVar Pallas.ScalarField)
        -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
      circuit = wrapCircuit type1ScalarOps (groupMapParams $ Proxy @Vesta.G) params claimedDigest

    builtState <- liftEffect $ compile
      (Proxy @(WrapInput nPublic 0 StepIPARounds WrapIPARounds (F WrapField) (Type1 (F WrapField)) Boolean))
      (Proxy @Unit)
      (Proxy @(KimchiConstraint Pallas.ScalarField))
      circuit
      Kimchi.initialState

    circuitSpecInputs (runWrapProverM witnessData)
      { builtState
      , checker: Kimchi.eval
      , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField))
          (circuit :: forall t. CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t (WrapProverM Pallas.ScalarField) => WrapInput nPublic 0 StepIPARounds WrapIPARounds (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField)) (BoolVar Pallas.ScalarField) -> Snarky (KimchiConstraint Pallas.ScalarField) t (WrapProverM Pallas.ScalarField) Unit)
      , testFunction: satisfied_
      , postCondition: Kimchi.postCondition
      }
      [ circuitInput ]

-- | Test that we can create a real Wrap proof (Pallas proof).
wrapProofCreationTest :: StepProofContext -> Aff Unit
wrapProofCreationTest ctx =
  reifyType (Array.length ctx.publicInputs) go
  where
  go :: forall nPublic. Reflectable nPublic Int => Proxy nPublic -> Aff Unit
  go _ = do
    let
      params = buildWrapCircuitParams @nPublic ctx
      claimedDigest = buildWrapClaimedDigest ctx
      circuitInput = buildWrapCircuitInput @nPublic ctx
      witnessData = buildWrapProverWitness ctx

      circuit
        :: forall t m
         . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
        => WrapWitnessM StepIPARounds m Pallas.ScalarField
        => WrapInput nPublic 0 StepIPARounds WrapIPARounds (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField)) (BoolVar Pallas.ScalarField)
        -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
      circuit = wrapCircuit type1ScalarOps (groupMapParams $ Proxy @Vesta.G) params claimedDigest

    builtState <- liftEffect $ compile
      (Proxy @(WrapInput nPublic 0 StepIPARounds WrapIPARounds (F WrapField) (Type1 (F WrapField)) Boolean))
      (Proxy @Unit)
      (Proxy @(KimchiConstraint Pallas.ScalarField))
      circuit
      Kimchi.initialState

    let
      rawSolver :: SolverT Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) (WrapProverM Pallas.ScalarField) (WrapInput nPublic 0 StepIPARounds WrapIPARounds (F WrapField) (Type1 (F WrapField)) Boolean) Unit
      rawSolver = makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField))
        (circuit :: forall t. CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t (WrapProverM Pallas.ScalarField) => WrapInput nPublic 0 StepIPARounds WrapIPARounds (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField)) (BoolVar Pallas.ScalarField) -> Snarky (KimchiConstraint Pallas.ScalarField) t (WrapProverM Pallas.ScalarField) Unit)

    -- Log circuit size information
    let
      kimchiRows :: Array (KimchiRow Pallas.ScalarField)
      kimchiRows = Array.concatMap
        (toKimchiRows :: KimchiGate Pallas.ScalarField -> Array (KimchiRow Pallas.ScalarField))
        builtState.constraints
    liftEffect $ log $ "[Wrap] Step proof domainLog2: " <> show ctx.domainLog2
    liftEffect $ log $ "[Wrap] Circuit gates (high-level): " <> show (Array.length builtState.constraints)
    liftEffect $ log $ "[Wrap] Kimchi rows (expanded): " <> show (Array.length kimchiRows)
    liftEffect $ log $ "[Wrap] Public inputs: " <> show (Array.length builtState.publicInputs)

    crs <- liftEffect $ createCRS @WrapField
    _pallasCtx <- createTestContext'
      { builtState
      , solver: \a -> liftEffect $ runWrapProverM witnessData (runSolverT rawSolver a)
      , input: circuitInput
      , targetDomainLog2: 15
      , crs
      }
    -- If we get here without error, the proof was created successfully
    pure unit

-------------------------------------------------------------------------------
-- | Spec
-------------------------------------------------------------------------------

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll (createStepProofContext BaseCase) $
  describe "Wrap E2E" do
    it "Wrap circuit satisfiable on real Step proof" wrapCircuitSatisfiableTest
    it "Wrap proof creation succeeds" wrapProofCreationTest
