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
import Pickles.IPA (type1ScalarOps)
import Pickles.Types (StepIPARounds, WrapField, WrapIPARounds)
import Pickles.Wrap.Advice (class WrapWitnessM)
import Pickles.Wrap.Circuit (WrapInput, wrapCircuit)
import Snarky.Backend.Compile (compile, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky)
import Snarky.Circuit.Kimchi (Type1, groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Pickles.TestContext (InductiveTestContext, StepProofContext, WrapProverM, buildWrapCircuitInput, buildWrapCircuitParams, buildWrapClaimedDigest, buildWrapProverWitness, runWrapProverM)
import Test.Snarky.Circuit.Utils (circuitSpecInputs, satisfied_)
import Test.Spec (SpecT, describe, it)
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

-------------------------------------------------------------------------------
-- | Spec
-------------------------------------------------------------------------------

spec :: SpecT Aff InductiveTestContext Aff Unit
spec =
  describe "Wrap E2E" do
    it "Wrap circuit satisfiable on real Step proof" \{ step0 } -> wrapCircuitSatisfiableTest step0
