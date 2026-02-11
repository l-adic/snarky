module Test.Pickles.Step.FinalizeOtherProof
  ( spec
  , realDataSpec
  ) where

-- | Tests for the FinalizeOtherProof circuit.
-- |
-- | Two test scenarios:
-- | 1. Base case: dummy inputs with shouldFinalize = false (bootstrapping)
-- | 2. Real data: Schnorr proof data with shouldFinalize = true (all checks)
-- |
-- | STAGED: This test is set up to generate a real Wrap proof (Pallas) 
-- | and verify it in the Step circuit (Vesta). The cross-field mappings
-- | are currently placeholders for implementation by an expert.

import Prelude

import Data.Identity (Identity)
import Effect.Aff (Aff)
import Pickles.IPA as IPA
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.Dummy (dummyFinalizeOtherProofParams, dummyUnfinalizedProof, dummyWrapProofWitness)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofInput, FinalizeOtherProofParams, finalizeOtherProofCircuit)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, assert_)
import Snarky.Circuit.Kimchi (Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Pickles.StepInputBuilder (buildFinalizeInput, buildFinalizeParams)
import Test.Pickles.TestContext (createWrapProofContext)
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied_)
import Test.Spec (Spec, SpecT, beforeAll, describe, it)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

type StepField = Vesta.ScalarField
type WrapField = Pallas.ScalarField

-- | Value type for test input
type FinalizeOtherProofTestInput =
  FinalizeOtherProofInput (F StepField) (Type2 (F StepField) Boolean) Boolean

-- | Variable type for circuit
type FinalizeOtherProofTestInputVar =
  FinalizeOtherProofInput (FVar StepField) (Type2 (FVar StepField) (BoolVar StepField)) (BoolVar StepField)

-------------------------------------------------------------------------------
-- | Tests
-------------------------------------------------------------------------------

spec :: Spec Unit
spec = describe "Pickles.Step.FinalizeOtherProof" do
  it "skeleton circuit is satisfiable with dummy inputs (base case)" do
    let
      input :: FinalizeOtherProofTestInput
      input =
        { unfinalized: dummyUnfinalizedProof @StepField @WrapField @(Type2 (F StepField) Boolean)
        , witness: dummyWrapProofWitness
        , prevChallengeDigest: zero
        }

      dummyTestCircuit
        :: forall t
         . CircuitM StepField (KimchiConstraint StepField) t Identity
        => FinalizeOtherProofTestInputVar
        -> Snarky (KimchiConstraint StepField) t Identity Unit
      dummyTestCircuit x =
        let
          ops :: IPA.IpaScalarOps StepField t Identity (Type2 (FVar StepField) (BoolVar StepField))
          ops = IPA.type2ScalarOps
        in
          void $ evalSpongeM initialSpongeCircuit (finalizeOtherProofCircuit ops dummyFinalizeOtherProofParams x)

    circuitSpecPureInputs
      { builtState: compilePure
          (Proxy @FinalizeOtherProofTestInput)
          (Proxy @Unit)
          (Proxy @(KimchiConstraint StepField))
          dummyTestCircuit
          Kimchi.initialState
      , checker: Kimchi.eval
      , solver: makeSolver (Proxy @(KimchiConstraint StepField)) dummyTestCircuit
      , testFunction: satisfied_
      , postCondition: Kimchi.postCondition
      }
      [ input ]

-------------------------------------------------------------------------------
-- | Real data test (All-checks with Wrap proof)
-------------------------------------------------------------------------------

type FinalizeOtherProofTestContext =
  { params :: FinalizeOtherProofParams StepField
  , input :: FinalizeOtherProofTestInput
  }

-- | Build the test context by generating a real Wrap proof and extracting
-- | cross-field data for the Step verifier.
createFinalizeOtherProofTestContext :: Aff FinalizeOtherProofTestContext
createFinalizeOtherProofTestContext = do
  wrapCtx <- createWrapProofContext
  let
    params = buildFinalizeParams wrapCtx
    input = buildFinalizeInput wrapCtx
  pure { params, input }

realDataSpec :: SpecT Aff Unit Aff Unit
realDataSpec = beforeAll createFinalizeOtherProofTestContext $
  describe "Pickles.Step.FinalizeOtherProof (real data)" do
    it "all checks pass with real Wrap proof data" \{ params, input } -> do
      let
        circuit
          :: forall t
           . CircuitM StepField (KimchiConstraint StepField) t Identity
          => FinalizeOtherProofTestInputVar
          -> Snarky (KimchiConstraint StepField) t Identity Unit
        circuit x = do
          let
            ops :: IPA.IpaScalarOps StepField t Identity (Type2 (FVar StepField) (BoolVar StepField))
            ops = IPA.type2ScalarOps
          { finalized } <- evalSpongeM initialSpongeCircuit (finalizeOtherProofCircuit ops params x)
          assert_ finalized

      circuitSpecPureInputs
        { builtState: compilePure
            (Proxy @FinalizeOtherProofTestInput)
            (Proxy @Unit)
            (Proxy @(KimchiConstraint StepField))
            circuit
            Kimchi.initialState
        , checker: Kimchi.eval
        , solver: makeSolver (Proxy @(KimchiConstraint StepField)) circuit
        , testFunction: satisfied_
        , postCondition: Kimchi.postCondition
        }
        [ input ]
