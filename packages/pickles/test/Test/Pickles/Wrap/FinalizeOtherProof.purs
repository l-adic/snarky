module Test.Pickles.Wrap.FinalizeOtherProof
  ( realDataSpec
  ) where

-- | Test for the FinalizeOtherProof circuit on the Wrap side (Fq circuit).
-- |
-- | Generates a real Schnorr Step proof, then builds cross-field inputs
-- | and verifies all deferred value checks pass in the Wrap circuit.
-- |
-- | This mirrors Test.Pickles.Step.FinalizeOtherProof but in the reverse
-- | direction: Wrap (Fq) circuit verifying Step (Fp) proof deferred values.

import Prelude

import Data.Identity (Identity)
import Effect.Aff (Aff)
import Pickles.IPA as IPA
import Pickles.PlonkChecks.XiCorrect (emptyPrevChallengeDigest)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofInput, FinalizeOtherProofParams, finalizeOtherProofCircuit)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, assert_)
import Snarky.Circuit.Kimchi (Type1)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Pickles.Types (StepIPARounds, WrapField)
import Test.Pickles.TestContext (StepCase(..), buildFinalizeInput, buildFinalizeParams, createStepProofContext)
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied_)
import Test.Spec (SpecT, beforeAll, describe, it)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Value type for test input (Wrap-side finalize: verifying Step proof → d = StepIPARounds)
type FinalizeOtherProofTestInput =
  FinalizeOtherProofInput StepIPARounds (F WrapField) (Type1 (F WrapField)) Boolean

-- | Variable type for circuit
type FinalizeOtherProofTestInputVar =
  FinalizeOtherProofInput StepIPARounds (FVar WrapField) (Type1 (FVar WrapField)) (BoolVar WrapField)

-------------------------------------------------------------------------------
-- | Real data test (All-checks with Step proof)
-------------------------------------------------------------------------------

type FinalizeOtherProofTestContext =
  { params :: FinalizeOtherProofParams WrapField
  , input :: FinalizeOtherProofTestInput
  }

-- | Build the test context by generating a real Step proof and extracting
-- | cross-field data for the Wrap verifier.
createFinalizeOtherProofTestContext :: Aff FinalizeOtherProofTestContext
createFinalizeOtherProofTestContext = do
  stepCtx <- createStepProofContext BaseCase
  let
    params = buildFinalizeParams stepCtx
    input = buildFinalizeInput { prevChallengeDigest: emptyPrevChallengeDigest, stepCtx }
  pure { params, input }

realDataSpec :: SpecT Aff Unit Aff Unit
realDataSpec = beforeAll createFinalizeOtherProofTestContext $
  describe "Pickles.Wrap.FinalizeOtherProof (real data)" do
    it "all checks pass with real Step proof data" \{ params, input } -> do
      let
        circuit
          :: forall t
           . CircuitM WrapField (KimchiConstraint WrapField) t Identity
          => FinalizeOtherProofTestInputVar
          -> Snarky (KimchiConstraint WrapField) t Identity Unit
        circuit x = do
          let
            ops :: IPA.IpaScalarOps WrapField t Identity (Type1 (FVar WrapField))
            ops = IPA.type1ScalarOps
          { finalized } <- evalSpongeM initialSpongeCircuit (finalizeOtherProofCircuit ops params x)
          assert_ finalized

      circuitSpecPureInputs
        { builtState: compilePure
            (Proxy @FinalizeOtherProofTestInput)
            (Proxy @Unit)
            (Proxy @(KimchiConstraint WrapField))
            circuit
            Kimchi.initialState
        , checker: Kimchi.eval
        , solver: makeSolver (Proxy @(KimchiConstraint WrapField)) circuit
        , testFunction: satisfied_
        , postCondition: Kimchi.postCondition
        }
        [ input ]
