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

import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Effect.Aff (Aff)
import Pickles.IPA as IPA
import Pickles.PlonkChecks.XiCorrect (emptyPrevChallengeDigest)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofInput, finalizeOtherProofCircuit)
import Pickles.Types (StepIPARounds, WrapField)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, assert_)
import Snarky.Circuit.Kimchi (Type1)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Test.Pickles.TestContext (InductiveTestContext, buildFinalizeInput, buildFinalizeParams)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied_)
import Test.Spec (SpecT, describe, it)

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

realDataSpec :: TestConfig WrapField (KimchiGate WrapField) (AuxState WrapField) -> SpecT Aff InductiveTestContext Aff Unit
realDataSpec cfg =
  describe "Pickles.Wrap.FinalizeOtherProof (real data)" do
    it "all checks pass with real Step proof data" \{ step0 } -> do
      let
        params = buildFinalizeParams step0
        input = buildFinalizeInput { prevChallengeDigest: emptyPrevChallengeDigest, stepCtx: step0 }

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

      void $ circuitTest' @WrapField
        cfg
        (NEA.singleton { testFunction: satisfied_, input: Exact (NEA.singleton input) })
        circuit
