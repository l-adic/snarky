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

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Maybe (fromJust)
import Data.Schnorr.Gen (genValidSignature)
import Data.Vector (Vector, nil, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Pickles.Dummy (dummyFinalizeOtherProofParams)
import Pickles.PublicInputCommit (CorrectionMode(..), mkConstLagrangeBase)
import Pickles.Step.Advice (class StepWitnessM)
import Pickles.Step.Circuit (AppCircuitInput, AppCircuitOutput, StepInput, WrapStatementPublicInput, stepCircuit)
import Pickles.Types (StepField, StepIPARounds, VerificationKey(..), WrapIPARounds)
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, SizedF, Snarky, sizeInFields)
import Snarky.Circuit.Kimchi (SplitField, Type2)
import Snarky.Circuit.Kimchi (groupMapParams) as Kimchi
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (curveParams, generator, toAffine)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Test.Pickles.TestContext (InductiveTestContext, SchnorrInputVar, StepProverM, StepSchnorrInput, buildStepFinalizeInput, buildStepFinalizeParams, buildStepIVPParams, buildStepProverWitness, computeStepChallengeDigest, computeStepSgEvals, extractWrapRawBpChallenges, runStepProverM, stepSchnorrAppCircuit, type1ToType2SF)
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTestM', satisfied_)
import Test.Spec (Spec, SpecT, describe, it)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Value type for test input (n=0: base case, no previous proofs)
type StepTestInput =
  StepInput 0 Unit Unit StepIPARounds WrapIPARounds (F StepField) (Type2 (SplitField (F StepField) Boolean)) Boolean

-- | Variable type for circuit
type StepTestInputVar =
  StepInput 0 Unit Unit StepIPARounds WrapIPARounds (FVar StepField) (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (BoolVar StepField)

-- | Trivial app circuit for base case: returns empty mustVerify
trivialAppCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => AppCircuitInput 0 Unit Unit
  -> Snarky (KimchiConstraint StepField) t m (AppCircuitOutput 0 Unit Unit StepField)
trivialAppCircuit _ = pure
  { mustVerify: nil
  , publicOutput: unit
  , auxiliaryOutput: unit
  }

-- | The circuit under test: runs stepCircuit and discards output
testCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepWitnessM 0 StepIPARounds WrapIPARounds m StepField
  => StepTestInputVar
  -> Snarky (KimchiConstraint StepField) t m Unit
testCircuit input = do
  let
    -- n=0: loop body never runs, IVP params just need to type-check
    pallasGen :: AffinePoint (F StepField)
    pallasGen = coerce (unsafePartial fromJust $ toAffine (generator :: PallasG) :: AffinePoint StepField)
    numPublic = sizeInFields (Proxy @StepField) (Proxy @(WrapStatementPublicInput StepIPARounds (F StepField)))
    params = Record.merge dummyFinalizeOtherProofParams
      { curveParams: curveParams (Proxy @PallasG)
      , lagrangeComms: map mkConstLagrangeBase (Array.replicate numPublic pallasGen)
      , blindingH: pallasGen
      , groupMapParams: Kimchi.groupMapParams (Proxy @PallasG)
      , correctionMode: PureCorrections
      , useOptSponge: false
      }
  _ <- stepCircuit @StepIPARounds params trivialAppCircuit input
  pure unit

spec :: TestConfig StepField (KimchiGate StepField) (AuxState StepField) -> Spec Unit
spec cfg = describe "Pickles.Step.Circuit" do
  it "Step circuit is satisfiable with dummy proofs (base case, n=0)" do
    let
      -- n=0 advice: all vectors empty, dummy VK
      dummyPt = { x: F zero, y: F zero } :: AffinePoint (F StepField)
      -- Pallas generator (on-curve, satisfies the WeierstrassAffinePoint check)
      pallasGenPt :: WeierstrassAffinePoint PallasG (F StepField)
      pallasGenPt = WeierstrassAffinePoint $ coerce (unsafePartial fromJust $ toAffine (generator :: PallasG) :: AffinePoint StepField)
      emptyAdvice =
        { stepInputFields: []
        , evals: nil
        , prevChallenges: nil
        , messages: nil
        , openingProofs: nil
        , fopProofStates: nil
        , messagesForNextWrapProof: nil
        , wrapVerifierIndex: VerificationKey
            { sigma: Vector.generate \_ -> pallasGenPt
            , coeff: Vector.generate \_ -> pallasGenPt
            , index: Vector.generate \_ -> pallasGenPt
            }
        , sgOld: nil
        , sgOldMask: Vector.nil
        }

      input :: StepTestInput
      input =
        { appInput: unit
        , previousProofInputs: nil
        , unfinalizedProofs: nil
        , prevChallengeDigests: nil
        }

    let
      testCircuit'
        :: forall t
         . CircuitM StepField (KimchiConstraint StepField) t (StepProverM 0 StepIPARounds WrapIPARounds StepField)
        => StepTestInputVar
        -> Snarky (KimchiConstraint StepField) t (StepProverM 0 StepIPARounds WrapIPARounds StepField) Unit
      testCircuit' = testCircuit
    void $ circuitTestM' @StepField
      (runStepProverM emptyAdvice)
      cfg
      (NEA.singleton { testFunction: satisfied_, input: Exact (NEA.singleton input) })
      testCircuit'

-------------------------------------------------------------------------------
-- | Real data test (Step → Wrap → Step cycle)
-------------------------------------------------------------------------------
type StepSchnorrInputVar =
  StepInput 1 SchnorrInputVar Unit StepIPARounds WrapIPARounds (FVar StepField) (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (BoolVar StepField)

realDataSpec :: TestConfig StepField (KimchiGate StepField) (AuxState StepField) -> SpecT Aff InductiveTestContext Aff Unit
realDataSpec cfg =
  describe "Pickles.Step.Circuit (real data)" do
    it "Step circuit verifies real Wrap proof (Step → Wrap → Step)" \{ step0, wrap0 } -> do
      schnorrInput <- liftEffect $ randomSampleOne $ genValidSignature (Proxy @PallasG) (Proxy @4)
      let
        challengeDigest = computeStepChallengeDigest step0
        sgEvals = computeStepSgEvals step0
        params = Record.merge (buildStepFinalizeParams step0) (buildStepIVPParams wrap0)
        fopInput = buildStepFinalizeInput
          { prevChallengeDigest: challengeDigest
          , sgPointEvals: sgEvals
          , stepCtx: step0
          , wrapCtx: wrap0
          }

        -- Public input uses N=15 Wrap bp challenges, not N=16 FOP state
        wrapBpChals :: Vector WrapIPARounds (SizedF 128 (F StepField))
        wrapBpChals = coerce (extractWrapRawBpChallenges wrap0)
        fopDv = fopInput.unfinalized.deferredValues
        publicUnfinalized = type1ToType2SF
          { deferredValues:
              { plonk: fopDv.plonk
              , combinedInnerProduct: fopDv.combinedInnerProduct
              , xi: fopDv.xi
              , bulletproofChallenges: wrapBpChals
              , b: fopDv.b
              }
          , shouldFinalize: fopInput.unfinalized.shouldFinalize
          , spongeDigestBeforeEvaluations: fopInput.unfinalized.spongeDigestBeforeEvaluations
          }

        input :: StepSchnorrInput
        input =
          { appInput: schnorrInput
          , previousProofInputs: unit :< nil
          , unfinalizedProofs: publicUnfinalized :< nil
          , prevChallengeDigests: F challengeDigest :< nil
          }
        witnessData = buildStepProverWitness step0 wrap0
      let
        realCircuit
          :: forall t m
           . CircuitM StepField (KimchiConstraint StepField) t m
          => StepWitnessM 1 StepIPARounds WrapIPARounds m StepField
          => StepSchnorrInputVar
          -> Snarky (KimchiConstraint StepField) t m Unit
        realCircuit i = do
          _ <- stepCircuit @StepIPARounds params (stepSchnorrAppCircuit true) i
          pure unit

      let
        realCircuit'
          :: forall t
           . CircuitM StepField (KimchiConstraint StepField) t (StepProverM 1 StepIPARounds WrapIPARounds StepField)
          => StepSchnorrInputVar
          -> Snarky (KimchiConstraint StepField) t (StepProverM 1 StepIPARounds WrapIPARounds StepField) Unit
        realCircuit' = realCircuit
      void $ circuitTestM' @StepField
        (runStepProverM witnessData)
        cfg
        (NEA.singleton { testFunction: satisfied_, input: Exact (NEA.singleton input) })
        realCircuit'
