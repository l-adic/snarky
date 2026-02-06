module Test.Pickles.Step.FinalizeOtherProof
  ( spec
  , realDataSpec
  ) where

-- | Tests for the FinalizeOtherProof circuit.
-- |
-- | Two test scenarios:
-- | 1. Base case: dummy inputs with shouldFinalize = false (bootstrapping)
-- | 2. Real data: Schnorr proof data with shouldFinalize = true (all checks)

import Prelude

import Data.Identity (Identity)
import Data.Vector as Vector
import Effect.Aff (Aff)
import JS.BigInt as BigInt
import Pickles.IPA as IPA
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI (evalSelectorPolys, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.PlonkChecks.Permutation (permScalar)
import Pickles.PlonkChecks.XiCorrect (FrSpongeInput, emptyPrevChallengeDigest, frSpongeChallengesPure)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Sponge as Pickles.Sponge
import Pickles.Step.Dummy (dummyFinalizeOtherProofParams, dummyUnfinalizedProof, dummyWrapProofWitness)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofInput, FinalizeOtherProofParams, finalizeOtherProofCircuit)
import Pickles.Step.Types (BulletproofChallenges)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, SizedF, Snarky, assert_, coerceViaBits)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (endoScalar, pow)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Types.Shifted (Type1, toShifted)
import Test.Pickles.E2E (computePublicEval, createTestContext, mkIpaTestContext) as E2E
import Test.Pickles.ProofFFI as ProofFFI
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied_)
import Test.Spec (Spec, SpecT, beforeAll, describe, it)
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

-- | Standard Kimchi constants
zkRows :: Int
zkRows = 3

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
        , prevChallengeDigest: zero
        }

      -- | The circuit under test for base case: runs finalizeOtherProofCircuit and discards output
      dummyTestCircuit
        :: forall t
         . CircuitM StepField (KimchiConstraint StepField) t Identity
        => FinalizeOtherProofTestInputVar
        -> Snarky (KimchiConstraint StepField) t Identity Unit
      dummyTestCircuit x =
        void $ evalSpongeM initialSpongeCircuit (finalizeOtherProofCircuit dummyFinalizeOtherProofParams x)

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
-- | Real data test (all checks with Schnorr proof)
-------------------------------------------------------------------------------

-- | Shared test context, reusing the E2E setup.
type TestContext =
  { params :: FinalizeOtherProofParams StepField
  , input :: FinalizeOtherProofTestInput
  }

createTestContext :: Aff TestContext
createTestContext = do
  ctx <- E2E.createTestContext
  let
    endo = endoScalar @Vesta.BaseField @Vesta.ScalarField

    ---------------------------------------------------------------------------
    -- Proof polynomial evaluations
    ---------------------------------------------------------------------------
    witnessEvals = ProofFFI.proofWitnessEvals ctx.proof
    zEvals = ProofFFI.proofZEvals ctx.proof
    sigmaEvals = ProofFFI.proofSigmaEvals ctx.proof
    coeffEvals = ProofFFI.proofCoefficientEvals ctx.proof
    indexEvals = evalSelectorPolys ctx.proverIndex ctx.oracles.zeta

    -- Public evals
    publicEvals = { zeta: ctx.oracles.publicEvalZeta, omegaTimesZeta: ctx.oracles.publicEvalZetaOmega }

    ---------------------------------------------------------------------------
    -- Domain-dependent values
    ---------------------------------------------------------------------------
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    omega = ipaCtx.omega
    zetaToNMinus1 = pow ctx.oracles.zeta n - one
    zkPoly = ProofFFI.permutationVanishingPolynomial
      { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
    omegaToMinusZkRows = pow omega (n - BigInt.fromInt zkRows)
    vanishesOnZk = vanishesOnZkAndPreviousRows
      { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
    lagrangeFalse0 = unnormalizedLagrangeBasis
      { domainLog2: ctx.domainLog2, zkRows: 0, offset: 0, pt: ctx.oracles.zeta }
    lagrangeTrue1 = unnormalizedLagrangeBasis
      { domainLog2: ctx.domainLog2, zkRows, offset: -1, pt: ctx.oracles.zeta }

    ---------------------------------------------------------------------------
    -- Fr-sponge challenges (xi, evalscale)
    ---------------------------------------------------------------------------
    spongeInput :: FrSpongeInput Vesta.ScalarField
    spongeInput =
      { fqDigest: ctx.oracles.fqDigest
      , prevChallengeDigest: emptyPrevChallengeDigest
      , ftEval1: ctx.oracles.ftEval1
      , publicEvals
      , zEvals
      , indexEvals
      , witnessEvals
      , coeffEvals
      , sigmaEvals
      , endo
      }

    frChallenges = frSpongeChallengesPure spongeInput

    ---------------------------------------------------------------------------
    -- Perm scalar (pure, using expanded plonk values from oracles)
    ---------------------------------------------------------------------------
    permInput =
      { w: map _.zeta (Vector.take @7 witnessEvals)
      , sigma: map _.zeta sigmaEvals
      , z: zEvals
      , shifts: ProofFFI.proverIndexShifts ctx.proverIndex
      , alpha: ctx.oracles.alpha
      , beta: ctx.oracles.beta
      , gamma: ctx.oracles.gamma
      , zkPolynomial: zkPoly
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: ctx.oracles.zeta
      }
    perm = permScalar permInput

    ---------------------------------------------------------------------------
    -- IPA context (sponge state, expanded challenges, omega)
    ---------------------------------------------------------------------------
    ipaCtx = E2E.mkIpaTestContext ctx

    ---------------------------------------------------------------------------
    -- b value (from Rust FFI, using expanded bulletproof challenges)
    ---------------------------------------------------------------------------

    bValue = ProofFFI.computeB0
      { challenges: Vector.toUnfoldable ipaCtx.challenges
      , zeta: ctx.oracles.zeta
      , zetaOmega: ctx.oracles.zeta * ipaCtx.omega
      , evalscale: ctx.oracles.u
      }

    ---------------------------------------------------------------------------
    -- Bulletproof challenges (raw 128-bit from IPA sponge)
    ---------------------------------------------------------------------------

    bulletproofChallenges :: Vector.Vector 16 (SizedF 128 (F StepField))
    bulletproofChallenges =
      let
        lrPairs = ProofFFI.pallasProofOpeningLr ctx.proof

        -- Extract raw 128-bit challenges via pure sponge
        rawBpChallenges :: Vector.Vector 16 (SizedF 128 Pallas.ScalarField)
        rawBpChallenges = Pickles.Sponge.evalPureSpongeM ipaCtx.spongeState do
          _ <- Pickles.Sponge.squeeze -- squeeze for u first
          IPA.extractScalarChallengesPure (coerce lrPairs)

        -- Coerce from Pallas.ScalarField to Vesta.ScalarField, then wrap in F
        rawBpChallengesStep :: Vector.Vector 16 (SizedF 128 Vesta.ScalarField)
        rawBpChallengesStep = map coerceViaBits rawBpChallenges
      in
        coerce rawBpChallengesStep

    ---------------------------------------------------------------------------
    -- Public eval for ft
    ---------------------------------------------------------------------------
    publicEvalForFt = E2E.computePublicEval ctx.publicInputs ctx.domainLog2 ctx.oracles.zeta

    ---------------------------------------------------------------------------
    -- Build UnfinalizedProof with real deferred values
    ---------------------------------------------------------------------------
    plonkMinimal =
      { alpha: coerce ctx.oracles.alphaChal :: SizedF 128 (F StepField)
      , beta: F ctx.oracles.beta
      , gamma: F ctx.oracles.gamma
      , zeta: coerce ctx.oracles.zetaChal :: SizedF 128 (F StepField)
      }

    unfinalized =
      { deferredValues:
          { plonk: plonkMinimal
          , combinedInnerProduct: toShifted $ F ctx.oracles.combinedInnerProduct
          , xi: coerce frChallenges.rawXi
          , bulletproofChallenges
          , b: toShifted $ F bValue
          , perm: toShifted $ F perm
          }
      , shouldFinalize: true
      , spongeDigestBeforeEvaluations: F ctx.oracles.fqDigest
      }

    ---------------------------------------------------------------------------
    -- Build WrapProofWitness with real evaluations and domain values
    ---------------------------------------------------------------------------
    witness =
      { allEvals:
          { ftEval1: F ctx.oracles.ftEval1
          , publicEvals: coerce publicEvals
          , zEvals: coerce zEvals
          , indexEvals: coerce indexEvals
          , witnessEvals: coerce witnessEvals
          , coeffEvals: coerce coeffEvals
          , sigmaEvals: coerce sigmaEvals
          }
      , domainValues:
          { zkPolynomial: F zkPoly
          , zetaToNMinus1: F zetaToNMinus1
          , omegaToMinusZkRows: F omegaToMinusZkRows
          , vanishesOnZk: F vanishesOnZk
          , lagrangeFalse0: F lagrangeFalse0
          , lagrangeTrue1: F lagrangeTrue1
          }
      , publicEvalForFt: F publicEvalForFt
      }

    ---------------------------------------------------------------------------
    -- FinalizeOtherProofParams with real values
    ---------------------------------------------------------------------------
    params :: FinalizeOtherProofParams StepField
    params =
      { domain:
          { generator: ProofFFI.domainGenerator ctx.domainLog2
          , shifts: ProofFFI.proverIndexShifts ctx.proverIndex
          }
      , endo
      , zkRows
      , linearizationPoly: Linearization.pallas
      }

    input :: FinalizeOtherProofTestInput
    input =
      { unfinalized
      , witness
      , prevChallengeDigest: F (emptyPrevChallengeDigest :: Vesta.ScalarField)
      }

  pure { params, input }

realDataSpec :: SpecT Aff Unit Aff Unit
realDataSpec = beforeAll createTestContext $
  describe "Pickles.Step.FinalizeOtherProof (real data)" do
    it "all checks pass with real Schnorr proof data" \{ params, input } -> do
      let
        circuit
          :: forall t
           . CircuitM StepField (KimchiConstraint StepField) t Identity
          => FinalizeOtherProofTestInputVar
          -> Snarky (KimchiConstraint StepField) t Identity Unit
        circuit x = do
          { finalized } <- evalSpongeM initialSpongeCircuit (finalizeOtherProofCircuit params x)
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
