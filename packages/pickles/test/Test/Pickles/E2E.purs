module Test.Pickles.E2E (spec) where

-- | Wrap-side verifier circuit tests on real Step proof data.
-- | Each test compiles a circuit, provides real proof-derived inputs,
-- | and verifies constraint satisfaction.

import Prelude

import Data.Array as Array
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Exception.Unsafe (unsafeThrow)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.IPA (BCorrectInput, CheckBulletproofInput, IpaFinalCheckInput, bCorrect)
import Pickles.IPA as IPA
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI (evalCoefficientPolys, evalSelectorPolys, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.PlonkChecks (PlonkChecksInput, plonkChecksCircuit)
import Pickles.PlonkChecks.CombinedInnerProduct (BatchingScalars, CombinedInnerProductCheckInput, combinedInnerProductCheckCircuit)
import Pickles.PlonkChecks.FtEval (ftEval0Circuit)
import Pickles.PlonkChecks.GateConstraints (GateConstraintInput)
import Pickles.PlonkChecks.Permutation (PermutationInput, permScalar)
import Pickles.PlonkChecks.XiCorrect (FrSpongeInput, XiCorrectInput, emptyPrevChallengeDigest, frSpongeChallengesPure, xiCorrectCircuit)
import Pickles.Sponge (evalPureSpongeM, evalSpongeM, initialSponge, initialSpongeCircuit, liftSnarky)
import Pickles.Sponge as Pickles.Sponge
import Pickles.Verify (IncrementallyVerifyProofInput, IncrementallyVerifyProofParams, incrementallyVerifyProof, verify)
import Pickles.Verify.FqSpongeTranscript (FqSpongeInput, spongeTranscriptCircuit, spongeTranscriptPure)
import RandomOracle.Sponge (Sponge)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, SizedF, Snarky, assertEqual_, assert_, coerceViaBits, const_, false_, toField, wrapF)
import Snarky.Circuit.Kimchi (Type1(..), expandToEndoScalar, fromShifted, groupMapParams, toShifted)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (EndoScalar(..), curveParams, endoScalar, fromAffine, fromBigInt, generator, pow, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.ProofFFI as ProofFFI
import Test.Pickles.TestContext (VestaTestContext, computePublicEval, createVestaTestContext, mkIpaTestContext, zkRows)
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied, satisfied_)
import Test.Spec (SpecT, beforeAll, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Circuit tests
-------------------------------------------------------------------------------

-- | Circuit test for ftEval0Circuit.
-- | Verifies the in-circuit computation matches the Rust FFI ftEval0 value.
ftEval0CircuitTest :: VestaTestContext -> Aff Unit
ftEval0CircuitTest ctx = do
  let
    -- Get proof evaluations
    witnessEvals = ProofFFI.proofWitnessEvals ctx.proof
    zEvals = ProofFFI.proofZEvals ctx.proof
    sigmaEvals = ProofFFI.proofSigmaEvals ctx.proof
    shifts = ProofFFI.proverIndexShifts ctx.proverIndex
    coeffEvals = evalCoefficientPolys ctx.proverIndex ctx.oracles.zeta
    indexEvals = evalSelectorPolys ctx.proverIndex ctx.oracles.zeta

    -- Compute domain-related values
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    omega = ProofFFI.domainGenerator ctx.domainLog2
    zetaToNMinus1 = pow ctx.oracles.zeta n - one
    zkPoly = ProofFFI.permutationVanishingPolynomial
      { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
    omegaToMinusZkRows = pow omega (n - BigInt.fromInt zkRows)
    vanishesOnZk' = vanishesOnZkAndPreviousRows
      { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
    lagrangeFalse0 = unnormalizedLagrangeBasis
      { domainLog2: ctx.domainLog2, zkRows: 0, offset: 0, pt: ctx.oracles.zeta }
    lagrangeTrue1 = unnormalizedLagrangeBasis
      { domainLog2: ctx.domainLog2, zkRows, offset: -1, pt: ctx.oracles.zeta }

    -- Build permutation input
    permInput :: PermutationInput (F Vesta.ScalarField)
    permInput =
      { w: map (F <<< _.zeta) (Vector.take @7 witnessEvals)
      , sigma: map (F <<< _.zeta) sigmaEvals
      , z: { zeta: F zEvals.zeta, omegaTimesZeta: F zEvals.omegaTimesZeta }
      , shifts: map F shifts
      , alpha: F ctx.oracles.alpha
      , beta: F (toField ctx.oracles.beta)
      , gamma: F (toField ctx.oracles.gamma)
      , zkPolynomial: F zkPoly
      , zetaToNMinus1: F zetaToNMinus1
      , omegaToMinusZkRows: F omegaToMinusZkRows
      , zeta: F ctx.oracles.zeta
      }

    -- Build gate constraint input
    gateInput :: GateConstraintInput (F Vesta.ScalarField)
    gateInput =
      { witnessEvals: coerce witnessEvals
      , coeffEvals: coerce coeffEvals
      , indexEvals: coerce indexEvals
      , alpha: F ctx.oracles.alpha
      , beta: F (toField ctx.oracles.beta)
      , gamma: F (toField ctx.oracles.gamma)
      , jointCombiner: F zero
      , vanishesOnZk: F vanishesOnZk'
      , lagrangeFalse0: F lagrangeFalse0
      , lagrangeTrue1: F lagrangeTrue1
      }

    -- Public eval (computed same as pure test)
    publicEval :: F Vesta.ScalarField
    publicEval = F $ computePublicEval ctx.publicInputs ctx.domainLog2 ctx.oracles.zeta

    -- Expected result from FFI
    expected :: F Vesta.ScalarField
    expected = F ctx.oracles.ftEval0

    -- Circuit input tuple
    circuitInput = { permInput, gateInput, publicEval }

    -- The circuit computes ftEval0 and asserts it equals the expected value
    circuit
      :: forall t m
       . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
      => { permInput :: PermutationInput (FVar Vesta.ScalarField)
         , gateInput :: GateConstraintInput (FVar Vesta.ScalarField)
         , publicEval :: FVar Vesta.ScalarField
         }
      -> Snarky (KimchiConstraint Vesta.ScalarField) t m Unit
    circuit input = do
      result <- ftEval0Circuit Linearization.pallas input
      assertEqual_ result (const_ (un F expected))

  circuitSpecPureInputs
    { builtState: compilePure
        ( Proxy
            @{ permInput :: PermutationInput (F Vesta.ScalarField)
            , gateInput :: GateConstraintInput (F Vesta.ScalarField)
            , publicEval :: F Vesta.ScalarField
            }
        )
        (Proxy @Unit)
        (Proxy @(KimchiConstraint Vesta.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit
    , testFunction: satisfied_
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

-- | Circuit test for combined_inner_product_correct.
-- | Computes ftEval0 in-circuit, feeds into combinedInnerProductCircuit,
-- | asserts result equals ctx.oracles.combinedInnerProduct.
combinedInnerProductCorrectCircuitTest :: VestaTestContext -> Aff Unit
combinedInnerProductCorrectCircuitTest ctx = do
  let
    -- Shared values used in multiple places
    witnessEvals = ProofFFI.proofWitnessEvals ctx.proof
    zEvals = ProofFFI.proofZEvals ctx.proof
    sigmaEvals = ProofFFI.proofSigmaEvals ctx.proof
    indexEvals = evalSelectorPolys ctx.proverIndex ctx.oracles.zeta
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    omega = ProofFFI.domainGenerator ctx.domainLog2

    -- Batching scalars (from Fiat-Shamir in real verification)
    scalars :: BatchingScalars (F Vesta.ScalarField)
    scalars =
      { polyscale: F ctx.oracles.v
      , evalscale: F ctx.oracles.u
      }

    -- Evaluation data
    evalInput :: CombinedInnerProductCheckInput (F Vesta.ScalarField)
    evalInput =
      { permInput:
          { w: map (F <<< _.zeta) (Vector.take @7 witnessEvals)
          , sigma: map (F <<< _.zeta) sigmaEvals
          , z: coerce zEvals
          , shifts: map F (ProofFFI.proverIndexShifts ctx.proverIndex)
          , alpha: F ctx.oracles.alpha
          , beta: F (toField ctx.oracles.beta)
          , gamma: F (toField ctx.oracles.gamma)
          , zkPolynomial: F $ ProofFFI.permutationVanishingPolynomial
              { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
          , zetaToNMinus1: F $ pow ctx.oracles.zeta n - one
          , omegaToMinusZkRows: F $ pow omega (n - BigInt.fromInt zkRows)
          , zeta: F ctx.oracles.zeta
          }
      , gateInput:
          { witnessEvals: coerce witnessEvals
          , coeffEvals: coerce (evalCoefficientPolys ctx.proverIndex ctx.oracles.zeta)
          , indexEvals: coerce indexEvals
          , alpha: F ctx.oracles.alpha
          , beta: F (toField ctx.oracles.beta)
          , gamma: F (toField ctx.oracles.gamma)
          , jointCombiner: F zero
          , vanishesOnZk: F $ vanishesOnZkAndPreviousRows
              { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
          , lagrangeFalse0: F $ unnormalizedLagrangeBasis
              { domainLog2: ctx.domainLog2, zkRows: 0, offset: 0, pt: ctx.oracles.zeta }
          , lagrangeTrue1: F $ unnormalizedLagrangeBasis
              { domainLog2: ctx.domainLog2, zkRows, offset: -1, pt: ctx.oracles.zeta }
          }
      , publicEvalForFt: F $ computePublicEval ctx.publicInputs ctx.domainLog2 ctx.oracles.zeta
      , publicPointEval: { zeta: F ctx.oracles.publicEvalZeta, omegaTimesZeta: F ctx.oracles.publicEvalZetaOmega }
      , ftEval1: F ctx.oracles.ftEval1
      , zEvals: coerce zEvals
      , indexEvals: coerce indexEvals
      , witnessEvals: coerce witnessEvals
      , coeffEvals: coerce (ProofFFI.proofCoefficientEvals ctx.proof)
      , sigmaEvals: coerce sigmaEvals
      }

    -- Combined input for the test framework
    circuitInput :: Tuple (BatchingScalars (F Vesta.ScalarField)) (CombinedInnerProductCheckInput (F Vesta.ScalarField))
    circuitInput = Tuple scalars evalInput

    circuit
      :: forall t m
       . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
      => Tuple (BatchingScalars (FVar Vesta.ScalarField)) (CombinedInnerProductCheckInput (FVar Vesta.ScalarField))
      -> Snarky (KimchiConstraint Vesta.ScalarField) t m Unit
    circuit (Tuple s input) = do
      cipResult <- combinedInnerProductCheckCircuit Linearization.pallas s input
      assertEqual_ cipResult (const_ ctx.oracles.combinedInnerProduct)

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(Tuple (BatchingScalars (F Vesta.ScalarField)) (CombinedInnerProductCheckInput (F Vesta.ScalarField))))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint Vesta.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit
    , testFunction: satisfied_
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

-- | Circuit test for xi_correct.
-- | Replays Fr-sponge in-circuit and asserts equality with claimed xi.
xiCorrectCircuitTest :: VestaTestContext -> Aff Unit
xiCorrectCircuitTest ctx = do
  let
    -- Get proof evaluations
    witnessEvals = ProofFFI.proofWitnessEvals ctx.proof
    zEvals = ProofFFI.proofZEvals ctx.proof
    sigmaEvals = ProofFFI.proofSigmaEvals ctx.proof
    coeffEvals = ProofFFI.proofCoefficientEvals ctx.proof
    indexEvals = evalSelectorPolys ctx.proverIndex ctx.oracles.zeta

    -- First compute the raw xi challenge using pure sponge
    spongeInput :: FrSpongeInput Vesta.ScalarField
    spongeInput =
      { fqDigest: ctx.oracles.fqDigest
      , prevChallengeDigest: emptyPrevChallengeDigest
      , ftEval1: ctx.oracles.ftEval1
      , publicEvals: { zeta: ctx.oracles.publicEvalZeta, omegaTimesZeta: ctx.oracles.publicEvalZetaOmega }
      , zEvals
      , indexEvals
      , witnessEvals
      , coeffEvals
      , sigmaEvals
      , endo: let EndoScalar e = endoScalar @Vesta.BaseField @Vesta.ScalarField in e
      }
    pureResult = frSpongeChallengesPure spongeInput

  -- First verify our pure computation matches Rust's expanded values
  liftEffect $ pureResult.xi `shouldEqual` ctx.oracles.v
  liftEffect $ pureResult.evalscale `shouldEqual` ctx.oracles.u

  let
    circuitInput :: XiCorrectInput (F Vesta.ScalarField)
    circuitInput =
      { fqDigest: F ctx.oracles.fqDigest
      , prevChallengeDigest: F emptyPrevChallengeDigest
      , ftEval1: F ctx.oracles.ftEval1
      , publicEvals: coerce { zeta: ctx.oracles.publicEvalZeta, omegaTimesZeta: ctx.oracles.publicEvalZetaOmega }
      , zEvals: coerce zEvals
      , indexEvals: coerce indexEvals
      , witnessEvals: coerce witnessEvals
      , coeffEvals: coerce coeffEvals
      , sigmaEvals: coerce sigmaEvals
      , endo: let EndoScalar e = endoScalar @Vesta.BaseField @Vesta.ScalarField in F e
      , claimedXi: coerce pureResult.rawXi -- use the verified raw challenge
      }

    circuit
      :: forall t m
       . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
      => XiCorrectInput (FVar Vesta.ScalarField)
      -> Snarky (KimchiConstraint Vesta.ScalarField) t m Unit
    circuit input = void $ evalSpongeM initialSpongeCircuit (xiCorrectCircuit input)

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(XiCorrectInput (F Vesta.ScalarField)))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint Vesta.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit
    , testFunction: satisfied_
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

-- | Circuit test for plonkChecksCircuit.
-- | This tests the composed circuit that verifies xi, derives evalscale,
-- | and computes combined_inner_product all in one circuit.
plonkChecksCircuitTest :: VestaTestContext -> Aff Unit
plonkChecksCircuitTest ctx = do
  let
    -- Get proof evaluations
    witnessEvals = ProofFFI.proofWitnessEvals ctx.proof
    zEvals = ProofFFI.proofZEvals ctx.proof
    sigmaEvals = ProofFFI.proofSigmaEvals ctx.proof
    coeffEvals = ProofFFI.proofCoefficientEvals ctx.proof
    indexEvals = evalSelectorPolys ctx.proverIndex ctx.oracles.zeta
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    omega = ProofFFI.domainGenerator ctx.domainLog2

    -- Compute raw challenges using pure sponge
    spongeInput :: FrSpongeInput Vesta.ScalarField
    spongeInput =
      { fqDigest: ctx.oracles.fqDigest
      , prevChallengeDigest: emptyPrevChallengeDigest
      , ftEval1: ctx.oracles.ftEval1
      , publicEvals: { zeta: ctx.oracles.publicEvalZeta, omegaTimesZeta: ctx.oracles.publicEvalZetaOmega }
      , zEvals
      , indexEvals
      , witnessEvals
      , coeffEvals
      , sigmaEvals
      , endo: let EndoScalar e = endoScalar @Vesta.BaseField @Vesta.ScalarField in e
      }
    pureResult = frSpongeChallengesPure spongeInput

  -- First verify our pure computation matches Rust's expanded values
  liftEffect $ pureResult.xi `shouldEqual` ctx.oracles.v
  liftEffect $ pureResult.evalscale `shouldEqual` ctx.oracles.u

  let

    -- Build the CombinedInnerProductCheckInput
    -- Note: polyscale and evalscale are derived by the circuit, not provided here
    cipInput :: CombinedInnerProductCheckInput (F Vesta.ScalarField)
    cipInput =
      { permInput:
          { w: map (F <<< _.zeta) (Vector.take @7 witnessEvals)
          , sigma: map (F <<< _.zeta) sigmaEvals
          , z: coerce zEvals
          , shifts: map F (ProofFFI.proverIndexShifts ctx.proverIndex)
          , alpha: F ctx.oracles.alpha
          , beta: F (toField ctx.oracles.beta)
          , gamma: F (toField ctx.oracles.gamma)
          , zkPolynomial: F $ ProofFFI.permutationVanishingPolynomial
              { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
          , zetaToNMinus1: F $ pow ctx.oracles.zeta n - one
          , omegaToMinusZkRows: F $ pow omega (n - BigInt.fromInt zkRows)
          , zeta: F ctx.oracles.zeta
          }
      , gateInput:
          { witnessEvals: coerce witnessEvals
          , coeffEvals: coerce (evalCoefficientPolys ctx.proverIndex ctx.oracles.zeta)
          , indexEvals: coerce indexEvals
          , alpha: F ctx.oracles.alpha
          , beta: F (toField ctx.oracles.beta)
          , gamma: F (toField ctx.oracles.gamma)
          , jointCombiner: F zero
          , vanishesOnZk: F $ vanishesOnZkAndPreviousRows
              { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
          , lagrangeFalse0: F $ unnormalizedLagrangeBasis
              { domainLog2: ctx.domainLog2, zkRows: 0, offset: 0, pt: ctx.oracles.zeta }
          , lagrangeTrue1: F $ unnormalizedLagrangeBasis
              { domainLog2: ctx.domainLog2, zkRows, offset: -1, pt: ctx.oracles.zeta }
          }
      , publicEvalForFt: F $ computePublicEval ctx.publicInputs ctx.domainLog2 ctx.oracles.zeta
      , publicPointEval: { zeta: F ctx.oracles.publicEvalZeta, omegaTimesZeta: F ctx.oracles.publicEvalZetaOmega }
      , ftEval1: F ctx.oracles.ftEval1
      , zEvals: coerce zEvals
      , indexEvals: coerce indexEvals
      , witnessEvals: coerce witnessEvals
      , coeffEvals: coerce coeffEvals
      , sigmaEvals: coerce sigmaEvals
      }

    -- Build the PlonkChecksInput
    circuitInput :: PlonkChecksInput (F Vesta.ScalarField)
    circuitInput =
      { allEvals:
          { ftEval1: F ctx.oracles.ftEval1
          , publicEvals: coerce { zeta: ctx.oracles.publicEvalZeta, omegaTimesZeta: ctx.oracles.publicEvalZetaOmega }
          , zEvals: coerce zEvals
          , indexEvals: coerce indexEvals
          , witnessEvals: coerce witnessEvals
          , coeffEvals: coerce coeffEvals
          , sigmaEvals: coerce sigmaEvals
          }
      , endo: let EndoScalar e = endoScalar @Vesta.BaseField @Vesta.ScalarField in F e
      , claimedXi: coerce pureResult.rawXi -- raw 128-bit challenge
      , claimedR: coerce pureResult.rawR -- raw 128-bit challenge
      , cipInput
      }

    -- Build initial sponge state with fqDigest and prevChallengeDigest absorbed
    initialSpongeWithDigests :: Pickles.Sponge.PureSpongeM Vesta.ScalarField Unit
    initialSpongeWithDigests = do
      Pickles.Sponge.absorb ctx.oracles.fqDigest
      Pickles.Sponge.absorb (emptyPrevChallengeDigest :: Vesta.ScalarField)

    -- Get the sponge state after absorbing digests
    spongeStateAfterDigests :: Sponge Vesta.ScalarField
    spongeStateAfterDigests =
      let
        Tuple _ s = Pickles.Sponge.runPureSpongeM Pickles.Sponge.initialSponge initialSpongeWithDigests
      in
        s

    circuit
      :: forall t m
       . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
      => PlonkChecksInput (FVar Vesta.ScalarField)
      -> Snarky (KimchiConstraint Vesta.ScalarField) t m Unit
    circuit input = do
      -- Start with sponge that has fqDigest and prevChallengeDigest absorbed
      output <- evalSpongeM (Pickles.Sponge.spongeFromConstants spongeStateAfterDigests) $
        plonkChecksCircuit Linearization.pallas input
      -- Verify outputs match expected values
      assertEqual_ output.polyscale (const_ ctx.oracles.v)
      assertEqual_ output.evalscale (const_ ctx.oracles.u)
      assertEqual_ output.combinedInnerProduct (const_ ctx.oracles.combinedInnerProduct)

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(PlonkChecksInput (F Vesta.ScalarField)))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint Vesta.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit
    , testFunction: satisfied_
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

-- | Test that bCorrectCircuit verifies using Rust-provided values.
-- | Uses circuitSpec infrastructure to verify constraint satisfaction.
bCorrectCircuitTest :: VestaTestContext -> Aff Unit
bCorrectCircuitTest ctx = do
  let
    { challenges, omega } = mkIpaTestContext ctx
    zetaOmega = ctx.oracles.zeta * omega

    circuitInput :: BCorrectInput 16 (F Vesta.ScalarField)
    circuitInput =
      { challenges: coerce challenges
      , zeta: F ctx.oracles.zeta
      , zetaOmega: F zetaOmega
      , evalscale: F ctx.oracles.u
      , expectedB: F $ ProofFFI.computeB0
          { challenges: Vector.toUnfoldable challenges
          , zeta: ctx.oracles.zeta
          , zetaOmega
          , evalscale: ctx.oracles.u
          }
      }

    circuit
      :: forall t m
       . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
      => BCorrectInput 16 (FVar Vesta.ScalarField)
      -> Snarky (KimchiConstraint Vesta.ScalarField) t m (BoolVar Vesta.ScalarField)
    circuit = IPA.bCorrectCircuit

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(BCorrectInput 16 (F Vesta.ScalarField)))
        (Proxy @Boolean)
        (Proxy @(KimchiConstraint Vesta.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit
    , testFunction: satisfied bCorrect
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

-- | In-circuit test for challenge extraction.
-- | Circuit runs over Pallas.ScalarField (Fq) where the sponge operates.
-- | Extracts 128-bit scalar challenges, verifies circuit matches pure sponge,
-- | and validates endo-mapped values match Rust.
extractChallengesCircuitTest :: VestaTestContext -> Aff Unit
extractChallengesCircuitTest ctx = do
  let
    { spongeState, challenges: rustChallenges } = mkIpaTestContext ctx

    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => Vector 16 (IPA.LrPair (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m (Vector 16 (SizedF 128 (FVar Pallas.ScalarField)))
    circuit pairs =
      Pickles.Sponge.evalSpongeM (Pickles.Sponge.spongeFromConstants spongeState) do
        _ <- Pickles.Sponge.squeeze -- Squeeze for u first
        IPA.extractScalarChallenges pairs

    testFn :: Vector 16 (IPA.LrPair (F Pallas.ScalarField)) -> Vector 16 (SizedF 128 (F Pallas.ScalarField))
    testFn pairs =
      let
        challenges :: Vector 16 (SizedF 128 Pallas.ScalarField)
        challenges = Pickles.Sponge.evalPureSpongeM spongeState do
          _ <- Pickles.Sponge.squeeze
          IPA.extractScalarChallengesPure (coerce pairs)

        endoMappedChallenges :: Array Pallas.BaseField
        endoMappedChallenges = Vector.toUnfoldable $ map
          (\c -> expandToEndoScalar c :: Pallas.BaseField)
          challenges
      in
        if endoMappedChallenges /= Vector.toUnfoldable rustChallenges then unsafeThrow "unexpected endoMappedChallenges"
        else coerce challenges

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(Vector 16 (IPA.LrPair (F Pallas.ScalarField))))
        (Proxy @(Vector 16 (SizedF 128 (F Pallas.ScalarField))))
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied testFn
    , postCondition: Kimchi.postCondition
    }
    [ coerce $ ProofFFI.pallasProofOpeningLr ctx.proof ]

-- | In-circuit test for bullet reduce (lr_prod computation).
-- | Circuit runs over Pallas.ScalarField (Fq) where the L/R points are.
-- | Extracts 128-bit scalar challenges, computes lr_prod, and verifies
-- | result matches Rust FFI.
bulletReduceCircuitTest :: VestaTestContext -> Aff Unit
bulletReduceCircuitTest ctx = do
  let
    { spongeState } = mkIpaTestContext ctx

    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => Vector 16 (IPA.LrPair (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m (AffinePoint (FVar Pallas.ScalarField))
    circuit pairs =
      Pickles.Sponge.evalSpongeM (Pickles.Sponge.spongeFromConstants spongeState) do
        _ <- Pickles.Sponge.squeeze
        challenges <- IPA.extractScalarChallenges pairs
        { p } <- liftSnarky $ IPA.bulletReduceCircuit @Pallas.ScalarField @Vesta.G { pairs, challenges }
        pure p

    testFn :: Vector 16 (IPA.LrPair (F Pallas.ScalarField)) -> AffinePoint (F Pallas.ScalarField)
    testFn pairs =
      let
        challenges :: Vector 16 (SizedF 128 Pallas.ScalarField)
        challenges = Pickles.Sponge.evalPureSpongeM spongeState do
          _ <- Pickles.Sponge.squeeze
          IPA.extractScalarChallengesPure (coerce pairs)

        lrProd :: Vesta.G
        lrProd = IPA.bulletReduce @Pallas.ScalarField @Vesta.G { pairs: coerce pairs, challenges }
        computedAffine = unsafePartial $ fromJust $ toAffine lrProd
        expectedLrProd = ProofFFI.pallasProofLrProd ctx.verifierIndex
          { proof: ctx.proof, publicInput: ctx.publicInputs }
      in
        if computedAffine /= expectedLrProd then unsafeThrow "bulletReduce lr_prod doesn't match Rust"
        else coerce computedAffine

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(Vector 16 (IPA.LrPair (F Pallas.ScalarField))))
        (Proxy @(AffinePoint (F Pallas.ScalarField)))
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied testFn
    , postCondition: Kimchi.postCondition
    }
    [ coerce $ ProofFFI.pallasProofOpeningLr ctx.proof ]

-- | In-circuit test for IPA final check.
-- | Tests the full IPA verification equation: c*Q + delta = z1*(sg + b*u) + z2*H
ipaFinalCheckCircuitTest :: VestaTestContext -> Aff Unit
ipaFinalCheckCircuitTest ctx = do
  let
    { challenges, spongeState, combinedPolynomial, omega } = mkIpaTestContext ctx

    circuitInput :: IpaFinalCheckInput 16 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
    circuitInput =
      { delta: coerce $ ProofFFI.pallasProofOpeningDelta ctx.proof
      , sg: coerce $ ProofFFI.pallasProofOpeningSg ctx.proof
      , lr: coerce $ ProofFFI.pallasProofOpeningLr ctx.proof
      , z1: toShifted $ F $ ProofFFI.pallasProofOpeningZ1 ctx.proof
      , z2: toShifted $ F $ ProofFFI.pallasProofOpeningZ2 ctx.proof
      , combinedPolynomial: coerce combinedPolynomial
      , combinedInnerProduct: toShifted $ F ctx.oracles.combinedInnerProduct
      , b: toShifted $ F $ ProofFFI.computeB0
          { challenges: Vector.toUnfoldable challenges
          , zeta: ctx.oracles.zeta
          , zetaOmega: ctx.oracles.zeta * omega
          , evalscale: ctx.oracles.u
          }
      , blindingGenerator: coerce $ ProofFFI.pallasProverIndexBlindingGenerator ctx.verifierIndex
      }

    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => IpaFinalCheckInput 16 (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
    circuit input = do
      { success } <- evalSpongeM (Pickles.Sponge.spongeFromConstants spongeState) $
        IPA.ipaFinalCheckCircuit @Pallas.ScalarField @Vesta.G
          IPA.type1ScalarOps
          (groupMapParams $ Proxy @Vesta.G)
          input
      assert_ success

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(IpaFinalCheckInput 16 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied_
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

-- | Debug verification test: prints intermediate IPA values to stderr.
-- | Also tests scaleFast1 with z1 and the generator point.
debugVerifyTest :: VestaTestContext -> Aff Unit
debugVerifyTest ctx = do
  let
    _ = ProofFFI.pallasDebugVerify ctx.verifierIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    z1Raw = ProofFFI.pallasProofOpeningZ1 ctx.proof

    z1Shifted :: Type1 (F Pallas.ScalarField)
    z1Shifted = toShifted (F z1Raw)

    z1Recovered :: F Pallas.BaseField
    z1Recovered = fromShifted z1Shifted

    genPoint = unsafePartial fromJust $ toAffine (generator @_ @Vesta.G)
    expectedAffine = unsafePartial fromJust $ toAffine $ scalarMul z1Raw (generator @_ @Vesta.G)

  liftEffect do
    log $ "z1Raw from FFI: " <> show z1Raw
    log $ "z1Shifted (Type1 t): " <> show z1Shifted
    log $ "z1Recovered (fromShifted): " <> show z1Recovered
    log $ "Roundtrip matches: " <> show (F z1Raw == z1Recovered)
    log $ "Expected z1*G: (" <> show expectedAffine.x <> ", " <> show expectedAffine.y <> ")"

  let
    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => Tuple (AffinePoint (FVar Pallas.ScalarField)) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m (AffinePoint (FVar Pallas.ScalarField))
    circuit (Tuple p t) = IPA.type1ScalarOps.scaleByShifted p t

    testFn
      :: Tuple (AffinePoint (F Pallas.ScalarField)) (Type1 (F Pallas.ScalarField))
      -> AffinePoint (F Pallas.ScalarField)
    testFn (Tuple p scalar_) =
      let
        scalar :: Pallas.BaseField
        scalar = case fromShifted scalar_ of F a -> a
      in
        coerce $ unsafePartial fromJust $ toAffine @Pallas.ScalarField $
          scalarMul scalar (fromAffine @Pallas.ScalarField @Vesta.G (coerce p))

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(Tuple (AffinePoint (F Pallas.ScalarField)) (Type1 (F Pallas.ScalarField))))
        (Proxy @(AffinePoint (F Pallas.ScalarField)))
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied testFn
    , postCondition: Kimchi.postCondition
    }
    [ Tuple (coerce genPoint) z1Shifted ]

  liftEffect $ log "scaleFast1 mini test passed!"

-- | Full bulletproof check test: composes sponge transcript → checkBulletproof.
-- | Tests the "right half" of incrementallyVerifyProof.
checkBulletproofTest :: VestaTestContext -> Aff Unit
checkBulletproofTest ctx = do
  let
    commitments = ProofFFI.pallasProofCommitments ctx.proof
    publicComm = unsafePartial fromJust $ Array.head $
      ProofFFI.pallasPublicComm ctx.verifierIndex ctx.publicInputs
    ftComm = ProofFFI.pallasFtComm ctx.verifierIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }
    columnCommsRaw = ProofFFI.pallasVerifierIndexColumnComms ctx.verifierIndex

    indexComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    indexComms = unsafePartial fromJust $ Vector.toVector $ Array.take 6 columnCommsRaw

    coeffComms :: Vector 15 (AffinePoint Pallas.ScalarField)
    coeffComms = unsafePartial fromJust $ Vector.toVector $ Array.take 15 $ Array.drop 6 columnCommsRaw

    sigmaComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    sigmaComms = unsafePartial fromJust $ Vector.toVector $ Array.drop 21 columnCommsRaw

    -- Assemble all 45 commitment bases in to_batch order (as circuit variables)
    allBases :: Vector 45 (AffinePoint (FVar Pallas.ScalarField))
    allBases = map constPt $
      (publicComm :< ftComm :< commitments.zComm :< Vector.nil)
        `Vector.append` indexComms
        `Vector.append` commitments.wComm
        `Vector.append` coeffComms
        `Vector.append` sigmaComms

    -- xi from oracles (convert from Fp to Fq representation)
    xiChalFq :: SizedF 128 Pallas.ScalarField
    xiChalFq = coerceViaBits ctx.oracles.vChal

    omega = ProofFFI.domainGenerator ctx.domainLog2

    -- Sponge input for transcript (constant data)
    spongeInput :: FqSpongeInput 0 7 Pallas.ScalarField
    spongeInput =
      { indexDigest: ProofFFI.pallasVerifierIndexDigest ctx.verifierIndex
      , sgOld: Vector.nil
      , publicComm
      , wComm: commitments.wComm
      , zComm: commitments.zComm
      , tComm: unsafePartial fromJust $ Vector.toVector @7 commitments.tComm
      }

    -- Convert sponge input to circuit constants
    constPt :: AffinePoint Pallas.ScalarField -> AffinePoint (FVar Pallas.ScalarField)
    constPt { x, y } = { x: const_ x, y: const_ y }

    spongeInputCircuit :: FqSpongeInput 0 7 (FVar Pallas.ScalarField)
    spongeInputCircuit =
      { indexDigest: const_ spongeInput.indexDigest
      , sgOld: Vector.nil
      , publicComm: constPt spongeInput.publicComm
      , wComm: map constPt spongeInput.wComm
      , zComm: constPt spongeInput.zComm
      , tComm: map constPt spongeInput.tComm
      }

    -- Rust ground truth for bulletproof challenges
    rustChallenges :: Vector 16 Vesta.ScalarField
    rustChallenges = unsafePartial fromJust $ Vector.toVector $
      ProofFFI.proofBulletproofChallenges ctx.verifierIndex
        { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Build circuit input for checkBulletproof
    circuitInput :: CheckBulletproofInput 16 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
    circuitInput =
      { xi: coerce xiChalFq
      , delta: coerce $ ProofFFI.pallasProofOpeningDelta ctx.proof
      , sg: coerce $ ProofFFI.pallasProofOpeningSg ctx.proof
      , lr: coerce $ ProofFFI.pallasProofOpeningLr ctx.proof
      , z1: toShifted $ F $ ProofFFI.pallasProofOpeningZ1 ctx.proof
      , z2: toShifted $ F $ ProofFFI.pallasProofOpeningZ2 ctx.proof
      , combinedInnerProduct: toShifted $ F ctx.oracles.combinedInnerProduct
      , b: toShifted $ F $ ProofFFI.computeB0
          { challenges: Vector.toUnfoldable rustChallenges
          , zeta: ctx.oracles.zeta
          , zetaOmega: ctx.oracles.zeta * omega
          , evalscale: ctx.oracles.u
          }
      , blindingGenerator: coerce $ ProofFFI.pallasProverIndexBlindingGenerator ctx.verifierIndex
      }

    -- Circuit returns extracted challenges (for validation against Rust)
    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => CheckBulletproofInput 16 (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m (Vector 16 (SizedF 128 (FVar Pallas.ScalarField)))
    circuit input = do
      { success, challenges } <- evalSpongeM initialSpongeCircuit do
        _ <- spongeTranscriptCircuit spongeInputCircuit
        IPA.checkBulletproof @Pallas.ScalarField @Vesta.G
          IPA.type1ScalarOps
          (groupMapParams $ Proxy @Vesta.G)
          allBases
          input
      assert_ success
      pure challenges

    -- Pure test function: replays sponge, extracts challenges, validates against Rust FFI
    testFn
      :: CheckBulletproofInput 16 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
      -> Vector 16 (SizedF 128 (F Pallas.ScalarField))
    testFn input =
      let
        -- Run pure sponge: transcript → absorb CIP → squeeze u → extract challenges
        challenges :: Vector 16 (SizedF 128 Pallas.ScalarField)
        challenges = evalPureSpongeM initialSponge do
          _ <- spongeTranscriptPure spongeInput
          -- Absorb CIP (same as checkBulletproof does)
          let Type1 (F cipField) = input.combinedInnerProduct
          Pickles.Sponge.absorb cipField
          -- Squeeze for u (consumed by ipaFinalCheckCircuit)
          _ <- Pickles.Sponge.squeeze
          -- Extract scalar challenges from LR pairs
          IPA.extractScalarChallengesPure (coerce input.lr)

        -- Endo-expand to full field elements and validate against Rust
        endoMapped :: Array Pallas.BaseField
        endoMapped = Vector.toUnfoldable $ map
          (\c -> expandToEndoScalar c :: Pallas.BaseField)
          challenges

        -- Verify challenge polynomial commitment matches proof sg
        computedSg = ProofFFI.pallasChallengePolyCommitment ctx.verifierIndex endoMapped
        expectedSg = ProofFFI.pallasProofOpeningSg ctx.proof
      in
        if endoMapped /= Vector.toUnfoldable rustChallenges then unsafeThrow "checkBulletproof: extracted challenges don't match Rust"
        else if computedSg /= expectedSg then unsafeThrow "checkBulletproof: challenge poly commitment doesn't match proof sg"
        else coerce challenges

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(CheckBulletproofInput 16 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))))
        (Proxy @(Vector 16 (SizedF 128 (F Pallas.ScalarField))))
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied testFn
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

-------------------------------------------------------------------------------
-- | incrementallyVerifyProof test
-------------------------------------------------------------------------------

-- | Full incrementallyVerifyProof circuit test.
-- | Wires together publicInputCommitment, sponge transcript, ftComm, and
-- | checkBulletproof in a single circuit and verifies satisfiability.
incrementallyVerifyProofTest :: VestaTestContext -> Aff Unit
incrementallyVerifyProofTest ctx = do
  let
    commitments = ProofFFI.pallasProofCommitments ctx.proof
    numPublic = Array.length ctx.publicInputs
    columnCommsRaw = ProofFFI.pallasVerifierIndexColumnComms ctx.verifierIndex

    indexComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    indexComms = unsafePartial fromJust $ Vector.toVector $ Array.take 6 columnCommsRaw

    coeffComms :: Vector 15 (AffinePoint Pallas.ScalarField)
    coeffComms = unsafePartial fromJust $ Vector.toVector $ Array.take 15 $ Array.drop 6 columnCommsRaw

    sigmaComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    sigmaComms = unsafePartial fromJust $ Vector.toVector $ Array.drop 21 columnCommsRaw

    -- Build params (compile-time constants)
    params :: IncrementallyVerifyProofParams 9 Pallas.ScalarField
    params =
      { curveParams: curveParams (Proxy @Vesta.G)
      , lagrangeComms: unsafePartial fromJust $ Vector.toVector $
          coerce (ProofFFI.pallasLagrangeCommitments ctx.verifierIndex numPublic)
      , blindingH: coerce $ ProofFFI.pallasProverIndexBlindingGenerator ctx.verifierIndex
      , sigmaCommLast: coerce $ ProofFFI.pallasSigmaCommLast ctx.verifierIndex
      , columnComms:
          { index: coerce indexComms
          , coeff: coerce coeffComms
          , sigma: coerce sigmaComms
          }
      , indexDigest: ProofFFI.pallasVerifierIndexDigest ctx.verifierIndex
      }

    -- Compute deferred values from oracles
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    maxPolySize = ProofFFI.pallasVerifierIndexMaxPolySize ctx.verifierIndex
    omega = ProofFFI.domainGenerator ctx.domainLog2

    -- Perm scalar (pure, using expanded plonk values from oracles)
    zetaToNMinus1 = pow ctx.oracles.zeta n - one
    zkPoly = ProofFFI.permutationVanishingPolynomial
      { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
    omegaToMinusZkRows = pow omega (n - BigInt.fromInt zkRows)
    permInput =
      { w: map _.zeta (Vector.take @7 (ProofFFI.proofWitnessEvals ctx.proof))
      , sigma: map _.zeta (ProofFFI.proofSigmaEvals ctx.proof)
      , z: ProofFFI.proofZEvals ctx.proof
      , shifts: ProofFFI.proverIndexShifts ctx.proverIndex
      , alpha: ctx.oracles.alpha
      , beta: toField ctx.oracles.beta
      , gamma: toField ctx.oracles.gamma
      , zkPolynomial: zkPoly
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: ctx.oracles.zeta
      }
    perm = permScalar permInput

    -- b value from FFI
    { challenges: rustChallenges } = mkIpaTestContext ctx
    bValue = ProofFFI.computeB0
      { challenges: Vector.toUnfoldable rustChallenges
      , zeta: ctx.oracles.zeta
      , zetaOmega: ctx.oracles.zeta * omega
      , evalscale: ctx.oracles.u
      }

    -- Bulletproof challenges (raw 128-bit from IPA sponge, coerced to Fq)
    { spongeState } = mkIpaTestContext ctx

    rawBpChallenges :: Vector 16 (SizedF 128 Pallas.ScalarField)
    rawBpChallenges = Pickles.Sponge.evalPureSpongeM spongeState do
      _ <- Pickles.Sponge.squeeze -- squeeze for u
      IPA.extractScalarChallengesPure (coerce $ ProofFFI.pallasProofOpeningLr ctx.proof)

    bulletproofChallenges :: Vector 16 (SizedF 128 (F Pallas.ScalarField))
    bulletproofChallenges = coerce rawBpChallenges

    -- Xi challenge in Fq (coerced from Fp)
    xiChalFq :: SizedF 128 (F Pallas.ScalarField)
    xiChalFq = coerce (coerceViaBits ctx.oracles.vChal :: SizedF 128 Pallas.ScalarField)

    -- Build circuit input
    tComm :: Vector 7 (AffinePoint (F Pallas.ScalarField))
    tComm = unsafePartial fromJust $ Vector.toVector @7 $ coerce commitments.tComm

    circuitInput :: IncrementallyVerifyProofInput 9 0 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
    circuitInput =
      { publicInput: unsafePartial fromJust $ Vector.toVector $
          map (\fp -> F (fromBigInt (toBigInt fp) :: Pallas.ScalarField)) ctx.publicInputs
      , sgOld: Vector.nil
      , deferredValues:
          { plonk:
              { alpha: wrapF (coerceViaBits ctx.oracles.alphaChal :: SizedF 128 Pallas.ScalarField)
              , beta: wrapF (coerceViaBits ctx.oracles.beta :: SizedF 128 Pallas.ScalarField)
              , gamma: wrapF (coerceViaBits ctx.oracles.gamma :: SizedF 128 Pallas.ScalarField)
              , zeta: wrapF (coerceViaBits ctx.oracles.zetaChal :: SizedF 128 Pallas.ScalarField)
              }
          , combinedInnerProduct: toShifted $ F ctx.oracles.combinedInnerProduct
          , xi: xiChalFq
          , bulletproofChallenges
          , b: toShifted $ F bValue
          , perm: toShifted $ F perm
          , zetaToSrsLength: toShifted $ F (pow ctx.oracles.zeta (BigInt.fromInt maxPolySize))
          , zetaToDomainSize: toShifted $ F (pow ctx.oracles.zeta n)
          }
      , wComm: coerce commitments.wComm
      , zComm: coerce commitments.zComm
      , tComm
      , opening:
          { delta: coerce $ ProofFFI.pallasProofOpeningDelta ctx.proof
          , sg: coerce $ ProofFFI.pallasProofOpeningSg ctx.proof
          , lr: coerce $ ProofFFI.pallasProofOpeningLr ctx.proof
          , z1: toShifted $ F $ ProofFFI.pallasProofOpeningZ1 ctx.proof
          , z2: toShifted $ F $ ProofFFI.pallasProofOpeningZ2 ctx.proof
          }
      }

    circuit
      :: forall t
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t Identity
      => IncrementallyVerifyProofInput 9 0 (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t Identity Unit
    circuit input = do
      { success } <- evalSpongeM initialSpongeCircuit $
        incrementallyVerifyProof @51 @Vesta.G
          IPA.type1ScalarOps
          (groupMapParams $ Proxy @Vesta.G)
          params
          input
      assert_ success

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(IncrementallyVerifyProofInput 9 0 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied_
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

-------------------------------------------------------------------------------
-- | verify test
-------------------------------------------------------------------------------

-- | Full verify circuit test.
-- | Wraps incrementallyVerifyProof with digest and challenge assertions.
verifyTest :: VestaTestContext -> Aff Unit
verifyTest ctx = do
  let
    commitments = ProofFFI.pallasProofCommitments ctx.proof
    numPublic = Array.length ctx.publicInputs
    columnCommsRaw = ProofFFI.pallasVerifierIndexColumnComms ctx.verifierIndex

    indexComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    indexComms = unsafePartial fromJust $ Vector.toVector $ Array.take 6 columnCommsRaw

    coeffComms :: Vector 15 (AffinePoint Pallas.ScalarField)
    coeffComms = unsafePartial fromJust $ Vector.toVector $ Array.take 15 $ Array.drop 6 columnCommsRaw

    sigmaComms :: Vector 6 (AffinePoint Pallas.ScalarField)
    sigmaComms = unsafePartial fromJust $ Vector.toVector $ Array.drop 21 columnCommsRaw

    -- Build params (compile-time constants)
    params :: IncrementallyVerifyProofParams 9 Pallas.ScalarField
    params =
      { curveParams: curveParams (Proxy @Vesta.G)
      , lagrangeComms: unsafePartial fromJust $ Vector.toVector $
          coerce (ProofFFI.pallasLagrangeCommitments ctx.verifierIndex numPublic)
      , blindingH: coerce $ ProofFFI.pallasProverIndexBlindingGenerator ctx.verifierIndex
      , sigmaCommLast: coerce $ ProofFFI.pallasSigmaCommLast ctx.verifierIndex
      , columnComms:
          { index: coerce indexComms
          , coeff: coerce coeffComms
          , sigma: coerce sigmaComms
          }
      , indexDigest: ProofFFI.pallasVerifierIndexDigest ctx.verifierIndex
      }

    -- Compute deferred values from oracles
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    maxPolySize = ProofFFI.pallasVerifierIndexMaxPolySize ctx.verifierIndex
    omega = ProofFFI.domainGenerator ctx.domainLog2

    -- Perm scalar (pure, using expanded plonk values from oracles)
    zetaToNMinus1 = pow ctx.oracles.zeta n - one
    zkPoly = ProofFFI.permutationVanishingPolynomial
      { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
    omegaToMinusZkRows = pow omega (n - BigInt.fromInt zkRows)
    permInput =
      { w: map _.zeta (Vector.take @7 (ProofFFI.proofWitnessEvals ctx.proof))
      , sigma: map _.zeta (ProofFFI.proofSigmaEvals ctx.proof)
      , z: ProofFFI.proofZEvals ctx.proof
      , shifts: ProofFFI.proverIndexShifts ctx.proverIndex
      , alpha: ctx.oracles.alpha
      , beta: toField ctx.oracles.beta
      , gamma: toField ctx.oracles.gamma
      , zkPolynomial: zkPoly
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: ctx.oracles.zeta
      }
    perm = permScalar permInput

    -- b value from FFI
    { challenges: rustChallenges } = mkIpaTestContext ctx
    bValue = ProofFFI.computeB0
      { challenges: Vector.toUnfoldable rustChallenges
      , zeta: ctx.oracles.zeta
      , zetaOmega: ctx.oracles.zeta * omega
      , evalscale: ctx.oracles.u
      }

    -- Bulletproof challenges (raw 128-bit from IPA sponge, coerced to Fq)
    { spongeState } = mkIpaTestContext ctx

    rawBpChallenges :: Vector 16 (SizedF 128 Pallas.ScalarField)
    rawBpChallenges = Pickles.Sponge.evalPureSpongeM spongeState do
      _ <- Pickles.Sponge.squeeze -- squeeze for u
      IPA.extractScalarChallengesPure (coerce $ ProofFFI.pallasProofOpeningLr ctx.proof)

    bulletproofChallenges :: Vector 16 (SizedF 128 (F Pallas.ScalarField))
    bulletproofChallenges = coerce rawBpChallenges

    -- Xi challenge in Fq (coerced from Fp)
    xiChalFq :: SizedF 128 (F Pallas.ScalarField)
    xiChalFq = coerce (coerceViaBits ctx.oracles.vChal :: SizedF 128 Pallas.ScalarField)

    -- Build circuit input
    tComm :: Vector 7 (AffinePoint (F Pallas.ScalarField))
    tComm = unsafePartial fromJust $ Vector.toVector @7 $ coerce commitments.tComm

    circuitInput :: IncrementallyVerifyProofInput 9 0 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))
    circuitInput =
      { publicInput: unsafePartial fromJust $ Vector.toVector $
          map (\fp -> F (fromBigInt (toBigInt fp) :: Pallas.ScalarField)) ctx.publicInputs
      , sgOld: Vector.nil
      , deferredValues:
          { plonk:
              { alpha: wrapF (coerceViaBits ctx.oracles.alphaChal :: SizedF 128 Pallas.ScalarField)
              , beta: wrapF (coerceViaBits ctx.oracles.beta :: SizedF 128 Pallas.ScalarField)
              , gamma: wrapF (coerceViaBits ctx.oracles.gamma :: SizedF 128 Pallas.ScalarField)
              , zeta: wrapF (coerceViaBits ctx.oracles.zetaChal :: SizedF 128 Pallas.ScalarField)
              }
          , combinedInnerProduct: toShifted $ F ctx.oracles.combinedInnerProduct
          , xi: xiChalFq
          , bulletproofChallenges
          , b: toShifted $ F bValue
          , perm: toShifted $ F perm
          , zetaToSrsLength: toShifted $ F (pow ctx.oracles.zeta (BigInt.fromInt maxPolySize))
          , zetaToDomainSize: toShifted $ F (pow ctx.oracles.zeta n)
          }
      , wComm: coerce commitments.wComm
      , zComm: coerce commitments.zComm
      , tComm
      , opening:
          { delta: coerce $ ProofFFI.pallasProofOpeningDelta ctx.proof
          , sg: coerce $ ProofFFI.pallasProofOpeningSg ctx.proof
          , lr: coerce $ ProofFFI.pallasProofOpeningLr ctx.proof
          , z1: toShifted $ F $ ProofFFI.pallasProofOpeningZ1 ctx.proof
          , z2: toShifted $ F $ ProofFFI.pallasProofOpeningZ2 ctx.proof
          }
      }

    -- Claimed sponge digest: coerce from Vesta.ScalarField to Pallas.ScalarField
    claimedDigestFq :: Pallas.ScalarField
    claimedDigestFq = fromBigInt (toBigInt ctx.oracles.fqDigest)

    circuit
      :: forall t
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t Identity
      => IncrementallyVerifyProofInput 9 0 (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t Identity Unit
    circuit input = do
      success <- evalSpongeM initialSpongeCircuit $
        verify @51 @Vesta.G
          IPA.type1ScalarOps
          (groupMapParams $ Proxy @Vesta.G)
          params
          input
          false_ -- isBaseCase (real proof, not base case)
          (const_ claimedDigestFq)
      assert_ success

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(IncrementallyVerifyProofInput 9 0 (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField))))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint Pallas.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit
    , testFunction: satisfied_
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

-------------------------------------------------------------------------------
-- | Main spec
-------------------------------------------------------------------------------

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll createVestaTestContext $
  describe "E2E Circuit Tests" do
    it "ftEval0Circuit matches Rust FFI ftEval0" ftEval0CircuitTest
    it "combined_inner_product_correct circuit integration" combinedInnerProductCorrectCircuitTest
    it "xiCorrectCircuit verifies claimed xi" xiCorrectCircuitTest
    it "plonkChecksCircuit verifies xi, evalscale, and combined_inner_product" plonkChecksCircuitTest
    it "bCorrectCircuit verifies with Rust-provided values" bCorrectCircuitTest
    it "extractScalarChallenges circuit matches pure and Rust" extractChallengesCircuitTest
    it "bulletReduceCircuit matches Rust lr_prod" bulletReduceCircuitTest
    it "debug verify traces intermediate IPA values" debugVerifyTest
    it "ipaFinalCheckCircuit verifies with Rust proof values" ipaFinalCheckCircuitTest
    it "checkBulletproof composes transcript and IPA verification" checkBulletproofTest
    it "incrementallyVerifyProof wires all components together" incrementallyVerifyProofTest
    it "verify wires IVP + deferred value assertions" verifyTest
