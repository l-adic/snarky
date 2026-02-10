module Test.Pickles.Step.SubCircuits (spec) where

-- | Real-data circuit tests for the Step-side verifier (Plonk checks).
-- | These tests run on Fp (Vesta.ScalarField) and verify portions of the
-- | verifier logic using data derived from a real Schnorr Step proof.

import Prelude

import Data.Identity (Identity)
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Pickles.IPA (BCorrectInput, bCorrect)
import Pickles.IPA as IPA
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI (evalCoefficientPolys, evalSelectorPolys, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.PlonkChecks (PlonkChecksInput, plonkChecksCircuit)
import Pickles.PlonkChecks.CombinedInnerProduct (BatchingScalars, CombinedInnerProductCheckInput, combinedInnerProductCheckCircuit)
import Pickles.PlonkChecks.FtEval (ftEval0Circuit)
import Pickles.PlonkChecks.GateConstraints (GateConstraintInput)
import Pickles.PlonkChecks.Permutation (PermutationInput)
import Pickles.PlonkChecks.XiCorrect (FrSpongeInput, XiCorrectInput, emptyPrevChallengeDigest, frSpongeChallengesPure, xiCorrectCircuit)
import Pickles.Sponge (evalSpongeM, initialSponge, initialSpongeCircuit, runPureSpongeM)
import Pickles.Sponge as Pickles.Sponge
import RandomOracle.Sponge (Sponge)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, assertEqual_, const_, toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (EndoScalar(..), endoScalar, pow)
import Snarky.Curves.Vesta as Vesta
import Test.Pickles.ProofFFI as ProofFFI
import Test.Pickles.TestContext (StepProofContext, computePublicEval, createStepProofContext, mkStepIpaContext, zkRows)
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied, satisfied_)
import Test.Spec (SpecT, beforeAll, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

-- | Circuit test for ftEval0Circuit.
-- | Verifies the in-circuit computation matches the Rust FFI ftEval0 value.
ftEval0CircuitTest :: StepProofContext -> Aff Unit
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
combinedInnerProductCorrectCircuitTest :: StepProofContext -> Aff Unit
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
xiCorrectCircuitTest :: StepProofContext -> Aff Unit
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
plonkChecksCircuitTest :: StepProofContext -> Aff Unit
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
bCorrectCircuitTest :: StepProofContext -> Aff Unit
bCorrectCircuitTest ctx = do
  let
    { challenges, omega } = mkStepIpaContext ctx
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

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll createStepProofContext $
  describe "Step Sub-circuits (Real Data)" do
    it "ftEval0Circuit matches Rust FFI ftEval0" ftEval0CircuitTest
    it "combined_inner_product_correct circuit integration" combinedInnerProductCorrectCircuitTest
    it "xiCorrectCircuit verifies claimed xi" xiCorrectCircuitTest
    it "plonkChecksCircuit verifies xi, evalscale, and combined_inner_product" plonkChecksCircuitTest
    it "bCorrectCircuit verifies with Rust-provided values" bCorrectCircuitTest
