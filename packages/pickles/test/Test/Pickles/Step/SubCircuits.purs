module Test.Pickles.Step.SubCircuits (spec) where

-- | Real-data circuit tests for the Step-side verifier (Plonk checks).
-- | These tests run on Fp (Vesta.ScalarField) and verify portions of the
-- | verifier logic using data derived from a real Schnorr Step proof.

import Prelude

import Data.Array as Array
import Data.Identity (Identity)
import Data.Newtype (un)
import Data.Reflectable (class Reflectable, reifyType)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Pickles.IPA (BCorrectInput, IpaFinalCheckInput, bCorrect, ipaFinalCheckCircuit, type2ScalarOps)
import Pickles.IPA as IPA
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI (evalCoefficientPolys, evalSelectorPolys, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.PlonkChecks (PlonkChecksInput, plonkChecksCircuit)
import Pickles.PlonkChecks.CombinedInnerProduct (BatchingScalars, CombinedInnerProductCheckInput, combinedInnerProductCheckCircuit)
import Pickles.PlonkChecks.FtEval (ftEval0Circuit)
import Pickles.PlonkChecks.GateConstraints (GateConstraintInput)
import Pickles.PlonkChecks.Permutation (PermutationInput)
import Pickles.PlonkChecks.XiCorrect (FrSpongeInput, XiCorrectInput, emptyPrevChallengeDigest, frSpongeChallengesPure, xiCorrectCircuit)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit, liftSnarky)
import Pickles.Sponge as Pickles.Sponge
import Pickles.Types (WrapIPARounds)
import Pickles.Verify (IncrementallyVerifyProofInput, incrementallyVerifyProof, verify)
import RandomOracle.Sponge (Sponge)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, assertEqual_, assert_, const_, false_, toField)
import Snarky.Circuit.Kimchi (Type2, groupMapParams, toShifted)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (EndoScalar(..), endoScalar, pow)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Pickles.ProofFFI as ProofFFI
import Test.Pickles.TestContext (InductiveTestContext, StepProofContext, WrapProofContext, buildStepIVPInput, buildStepIVPParams, computePublicEval, mkStepIpaContext, mkWrapIpaContext, toVectorOrThrow, unsafeFqToFp, zkRows)
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied, satisfied_)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

-- | Test for ipaFinalCheckCircuit in an Fp circuit verifying an Fq proof (cross-field).
ipaFinalCheckTest :: WrapProofContext -> Aff Unit
ipaFinalCheckTest ctx = do
  let
    -- Extract Fq proof data
    z1 = ProofFFI.vestaProofOpeningZ1 ctx.proof
    z2 = ProofFFI.vestaProofOpeningZ2 ctx.proof
    b = ProofFFI.computeB0
      { challenges: ProofFFI.proofBulletproofChallenges ctx.verifierIndex { proof: ctx.proof, publicInput: ctx.publicInputs }
      , zeta: ctx.oracles.zeta
      , zetaOmega: ctx.oracles.zeta * ProofFFI.domainGenerator ctx.domainLog2
      , evalscale: ctx.oracles.u
      }
    cip = ctx.oracles.combinedInnerProduct

    -- Convert Fq scalars to Type2 (Fp circuit representation)
    z1Shifted = toShifted (F z1)
    z2Shifted = toShifted (F z2)
    bShifted = toShifted (F b)
    cipShifted = toShifted (F cip)

    -- Commitment curve for our Fp circuit is Pallas (base Fp).
    delta = ProofFFI.vestaProofOpeningDelta ctx.proof
    sg = ProofFFI.vestaProofOpeningSg ctx.proof
    lr = toVectorOrThrow @16 "ipaFinalCheckTest vestaProofOpeningLr" $
      ProofFFI.vestaProofOpeningLr ctx.proof
    blindingGenerator = ProofFFI.vestaProverIndexBlindingGenerator ctx.verifierIndex
    combinedPolynomial = ProofFFI.vestaCombinedPolynomialCommitment ctx.verifierIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Group map params for Pallas
    pallasGroupMapParams = groupMapParams (Proxy @Pallas.G)

    -- Use mkWrapIpaContext to get correct sponge state
    ipaCtx = mkWrapIpaContext ctx

    -- Circuit input
    input :: IpaFinalCheckInput 16 (F Vesta.ScalarField) (Type2 (F Vesta.ScalarField) Boolean)
    input =
      { delta: coerce delta
      , sg: coerce sg
      , lr: coerce lr
      , z1: z1Shifted
      , z2: z2Shifted
      , combinedInnerProduct: cipShifted
      , b: bShifted
      , blindingGenerator: coerce blindingGenerator
      , combinedPolynomial: coerce combinedPolynomial
      }

    circuit
      :: forall t m
       . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
      => IpaFinalCheckInput 16 (FVar Vesta.ScalarField) (Type2 (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField))
      -> Snarky (KimchiConstraint Vesta.ScalarField) t m Unit
    circuit inVar = do
      let
        initialSpongeState :: Sponge (FVar Vesta.ScalarField)
        initialSpongeState =
          { state: map const_ ipaCtx.spongeState.state
          , spongeState: ipaCtx.spongeState.spongeState
          }
      void $ evalSpongeM initialSpongeState do
        let ops = type2ScalarOps
        res <- ipaFinalCheckCircuit @Vesta.ScalarField @Pallas.G ops pallasGroupMapParams inVar
        liftSnarky $ assert_ res.success

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(IpaFinalCheckInput 16 (F Vesta.ScalarField) (Type2 (F Vesta.ScalarField) Boolean)))
        (Proxy @Unit)
        (Proxy @(KimchiConstraint Vesta.ScalarField))
        circuit
        Kimchi.initialState
    , checker: Kimchi.eval
    , solver: makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit
    , testFunction: satisfied_
    , postCondition: Kimchi.postCondition
    }
    [ input ]

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
    publicEval = F $ computePublicEval
      { publicInputs: ctx.publicInputs
      , domainLog2: ctx.domainLog2
      , omega
      , zeta: ctx.oracles.zeta
      }

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
      , publicEvalForFt: F $ computePublicEval
          { publicInputs: ctx.publicInputs
          , domainLog2: ctx.domainLog2
          , omega
          , zeta: ctx.oracles.zeta
          }
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
      , publicEvalForFt: F $ computePublicEval
          { publicInputs: ctx.publicInputs
          , domainLog2: ctx.domainLog2
          , omega
          , zeta: ctx.oracles.zeta
          }
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

-------------------------------------------------------------------------------
-- | incrementallyVerifyProof test
-------------------------------------------------------------------------------

-- | Full incrementallyVerifyProof circuit test for Fp circuit verifying a Wrap (Pallas) proof.
incrementallyVerifyProofTest :: WrapProofContext -> Aff Unit
incrementallyVerifyProofTest ctx =
  reifyType (Array.length ctx.publicInputs) go
  where
  go :: forall nPublic. Reflectable nPublic Int => Proxy nPublic -> Aff Unit
  go _ =
    let
      params = buildStepIVPParams @nPublic ctx
      circuitInput = buildStepIVPInput @nPublic ctx

      circuit
        :: forall t
         . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t Identity
        => IncrementallyVerifyProofInput nPublic 0 WrapIPARounds (FVar Vesta.ScalarField) (Type2 (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField))
        -> Snarky (KimchiConstraint Vesta.ScalarField) t Identity Unit
      circuit input = do
        { success } <- evalSpongeM initialSpongeCircuit $
          incrementallyVerifyProof @51 @Pallas.G
            IPA.type2ScalarOps
            (groupMapParams $ Proxy @Pallas.G)
            params
            input
        assert_ success
    in
      circuitSpecPureInputs
        { builtState: compilePure
            (Proxy @(IncrementallyVerifyProofInput nPublic 0 WrapIPARounds (F Vesta.ScalarField) (Type2 (F Vesta.ScalarField) Boolean)))
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

-------------------------------------------------------------------------------
-- | verify test
-------------------------------------------------------------------------------

-- | Full verify circuit test for Fp circuit verifying a Wrap (Pallas) proof.
-- | Wraps incrementallyVerifyProof with digest and challenge assertions.
verifyTest :: WrapProofContext -> Aff Unit
verifyTest ctx =
  reifyType (Array.length ctx.publicInputs) go
  where
  go :: forall nPublic. Reflectable nPublic Int => Proxy nPublic -> Aff Unit
  go _ =
    let
      params = buildStepIVPParams @nPublic ctx
      circuitInput = buildStepIVPInput @nPublic ctx

      -- Claimed sponge digest: coerce from Pallas.ScalarField (Fq) to Vesta.ScalarField (Fp)
      claimedDigestFp :: Vesta.ScalarField
      claimedDigestFp = unsafeFqToFp ctx.oracles.fqDigest

      circuit
        :: forall t
         . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t Identity
        => IncrementallyVerifyProofInput nPublic 0 WrapIPARounds (FVar Vesta.ScalarField) (Type2 (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField))
        -> Snarky (KimchiConstraint Vesta.ScalarField) t Identity Unit
      circuit input = do
        success <- evalSpongeM initialSpongeCircuit $
          verify @51 @Pallas.G
            IPA.type2ScalarOps
            (groupMapParams $ Proxy @Pallas.G)
            params
            input
            false_ -- isBaseCase (real proof, not base case)
            (const_ claimedDigestFp)
        assert_ success
    in
      circuitSpecPureInputs
        { builtState: compilePure
            (Proxy @(IncrementallyVerifyProofInput nPublic 0 WrapIPARounds (F Vesta.ScalarField) (Type2 (F Vesta.ScalarField) Boolean)))
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

spec :: SpecT Aff InductiveTestContext Aff Unit
spec = do
  describe "Step Sub-circuits (Real Data)" do
    it "ftEval0Circuit matches Rust FFI ftEval0" \{ step0 } -> ftEval0CircuitTest step0
    it "combined_inner_product_correct circuit integration" \{ step0 } -> combinedInnerProductCorrectCircuitTest step0
    it "xiCorrectCircuit verifies claimed xi" \{ step0 } -> xiCorrectCircuitTest step0
    it "plonkChecksCircuit verifies xi, evalscale, and combined_inner_product" \{ step0 } -> plonkChecksCircuitTest step0
    it "bCorrectCircuit verifies with Rust-provided values" \{ step0 } -> bCorrectCircuitTest step0

  describe "Step Verifier Cross-Field (Fp circuit verifying Fq proof)" do
    it "verifies Fq IPA final check using Type2 shifted values" \{ wrap0 } -> ipaFinalCheckTest wrap0
    it "incrementallyVerifyProof (Fp circuit verifying Wrap proof)" \{ wrap0 } -> incrementallyVerifyProofTest wrap0
    it "verify (Fp circuit verifying Wrap proof)" \{ wrap0 } -> verifyTest wrap0
