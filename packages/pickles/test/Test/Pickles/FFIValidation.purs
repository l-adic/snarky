module Test.Pickles.FFIValidation (spec) where

-- | Pure PureScript vs Rust FFI validation tests.
-- | These tests compare PureScript implementations against Rust FFI ground truth
-- | without compiling any circuits.

import Prelude

import Data.Array as Array
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Pickles.Commitments (combinedInnerProduct)
import Pickles.IPA (computeB)
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (PointEval, evalCoefficientPolys, evalLinearization, evalSelectorPolys, evalWitnessPolys, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.PlonkChecks.FtEval (ftEval0)
import Pickles.PlonkChecks.GateConstraints (buildChallenges, buildEvalPoint, parseHex)
import Pickles.PlonkChecks.Permutation (permContribution)
import Pickles.PlonkChecks.XiCorrect (FrSpongeInput, emptyPrevChallengeDigest, frSpongeChallengesPure)
import Snarky.Circuit.DSL (toField)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, pow)
import Pickles.Types (StepIPARounds)
import Snarky.Curves.Vesta as Vesta
import Test.Pickles.Linearization (buildFFIInput)
import Test.Pickles.ProofFFI as ProofFFI
import Test.Pickles.TestContext (StepCase(..), StepProofContext, computePublicEval, createStepProofContext, toVectorOrThrow, zkRows)
import Test.Spec (SpecT, beforeAll, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | Test that PureScript linearization matches Rust for a valid Schnorr circuit.
-- | Uses fixed challenges (not proof-derived) to test gate constraint evaluation.
gateConstraintTest :: StepProofContext -> Aff Unit
gateConstraintTest ctx = do
  let
    -- Fixed challenges for deterministic testing
    zeta = fromBigInt (BigInt.fromInt 98765) :: Vesta.ScalarField
    alpha = fromBigInt (BigInt.fromInt 11111) :: Vesta.ScalarField
    beta = fromBigInt (BigInt.fromInt 22222) :: Vesta.ScalarField
    gamma = fromBigInt (BigInt.fromInt 33333) :: Vesta.ScalarField
    jointCombiner = fromBigInt (BigInt.fromInt 44444) :: Vesta.ScalarField
    -- Compute evaluations using FFI from prover index
    witnessEvals = evalWitnessPolys ctx.proverIndex ctx.witness zeta
    coeffEvals = evalCoefficientPolys ctx.proverIndex zeta
    indexEvals = evalSelectorPolys ctx.proverIndex zeta

    -- Compute domain-dependent values
    vanishesOnZk' = vanishesOnZkAndPreviousRows
      { domainLog2: ctx.domainLog2, zkRows, pt: zeta }
    lagrangeFalse0 = unnormalizedLagrangeBasis
      { domainLog2: ctx.domainLog2, zkRows: 0, offset: 0, pt: zeta }
    lagrangeTrue1 = unnormalizedLagrangeBasis
      { domainLog2: ctx.domainLog2, zkRows, offset: -1, pt: zeta }

    evalPoint = buildEvalPoint
      { witnessEvals
      , coeffEvals
      , indexEvals
      , defaultVal: zero
      }

    challenges = buildChallenges
      { alpha
      , beta
      , gamma
      , jointCombiner
      , vanishesOnZk: vanishesOnZk'
      , lagrangeFalse0
      , lagrangeTrue1
      }

    env = fieldEnv evalPoint challenges parseHex

    -- Evaluate using PureScript interpreter
    psResult :: Vesta.ScalarField
    psResult = evaluate PallasTokens.constantTermTokens env

    -- Build FFI input for Rust evaluator
    ffiInput = buildFFIInput
      { witnessEvals
      , coeffEvals
      , indexEvals
      , alpha
      , beta
      , gamma
      , jointCombiner
      , zeta
      , domainLog2: ctx.domainLog2
      }

    -- Evaluate using Rust
    rustResult = evalLinearization ffiInput

  -- PureScript should match Rust
  liftEffect $ psResult `shouldEqual` rustResult

-- | Test that PureScript permContribution matches the oracle ft_eval0 value.
permutationTest :: StepProofContext -> Aff Unit
permutationTest ctx = do
  let
    -- Get proof evaluations
    witnessEvals = ProofFFI.proofWitnessEvals ctx.proof
    zEvals = ProofFFI.proofZEvals ctx.proof
    sigmaEvals = ProofFFI.proofSigmaEvals ctx.proof
    shifts = ProofFFI.proverIndexShifts ctx.proverIndex

    -- Compute domain-related values for permutation
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    omega = ProofFFI.domainGenerator ctx.domainLog2
    zetaToNMinus1 = pow ctx.oracles.zeta n - one
    zkPoly = ProofFFI.permutationVanishingPolynomial
      { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
    omegaToMinusZkRows = pow omega (n - BigInt.fromInt zkRows)

    -- Build permutation input and compute contribution
    permInput =
      { w: map _.zeta (Vector.take @7 witnessEvals)
      , sigma: map _.zeta sigmaEvals
      , z: zEvals
      , shifts
      , alpha: ctx.oracles.alpha
      , beta: toField ctx.oracles.beta
      , gamma: toField ctx.oracles.gamma
      , zkPolynomial: zkPoly
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: ctx.oracles.zeta
      }
    permResult = permContribution permInput

    -- Compute gate constraints using proof witness evals
    coeffEvals = evalCoefficientPolys ctx.proverIndex ctx.oracles.zeta
    indexEvals = evalSelectorPolys ctx.proverIndex ctx.oracles.zeta
    vanishesOnZk' = vanishesOnZkAndPreviousRows
      { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
    lagrangeFalse0 = unnormalizedLagrangeBasis
      { domainLog2: ctx.domainLog2, zkRows: 0, offset: 0, pt: ctx.oracles.zeta }
    lagrangeTrue1 = unnormalizedLagrangeBasis
      { domainLog2: ctx.domainLog2, zkRows, offset: -1, pt: ctx.oracles.zeta }
    evalPoint = buildEvalPoint
      { witnessEvals
      , coeffEvals
      , indexEvals
      , defaultVal: zero
      }
    challenges = buildChallenges
      { alpha: ctx.oracles.alpha
      , beta: toField ctx.oracles.beta
      , gamma: toField ctx.oracles.gamma
      , jointCombiner: zero
      , vanishesOnZk: vanishesOnZk'
      , lagrangeFalse0
      , lagrangeTrue1
      }
    env = fieldEnv evalPoint challenges parseHex
    gateResult = evaluate PallasTokens.constantTermTokens env

    -- Compute public input polynomial evaluation
    publicEval = computePublicEval
      { publicInputs: ctx.publicInputs
      , domainLog2: ctx.domainLog2
      , omega: ProofFFI.domainGenerator ctx.domainLog2
      , zeta: ctx.oracles.zeta
      }

  -- Verify: permContribution = ftEval0 - publicEval + gateConstraints
  liftEffect $ permResult `shouldEqual` (ctx.oracles.ftEval0 - publicEval + gateResult)

-- | Test that PureScript ftEval0 matches the Rust FFI value.
-- | This validates the composition: ftEval0 = permContribution + publicEval - gateConstraints
ftEval0Test :: StepProofContext -> Aff Unit
ftEval0Test ctx = do
  let
    -- Get proof evaluations
    witnessEvals = ProofFFI.proofWitnessEvals ctx.proof
    zEvals = ProofFFI.proofZEvals ctx.proof
    sigmaEvals = ProofFFI.proofSigmaEvals ctx.proof
    shifts = ProofFFI.proverIndexShifts ctx.proverIndex

    -- Compute domain-related values for permutation
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    omega = ProofFFI.domainGenerator ctx.domainLog2
    zetaToNMinus1 = pow ctx.oracles.zeta n - one
    zkPoly = ProofFFI.permutationVanishingPolynomial
      { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
    omegaToMinusZkRows = pow omega (n - BigInt.fromInt zkRows)

    -- Build permutation input and compute contribution
    permInput =
      { w: map _.zeta (Vector.take @7 witnessEvals)
      , sigma: map _.zeta sigmaEvals
      , z: zEvals
      , shifts
      , alpha: ctx.oracles.alpha
      , beta: toField ctx.oracles.beta
      , gamma: toField ctx.oracles.gamma
      , zkPolynomial: zkPoly
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: ctx.oracles.zeta
      }
    permResult = permContribution permInput

    -- Compute gate constraints using proof witness evals
    coeffEvals = evalCoefficientPolys ctx.proverIndex ctx.oracles.zeta
    indexEvals = evalSelectorPolys ctx.proverIndex ctx.oracles.zeta
    vanishesOnZk' = vanishesOnZkAndPreviousRows
      { domainLog2: ctx.domainLog2, zkRows, pt: ctx.oracles.zeta }
    lagrangeFalse0 = unnormalizedLagrangeBasis
      { domainLog2: ctx.domainLog2, zkRows: 0, offset: 0, pt: ctx.oracles.zeta }
    lagrangeTrue1 = unnormalizedLagrangeBasis
      { domainLog2: ctx.domainLog2, zkRows, offset: -1, pt: ctx.oracles.zeta }
    evalPoint = buildEvalPoint
      { witnessEvals
      , coeffEvals
      , indexEvals
      , defaultVal: zero
      }
    challenges = buildChallenges
      { alpha: ctx.oracles.alpha
      , beta: toField ctx.oracles.beta
      , gamma: toField ctx.oracles.gamma
      , jointCombiner: zero
      , vanishesOnZk: vanishesOnZk'
      , lagrangeFalse0
      , lagrangeTrue1
      }
    env = fieldEnv evalPoint challenges parseHex
    gateResult = evaluate PallasTokens.constantTermTokens env

    -- Compute public input polynomial evaluation (same as permutationTest)
    publicEval = computePublicEval
      { publicInputs: ctx.publicInputs
      , domainLog2: ctx.domainLog2
      , omega: ProofFFI.domainGenerator ctx.domainLog2
      , zeta: ctx.oracles.zeta
      }

    -- Compute ftEval0 using our composition function
    computed = ftEval0
      { permContribution: permResult
      , publicEval
      , gateConstraints: gateResult
      }

  -- Compare against Rust FFI ground truth
  liftEffect $ computed `shouldEqual` ctx.oracles.ftEval0

-- | Test that PureScript combinedInnerProduct matches the Rust FFI value.
combinedInnerProductTest :: StepProofContext -> Aff Unit
combinedInnerProductTest ctx = do
  let
    -- Get proof evaluations
    witnessEvals = ProofFFI.proofWitnessEvals ctx.proof
    zEvals = ProofFFI.proofZEvals ctx.proof
    sigmaEvals = ProofFFI.proofSigmaEvals ctx.proof
    coeffEvals = ProofFFI.proofCoefficientEvals ctx.proof

    -- Get selector evaluations from prover index
    indexEvalsRaw = evalSelectorPolys ctx.proverIndex ctx.oracles.zeta

    -- Build the 45-element evaluation vector in the correct order:
    -- 1. public (1)
    -- 2. ft (1)
    -- 3. z (1)
    -- 4. Index: Generic, Poseidon, CompleteAdd, VarBaseMul, EndoMul, EndoMulScalar (6)
    -- 5. Witness: 0..14 (15)
    -- 6. Coefficient: 0..14 (15)
    -- 7. Sigma: 0..5 (6)

    -- Public eval
    publicEval :: PointEval Vesta.ScalarField
    publicEval = { zeta: ctx.oracles.publicEvalZeta, omegaTimesZeta: ctx.oracles.publicEvalZetaOmega }

    -- ft eval
    ftEval :: PointEval Vesta.ScalarField
    ftEval = { zeta: ctx.oracles.ftEval0, omegaTimesZeta: ctx.oracles.ftEval1 }

    -- Build the full 45-element vector using type-safe append
    -- Index selector order matches Kimchi verifier: Generic, Poseidon, CompleteAdd, VarBaseMul, EndoMul, EndoMulScalar
    -- 3 + 6 + 15 + 15 + 6 = 45
    allEvals :: Vector 45 (PointEval Vesta.ScalarField)
    allEvals =
      (publicEval :< ftEval :< zEvals :< Vector.nil)
        `Vector.append` indexEvalsRaw
        `Vector.append` witnessEvals
        `Vector.append` coeffEvals
        `Vector.append` sigmaEvals

    -- Compute combined inner product using PureScript
    psResult = combinedInnerProduct
      { polyscale: ctx.oracles.v
      , evalscale: ctx.oracles.u
      , evals: allEvals
      }

  -- Compare against Rust combined_inner_product from oracles
  liftEffect $ psResult `shouldEqual` ctx.oracles.combinedInnerProduct

-- | Test xi_correct and r_correct: verify that claimed xi (polyscale) and r (evalscale)
-- | were computed correctly via Fr-sponge Fiat-Shamir.
xiCorrectTest :: StepProofContext -> Aff Unit
xiCorrectTest ctx = do
  let
    -- Get proof evaluations
    witnessEvals = ProofFFI.proofWitnessEvals ctx.proof
    zEvals = ProofFFI.proofZEvals ctx.proof
    sigmaEvals = ProofFFI.proofSigmaEvals ctx.proof
    coeffEvals = ProofFFI.proofCoefficientEvals ctx.proof
    indexEvals = evalSelectorPolys ctx.proverIndex ctx.oracles.zeta

    -- Public evals
    publicEvals :: PointEval Vesta.ScalarField
    publicEvals = { zeta: ctx.oracles.publicEvalZeta, omegaTimesZeta: ctx.oracles.publicEvalZetaOmega }

    -- Build FrSpongeInput for pure challenge computation
    spongeInput :: FrSpongeInput Vesta.ScalarField
    spongeInput =
      { fqDigest: ctx.oracles.fqDigest
      , prevChallengeDigest: emptyPrevChallengeDigest -- no previous recursion in our test
      , ftEval1: ctx.oracles.ftEval1
      , publicEvals
      , zEvals
      , indexEvals
      , witnessEvals
      , coeffEvals
      , sigmaEvals
      , endo: let EndoScalar e = endoScalar @Vesta.BaseField @Vesta.ScalarField in e
      }

    -- Compute scalar challenges using PureScript Fr-sponge
    result = frSpongeChallengesPure spongeInput

  -- Compare PureScript computed xi (endo-expanded) against Rust's v (polyscale)
  liftEffect $ result.xi `shouldEqual` ctx.oracles.v
  -- Compare PureScript computed evalscale (endo-expanded) against Rust's u (evalscale)
  liftEffect $ result.evalscale `shouldEqual` ctx.oracles.u

-- | Test that the opening proof verifies.
openingProofTest :: StepProofContext -> Aff Unit
openingProofTest ctx = do
  let verified = ProofFFI.verifyOpeningProof ctx.verifierIndex { proof: ctx.proof, publicInput: ctx.publicInputs }
  liftEffect $ verified `shouldEqual` true

-- | Test that PureScript computeB matches the Rust FFI computeB0.
computeBTest :: StepProofContext -> Aff Unit
computeBTest ctx = do
  let
    -- Get bulletproof challenges from the proof
    challengesArray = ProofFFI.proofBulletproofChallenges ctx.verifierIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Convert to type-safe vector (16 = IPA rounds for Schnorr circuit's SRS)
    challenges :: Vector StepIPARounds Vesta.ScalarField
    challenges = toVectorOrThrow @StepIPARounds "computeBTest proofBulletproofChallenges" challengesArray

    -- Compute zeta * omega for the second evaluation point
    omega = ProofFFI.domainGenerator ctx.domainLog2
    zetaOmega = ctx.oracles.zeta * omega

    -- Compute using PureScript
    psResult = computeB challenges
      { zeta: ctx.oracles.zeta
      , zetaOmega
      , evalscale: ctx.oracles.u
      }

    -- Compute using Rust FFI
    rustResult = ProofFFI.computeB0
      { challenges: challengesArray
      , zeta: ctx.oracles.zeta
      , zetaOmega
      , evalscale: ctx.oracles.u
      }

  -- Compare PureScript vs Rust
  liftEffect $ psResult `shouldEqual` rustResult

-- | Test that IPA rounds matches the bulletproof challenges length.
-- | Note: IPA rounds depends on SRS size, not circuit domain size.
ipaRoundsTest :: StepProofContext -> Aff Unit
ipaRoundsTest ctx = do
  let
    -- Get IPA rounds from the proof
    ipaRounds = ProofFFI.proofIpaRounds ctx.proof

    -- Get bulletproof challenges (their count should match IPA rounds)
    challengesArray = ProofFFI.proofBulletproofChallenges ctx.verifierIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }
    numChallenges = Array.length challengesArray

  -- IPA rounds should match the number of challenges
  liftEffect $ ipaRounds `shouldEqual` numChallenges

-------------------------------------------------------------------------------
-- | Main spec
-------------------------------------------------------------------------------

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll (createStepProofContext BaseCase) $
  describe "FFI Validation" do
    it "PS gate constraint evaluation matches Rust for valid Schnorr witness" gateConstraintTest
    it "PS permContribution matches ftEval0 - publicEval + gateConstraints" permutationTest
    it "PS ftEval0 matches Rust FFI ftEval0" ftEval0Test
    it "PS combinedInnerProduct matches Rust combined_inner_product" combinedInnerProductTest
    it "PS Fr-sponge challenges (xi, evalscale) match Rust" xiCorrectTest
    it "opening proof verifies" openingProofTest
    it "PS computeB matches Rust computeB0" computeBTest
    it "IPA rounds matches domain log2" ipaRoundsTest
