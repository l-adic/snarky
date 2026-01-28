module Test.Pickles.E2E
  ( computePublicEval
  , schnorrBuiltState
  , schnorrCircuit
  , schnorrSolver
  , spec
  ) where

-- | End-to-end tests using a real Schnorr circuit.
-- | Builds a circuit, generates a valid witness, creates a prover index,
-- | and verifies various plonk checks against the real evaluations.
-- |
-- | This module will grow as we add permutation, commitment, and full
-- | ft_eval0 verification.

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Morph (hoist)
import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Identity (Identity(..))
import Data.Maybe (fromJust)
import Data.Newtype (un)
import Data.Schnorr.Gen (VerifyInput, genValidSignature)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Exception (error)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.Commitments (combinedInnerProduct, computeB)
import Pickles.Verifier (verify)
import Pickles.Verifier (VerifyInput) as Verifier
import Pickles.Verifier.Types (VerifierOutput)
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (PointEval, evalCoefficientPolys, evalLinearization, evalSelectorPolys, evalWitnessPolys, proverIndexDomainLog2, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.PlonkChecks.GateConstraints (buildChallenges, buildEvalPoint, parseHex)
import Pickles.PlonkChecks.Permutation (permContribution)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, compilePure, makeSolver, runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (createCRS, createProverIndex)
import Snarky.Backend.Kimchi.Types (ProverIndex)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky)
import Snarky.Circuit.Schnorr (SignatureVar(..), verifies)
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (class FieldSizeInBits, endoBase, endoScalar, fromAffine, fromBigInt, generator, pow, scalarMul, toAffine, toBigInt)
import Snarky.Types.Shifted (Type2, toShifted)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.Linearization (buildFFIInput)
import Test.Pickles.ProofFFI (OraclesResult, Proof, pallasVerifyDeferredCheckInternal)
import Test.Pickles.ProofFFI as ProofFFI
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Spec (SpecT, beforeAll, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Type.Proxy (Proxy(..))

-- | Standard Kimchi constants
zkRows :: Int
zkRows = 3

-------------------------------------------------------------------------------
-- | Schnorr circuit setup
-------------------------------------------------------------------------------

-- | The Schnorr verification circuit over Vesta.ScalarField (= Pallas.BaseField = Fp).
schnorrCircuit
  :: forall t
   . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t Identity
  => VerifyInput 4 (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField)
  -> Snarky (KimchiConstraint Vesta.ScalarField) t Identity (BoolVar Vesta.ScalarField)
schnorrCircuit { signature: { r: sigR, s: sigS }, publicKey, message } =
  let
    genPointVar :: AffinePoint (FVar Vesta.ScalarField)
    genPointVar =
      let
        { x, y } = unsafePartial fromJust $ toAffine (generator @_ @Pallas.G)
      in
        { x: const_ x, y: const_ y }
    signature = SignatureVar { r: sigR, s: sigS }
  in
    verifies @51 genPointVar { signature, publicKey, message }

-- | Compiled circuit state for the Schnorr circuit.
schnorrBuiltState :: CircuitBuilderState (KimchiGate Vesta.ScalarField) (AuxState Vesta.ScalarField)
schnorrBuiltState = compilePure
  (Proxy @(VerifyInput 4 (F Vesta.ScalarField) Boolean))
  (Proxy @Boolean)
  (Proxy @(KimchiConstraint Vesta.ScalarField))
  schnorrCircuit
  Kimchi.initialState

-- | Solver for the Schnorr circuit.
schnorrSolver :: Solver Vesta.ScalarField (KimchiGate Vesta.ScalarField) (VerifyInput 4 (F Vesta.ScalarField) Boolean) Boolean
schnorrSolver = makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) schnorrCircuit

-------------------------------------------------------------------------------
-- | Test setup types
-------------------------------------------------------------------------------

-- | Shared test context created once by beforeAll.
-- | Contains prover index, witness, proof, and oracles.
type TestContext =
  { proverIndex :: ProverIndex Vesta.G Vesta.ScalarField
  , witness :: Vector 15 (Array Vesta.ScalarField)
  , publicInputs :: Array Vesta.ScalarField
  , domainLog2 :: Int
  , proof :: Proof Vesta.G Vesta.ScalarField
  , oracles :: OraclesResult Vesta.ScalarField
  }

-- | Create the shared test context.
-- | Generates a valid Schnorr signature, runs the solver, creates the prover index,
-- | generates a proof, and computes oracles.
createTestContext :: Aff TestContext
createTestContext = do
  let gen = genValidSignature (Proxy @Pallas.G) (Proxy @4)

  -- Generate a valid input and run the solver
  input <- liftEffect $ randomSampleOne gen
  crs <- liftEffect $ createCRS @Vesta.ScalarField

  let
    nat :: Identity ~> Aff
    nat = pure <<< un Identity

  eRes <- runSolverT (\a -> hoist nat $ schnorrSolver a) input
  case eRes of
    Left e -> liftEffect $ throwError $ error (show e)
    Right (Tuple _ assignments) -> do
      let
        -- Build constraint system and witness
        { constraintSystem, constraints } = makeConstraintSystem @Vesta.ScalarField
          { constraints: concatMap toKimchiRows schnorrBuiltState.constraints
          , publicInputs: schnorrBuiltState.publicInputs
          , unionFind: (un AuxState schnorrBuiltState.aux).wireState.unionFind
          }
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables constraints
          , publicInputs: schnorrBuiltState.publicInputs
          }
        endo = endoBase @Vesta.ScalarField @Pallas.ScalarField
        proverIndex = createProverIndex @Vesta.ScalarField @Vesta.G
          { endo
          , constraintSystem
          , crs
          }
        domainLog2 = proverIndexDomainLog2 proverIndex

        -- Create proof and get oracles
        proof = ProofFFI.createProof { proverIndex, witness }
        oracles = ProofFFI.proofOracles proverIndex { proof, publicInput: publicInputs }

      pure { proverIndex, witness, publicInputs, domainLog2, proof, oracles }

-------------------------------------------------------------------------------
-- | Permutation helper
-------------------------------------------------------------------------------

-- | Compute the public input polynomial evaluation at zeta.
-- | p(zeta) = (Z_H(zeta) / n) * sum_i (omega^i * publicInput[i] / (zeta - omega^i))
-- | where Z_H(zeta) = zeta^n - 1, n = 2^domainLog2, omega = domain generator.
-- | The omega^i factor comes from the Lagrange basis: L_i(x) = omega^i * (x^n - 1) / (n * (x - omega^i))
computePublicEval
  :: Array Vesta.ScalarField
  -> Int
  -> Vesta.ScalarField
  -> Vesta.ScalarField
computePublicEval publicInputs domainLog2 zeta =
  let
    omega = ProofFFI.domainGenerator domainLog2
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt domainLog2)
    zetaToNMinus1 = pow zeta n - one
    { acc } = foldl
      ( \{ acc: a, omegaPow } p ->
          { acc: a + omegaPow * p / (zeta - omegaPow)
          , omegaPow: omegaPow * omega
          }
      )
      { acc: zero, omegaPow: one }
      publicInputs
  in
    zetaToNMinus1 * acc / fromBigInt n

-------------------------------------------------------------------------------
-- | Tests
-------------------------------------------------------------------------------

-- | Test that PureScript linearization matches Rust for a valid Schnorr circuit.
-- | Uses random challenges (not proof-derived) to test gate constraint evaluation.
gateConstraintTest :: TestContext -> Aff Unit
gateConstraintTest ctx = do
  -- Generate random challenges (independent of the proof)
  zeta <- liftEffect $ randomSampleOne (arbitrary @Vesta.ScalarField)
  alpha <- liftEffect $ randomSampleOne (arbitrary @Vesta.ScalarField)
  beta <- liftEffect $ randomSampleOne (arbitrary @Vesta.ScalarField)
  gamma <- liftEffect $ randomSampleOne (arbitrary @Vesta.ScalarField)
  jointCombiner <- liftEffect $ randomSampleOne (arbitrary @Vesta.ScalarField)

  let
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
permutationTest :: TestContext -> Aff Unit
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
      , beta: ctx.oracles.beta
      , gamma: ctx.oracles.gamma
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
      , beta: ctx.oracles.beta
      , gamma: ctx.oracles.gamma
      , jointCombiner: zero
      , vanishesOnZk: vanishesOnZk'
      , lagrangeFalse0
      , lagrangeTrue1
      }
    env = fieldEnv evalPoint challenges parseHex
    gateResult = evaluate PallasTokens.constantTermTokens env

    -- Compute public input polynomial evaluation
    publicEval = computePublicEval ctx.publicInputs ctx.domainLog2 ctx.oracles.zeta

  -- Verify: permContribution = ftEval0 - publicEval + gateConstraints
  liftEffect $ permResult `shouldEqual` (ctx.oracles.ftEval0 - publicEval + gateResult)

-- | Test that PureScript combinedInnerProduct matches the Rust FFI value.
combinedInnerProductTest :: TestContext -> Aff Unit
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

-- | Test that the opening proof verifies.
openingProofTest :: TestContext -> Aff Unit
openingProofTest ctx = do
  let verified = ProofFFI.verifyOpeningProof ctx.proverIndex { proof: ctx.proof, publicInput: ctx.publicInputs }
  liftEffect $ verified `shouldEqual` true

-- | Test that PureScript computeB matches the Rust FFI computeB0.
computeBTest :: TestContext -> Aff Unit
computeBTest ctx = do
  let
    -- Get bulletproof challenges from the proof
    { challenges: challengesArray } = ProofFFI.proofBulletproofChallenges ctx.proverIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Convert to type-safe vector (16 = IPA rounds for Schnorr circuit's SRS)
    challenges :: Vector 16 Vesta.ScalarField
    challenges = unsafePartial $ fromJust $ Vector.toVector challengesArray

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
ipaRoundsTest :: TestContext -> Aff Unit
ipaRoundsTest ctx = do
  let
    -- Get IPA rounds from the proof
    ipaRounds = ProofFFI.proofIpaRounds ctx.proof

    -- Get bulletproof challenges (their count should match IPA rounds)
    { challenges: challengesArray } = ProofFFI.proofBulletproofChallenges ctx.proverIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }
    numChallenges = Array.length challengesArray

  -- IPA rounds should match the number of challenges
  liftEffect $ ipaRounds `shouldEqual` numChallenges

-- | Test the deferred sg commitment check using internal Rust implementation.
-- | This runs the entire check in Rust to isolate any FFI boundary issues.
deferredCheckInternalTest :: TestContext -> Aff Unit
deferredCheckInternalTest ctx = do
  let
    verified = pallasVerifyDeferredCheckInternal ctx.proverIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }
  liftEffect $ verified `shouldEqual` true

-- | Test the deferred sg commitment check.
-- | This verifies that sg = MSM(SRS.g, b_poly_coefficients(challenges)).
deferredCheckTest :: TestContext -> Aff Unit
deferredCheckTest ctx = do
  let
    -- Get bulletproof challenges from the proof
    { challenges: challengesArray } = ProofFFI.proofBulletproofChallenges ctx.proverIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Create b_poly_coefficients polynomial from challenges
    poly = ProofFFI.bPolyCoefficients challengesArray

    -- Get sg commitment coordinates from the proof
    sg = ProofFFI.proofSg ctx.proof

    -- Verify the deferred check: sg = MSM(SRS.g, coeffs)
    verified = ProofFFI.verifyDeferredCheck ctx.proverIndex
      { sgX: sg.x, sgY: sg.y, poly }

  -- The deferred check should pass
  liftEffect $ verified `shouldEqual` true

-- | Test that polynomial length matches 2^(IPA rounds).
polyLengthTest :: TestContext -> Aff Unit
polyLengthTest ctx = do
  let
    -- Get IPA rounds from the proof
    ipaRounds = ProofFFI.proofIpaRounds ctx.proof

    -- Get bulletproof challenges and create polynomial
    { challenges: challengesArray } = ProofFFI.proofBulletproofChallenges ctx.proverIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }
    poly = ProofFFI.bPolyCoefficients challengesArray

    -- Get polynomial length
    polyLen = BigInt.fromInt $ ProofFFI.polyLength poly

    -- Expected length is 2^k where k = number of challenges
    expectedLen = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ipaRounds)

  -- Polynomial length should be 2^(IPA rounds)
  liftEffect $ polyLen `shouldEqual` expectedLen

-------------------------------------------------------------------------------
-- | Verifier Circuit Test
-------------------------------------------------------------------------------

-- | Helper to convert scalar field value to base field via BigInt.
-- | Safe because both are 255-bit fields and we only use this for values
-- | that fit in both (e.g., 128-bit challenges).
scalarToBase :: Vesta.ScalarField -> Vesta.BaseField
scalarToBase x = fromBigInt (toBigInt x)

-- | Build verifier circuit input from the Schnorr proof data.
-- |
-- | The verifier circuit operates over Vesta.BaseField, so:
-- | - Commitment coordinates are native (Vesta points have Vesta.BaseField coords)
-- | - Scalars (z1, z2) are converted via Shifted typeclass (cross-field Type2)
-- | - Other scalar values are converted via BigInt (safe for 128-bit values)
buildVerifierInput
  :: TestContext
  -> Verifier.VerifyInput 16 1 (F Vesta.BaseField) Boolean
buildVerifierInput ctx =
  let
    -- Get sponge-derived values from FFI
    { challenges: challengesArray, c: cScalar } = ProofFFI.proofBulletproofChallenges ctx.proverIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }
    uPoint = ProofFFI.proofUPoint ctx.proverIndex { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Get opening proof data (coordinates in Vesta.BaseField)
    lrPairsArray = ProofFFI.proofOpeningLR ctx.proof
    delta = ProofFFI.proofOpeningDelta ctx.proof
    z1 = ProofFFI.proofOpeningZ1 ctx.proof
    z2 = ProofFFI.proofOpeningZ2 ctx.proof
    sg = ProofFFI.proofSg ctx.proof
    h = ProofFFI.proverIndexH ctx.proverIndex

    -- Get z commitment for the single polynomial commitment
    zComm = ProofFFI.proofZComm ctx.proof

    -- Convert scalar field values to base field
    omega = ProofFFI.domainGenerator ctx.domainLog2

    -- Convert challenges to base field (challenges are 128-bit, fit in both fields)
    challengesBase :: Vector 16 (F Vesta.BaseField)
    challengesBase = unsafePartial $ fromJust $ Vector.toVector $
      map (F <<< scalarToBase) challengesArray

    -- Convert L/R pairs (already in Vesta.BaseField from FFI)
    lrPairs :: Vector 16 { l :: AffinePoint (F Vesta.BaseField), r :: AffinePoint (F Vesta.BaseField) }
    lrPairs = unsafePartial $ fromJust $ Vector.toVector $
      map (\p -> { l: { x: F p.l.x, y: F p.l.y }, r: { x: F p.r.x, y: F p.r.y } }) lrPairsArray

    -- Convert z1, z2 using Shifted (cross-field Type2 conversion)
    -- z1, z2 are in Vesta.ScalarField, convert to Type2 (F Vesta.BaseField) Boolean
    z1Type2 :: Type2 (F Vesta.BaseField) Boolean
    z1Type2 = toShifted (F z1)

    z2Type2 :: Type2 (F Vesta.BaseField) Boolean
    z2Type2 = toShifted (F z2)
  in
    { xi: F (scalarToBase ctx.oracles.v)
    , commitments: { x: F zComm.x, y: F zComm.y } :< Vector.nil
    , combinedInnerProduct: F (scalarToBase ctx.oracles.combinedInnerProduct)
    , opening:
        { lr: lrPairs
        , delta: { x: F delta.x, y: F delta.y }
        , z1: z1Type2
        , z2: z2Type2
        , sg: { x: F sg.x, y: F sg.y }
        }
    , zeta: F (scalarToBase ctx.oracles.zeta)
    , zetaOmega: F (scalarToBase (ctx.oracles.zeta * omega))
    , evalscale: F (scalarToBase ctx.oracles.u)
    , h: { x: F h.x, y: F h.y }
    , challenges: challengesBase
    , u: { x: F uPoint.x, y: F uPoint.y }
    , c: F (scalarToBase cScalar)
    }

-- | Type alias for the verifier circuit input (value version)
type VerifierInputValue = Verifier.VerifyInput 16 1 (F Vesta.BaseField) Boolean

-- | Type alias for the verifier circuit output (value version)
type VerifierOutputValue = VerifierOutput 16 (F Vesta.BaseField)

-- | The verifier circuit over Vesta.BaseField.
-- | Verifies a Schnorr proof's IPA equation.
verifierCircuit
  :: forall t
   . CircuitM Vesta.BaseField (KimchiConstraint Vesta.BaseField) t Identity
  => Verifier.VerifyInput 16 1 (FVar Vesta.BaseField) (BoolVar Vesta.BaseField)
  -> Snarky (KimchiConstraint Vesta.BaseField) t Identity (VerifierOutput 16 (FVar Vesta.BaseField))
verifierCircuit = verify @16 @15 @1 @0 @51

-- | Compiled circuit state for the verifier circuit.
verifierBuiltState :: CircuitBuilderState (KimchiGate Vesta.BaseField) (AuxState Vesta.BaseField)
verifierBuiltState = compilePure
  (Proxy @VerifierInputValue)
  (Proxy @VerifierOutputValue)
  (Proxy @(KimchiConstraint Vesta.BaseField))
  verifierCircuit
  Kimchi.initialState

-- | Solver for the verifier circuit.
verifierSolver :: Solver Vesta.BaseField (KimchiGate Vesta.BaseField) VerifierInputValue VerifierOutputValue
verifierSolver = makeSolver (Proxy @(KimchiConstraint Vesta.BaseField)) verifierCircuit

-- | Test that the verifier circuit produces the correct output.
-- | This verifies the IPA equation in-circuit.
verifierCircuitTest :: TestContext -> Aff Unit
verifierCircuitTest ctx = do
  let
    -- Build the verifier input from proof data
    input = buildVerifierInput ctx

    nat :: Identity ~> Aff
    nat = pure <<< un Identity

  -- Run the solver with the proof data
  eRes <- runSolverT (\a -> hoist nat $ verifierSolver a) input
  case eRes of
    Left e -> liftEffect $ fail $ "Verifier circuit failed: " <> show e
    Right (Tuple output _assignments) -> do
      -- Check that the output challenges match the input challenges
      -- (The circuit just passes through the challenges for deferred verification)
      liftEffect $ output.deferredCheck.challenges `shouldEqual` input.challenges

      -- Verify the deferred sg check via FFI
      let
        { challenges: challengesArray } = ProofFFI.proofBulletproofChallenges ctx.proverIndex
          { proof: ctx.proof, publicInput: ctx.publicInputs }
        poly = ProofFFI.bPolyCoefficients challengesArray
        sg = ProofFFI.proofSg ctx.proof
        verified = ProofFFI.verifyDeferredCheck ctx.proverIndex
          { sgX: sg.x, sgY: sg.y, poly }

      liftEffect $ verified `shouldEqual` true

-------------------------------------------------------------------------------
-- | Main spec
-------------------------------------------------------------------------------

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll createTestContext $
  describe "E2E Schnorr Circuit" do
    it "PS gate constraint evaluation matches Rust for valid Schnorr witness" gateConstraintTest
    it "PS permContribution matches ftEval0 - publicEval + gateConstraints" permutationTest
    it "PS combinedInnerProduct matches Rust combined_inner_product" combinedInnerProductTest
    it "opening proof verifies" openingProofTest
    it "PS computeB matches Rust computeB0" computeBTest
    it "IPA rounds matches domain log2" ipaRoundsTest
    it "deferred sg check verifies (internal Rust)" deferredCheckInternalTest
    it "deferred sg check verifies" deferredCheckTest
    it "polynomial length matches 2^(IPA rounds)" polyLengthTest
    it "verifier circuit satisfies with valid proof" verifierCircuitTest
