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
import Control.Monad.State.Trans (StateT(..), evalStateT)
import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Foldable (foldl)
import Data.Identity (Identity(..))
import Data.Maybe (fromJust)
import Data.Newtype (un, unwrap)
import Data.Schnorr.Gen (VerifyInput, genValidSignature)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (error)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.Commitments (combinedInnerProduct, computeB)
import Pickles.IPA (BCorrectInput)
import Pickles.IPA as IPA
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (PointEval, evalCoefficientPolys, evalLinearization, evalSelectorPolys, evalWitnessPolys, proverIndexDomainLog2, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.PlonkChecks.GateConstraints (buildChallenges, buildEvalPoint, parseHex)
import Pickles.PlonkChecks.Permutation (permContribution)
import Pickles.Sponge (lowest128BitsPure)
import Pickles.Sponge as Pickles.Sponge
import Poseidon (class PoseidonField)
import RandomOracle.Sponge (Sponge)
import RandomOracle.Sponge as RandomOracle
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, compilePure, makeSolver, runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (createCRS, createProverIndex)
import Snarky.Backend.Kimchi.Types (ProverIndex)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Circuit.Schnorr (SignatureVar(..), pallasScalarOps, verifies)
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, endoScalar, fromBigInt, generator, pow, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.SizedF (SizedF(..), coerceViaBits)
import Test.Pickles.Linearization (buildFFIInput)
import Test.Pickles.ProofFFI (OraclesResult, Proof)
import Test.Pickles.ProofFFI as ProofFFI
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied)
import Test.Spec (SpecT, beforeAll, describe, it)
import Test.Spec.Assertions (shouldEqual)
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
    verifies (pallasScalarOps @51) genPointVar { signature, publicKey, message }

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
        -- For Vesta commitment curve, use the Vesta endoScalar (in Fp = Vesta.ScalarField)
        endo = endoScalar @Vesta.BaseField @Vesta.ScalarField
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
    challengesArray = ProofFFI.proofBulletproofChallenges ctx.proverIndex
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
    challengesArray = ProofFFI.proofBulletproofChallenges ctx.proverIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }
    numChallenges = Array.length challengesArray

  -- IPA rounds should match the number of challenges
  liftEffect $ ipaRounds `shouldEqual` numChallenges

-------------------------------------------------------------------------------
-- | Pure sponge monad helpers (without newtype wrapper for simpler use)
-------------------------------------------------------------------------------

-- | A simpler state monad for the sponge (avoiding SpongeM complexity)
type PureSpongeM' f = StateT (Sponge f) Identity

-- | Run the pure sponge monad
evalPureSpongeM' :: forall f a. Sponge f -> PureSpongeM' f a -> a
evalPureSpongeM' s m = un Identity $ evalStateT m s

-- | Absorb a field element
absorbPure :: forall f. PoseidonField f => f -> PureSpongeM' f Unit
absorbPure x = StateT \s -> Identity $ Tuple unit (RandomOracle.absorb x s)

-- | Squeeze a 128-bit scalar challenge
squeezeScalarChallengePure' :: forall f. PrimeField f => FieldSizeInBits f 255 => PoseidonField f => PureSpongeM' f (SizedF 128 f)
squeezeScalarChallengePure' = StateT \s ->
  let
    { result, sponge } = RandomOracle.squeeze s
  in
    Identity $ Tuple (SizedF $ lowest128BitsPure result) sponge

-- | Test that bCorrectCircuit verifies using Rust-provided values.
-- | Uses circuitSpec infrastructure to verify constraint satisfaction.
bCorrectCircuitTest :: TestContext -> Aff Unit
bCorrectCircuitTest ctx = do
  let
    -- Get bulletproof challenges from Rust
    challengesArray = ProofFFI.proofBulletproofChallenges ctx.proverIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    challenges :: Vector 16 (F Vesta.ScalarField)
    challenges = unsafePartial $ fromJust $ Vector.toVector $ map F challengesArray

    -- Get evaluation points from oracles
    omega = ProofFFI.domainGenerator ctx.domainLog2
    zetaOmega = ctx.oracles.zeta * omega

    -- Compute expected b value using Rust FFI
    expectedB = ProofFFI.computeB0
      { challenges: challengesArray
      , zeta: ctx.oracles.zeta
      , zetaOmega
      , evalscale: ctx.oracles.u
      }

    -- Bundle circuit input (using F wrapper for CircuitType)
    circuitInput :: BCorrectInput 16 (F Vesta.ScalarField)
    circuitInput =
      { challenges
      , zeta: F ctx.oracles.zeta
      , zetaOmega: F zetaOmega
      , evalscale: F ctx.oracles.u
      , expectedB: F expectedB
      }

    -- The circuit wrapping bCorrectCircuit
    circuit
      :: forall t m
       . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
      => BCorrectInput 16 (FVar Vesta.ScalarField)
      -> Snarky (KimchiConstraint Vesta.ScalarField) t m (BoolVar Vesta.ScalarField)
    circuit = IPA.bCorrectCircuit

    solver = makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit

    builtState = compilePure
      (Proxy @(BCorrectInput 16 (F Vesta.ScalarField)))
      (Proxy @Boolean)
      (Proxy @(KimchiConstraint Vesta.ScalarField))
      circuit
      Kimchi.initialState

  -- Run circuitSpec with the single Rust-provided test input
  -- testFunction expects the circuit to return true (b is correct)
  circuitSpecPureInputs
    { builtState
    , checker: Kimchi.eval
    , solver
    , testFunction: satisfied (const true :: BCorrectInput 16 (F Vesta.ScalarField) -> Boolean)
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

-- | In-circuit test for challenge extraction.
-- | Circuit runs over Pallas.ScalarField (Fq) where the sponge operates.
-- | Extracts 128-bit scalar challenges, verifies circuit matches pure sponge,
-- | and validates endo-mapped values match Rust.
extractChallengesCircuitTest :: TestContext -> Aff Unit
extractChallengesCircuitTest ctx = do
  let
    -- Get L/R pairs from the proof (coordinates in Pallas.ScalarField = Fq)
    lrPairs :: Vector 16 (IPA.LrPair Pallas.ScalarField)
    lrPairs = ProofFFI.pallasProofOpeningLr ctx.proof

    -- Get sponge checkpoint (used as constants, not circuit inputs)
    checkpoint = ProofFFI.pallasSpongeCheckpointBeforeChallenges ctx.proverIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Parse checkpoint into sponge state
    spongeMode = case checkpoint.spongeMode of
      "Absorbed" -> RandomOracle.Absorbed (unsafeFinite checkpoint.modeCount)
      _ -> RandomOracle.Squeezed (unsafeFinite checkpoint.modeCount)

    -- Pure sponge for computing expected values
    pureSponge :: Sponge Pallas.ScalarField
    pureSponge = { state: checkpoint.state, spongeState: spongeMode }

    -- Circuit sponge initialized from constants
    circuitSponge = Pickles.Sponge.spongeFromConstants
      { state: checkpoint.state, spongeState: spongeMode }

    -- Compute expected 128-bit challenges using pure sponge
    expected128BitChallenges :: Vector 16 (SizedF 128 Pallas.ScalarField)
    expected128BitChallenges = evalPureSpongeM' pureSponge $ do
      traverse processPairPure lrPairs
      where
      processPairPure { l, r } = do
        absorbPure l.x
        absorbPure l.y
        absorbPure r.x
        absorbPure r.y
        squeezeScalarChallengePure'

    -- Apply endo mapping to 128-bit challenges to get full field elements
    -- coerceViaBits: SizedF 128 Pallas.ScalarField -> SizedF 128 Pallas.BaseField (same bits, different field)
    -- toFieldPure: applies endo mapping to get full field element
    endoMappedChallenges :: Array Pallas.BaseField
    endoMappedChallenges = Vector.toUnfoldable $ map
      (\raw128 -> unwrap $ toFieldPure (coerceViaBits raw128) (endoScalar :: Pallas.BaseField))
      expected128BitChallenges

    -- Get Rust-computed endo-mapped challenges for comparison
    rustChallenges = ProofFFI.proofBulletproofChallenges ctx.proverIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Build circuit input (just L/R pairs - sponge is constant)
    circuitInput :: Vector 16 (IPA.LrPair (F Pallas.ScalarField))
    circuitInput = map (\{ l, r } -> { l: { x: F l.x, y: F l.y }, r: { x: F r.x, y: F r.y } }) lrPairs

    -- The circuit: extract 128-bit scalar challenges
    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => Vector 16 (IPA.LrPair (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m (Vector 16 (SizedF 128 (FVar Pallas.ScalarField)))
    circuit pairs = Pickles.Sponge.evalSpongeM circuitSponge (IPA.extractScalarChallenges pairs)

    solver = makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) circuit

    builtState = compilePure
      (Proxy @(Vector 16 (IPA.LrPair (F Pallas.ScalarField))))
      (Proxy @(Vector 16 (SizedF 128 (F Pallas.ScalarField))))
      (Proxy @(KimchiConstraint Pallas.ScalarField))
      circuit
      Kimchi.initialState

    -- testFunction: compare circuit output to expected pure sponge output
    testFn :: Vector 16 (IPA.LrPair (F Pallas.ScalarField)) -> Vector 16 (SizedF 128 (F Pallas.ScalarField))
    testFn _ = map (\(SizedF x) -> SizedF (F x)) expected128BitChallenges

  -- Verify endo-mapped challenges match Rust (validates pure sponge + endo)
  liftEffect $ endoMappedChallenges `shouldEqual` rustChallenges

  -- Verify circuit produces correct 128-bit challenges (validates circuit impl)
  circuitSpecPureInputs
    { builtState
    , checker: Kimchi.eval
    , solver
    , testFunction: satisfied testFn
    , postCondition: Kimchi.postCondition
    }
    [ circuitInput ]

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
    it "bCorrectCircuit verifies with Rust-provided values" bCorrectCircuitTest
    it "extractScalarChallenges circuit matches pure and Rust" extractChallengesCircuitTest
