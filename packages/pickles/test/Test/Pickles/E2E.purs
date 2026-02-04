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
import Data.Array (concatMap, (:))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Foldable (foldl)
import Data.Identity (Identity(..))
import Data.Maybe (fromJust)
import Data.Newtype (un, unwrap)
import Data.Schnorr (isEven, truncateFieldCoerce)
import Data.Schnorr.Gen (VerifyInput)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Exception (error)
import Effect.Exception.Unsafe (unsafeThrow)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.Commitments (combinedInnerProduct)
import Pickles.IPA (BCorrectInput, IpaFinalCheckInput, bCorrect, computeB)
import Pickles.IPA as IPA
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (PointEval, evalCoefficientPolys, evalLinearization, evalSelectorPolys, evalWitnessPolys, proverIndexDomainLog2, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.PlonkChecks.CombinedInnerProduct (CombinedInnerProductCheckInput, combinedInnerProductCheckCircuit)
import Pickles.PlonkChecks.FtEval (ftEval0, ftEval0Circuit)
import Pickles.PlonkChecks.GateConstraints (GateConstraintInput, buildChallenges, buildEvalPoint, parseHex)
import Pickles.PlonkChecks.Permutation (PermutationInput, permContribution)
import Pickles.PlonkChecks.XiCorrect (XiCorrectInput, emptyPrevChallengeDigest, xiCorrectCircuit, xiCorrectPure)
import Pickles.Sponge (liftSnarky)
import Pickles.Sponge as Pickles.Sponge
import Poseidon as Poseidon
import RandomOracle.Sponge (Sponge)
import RandomOracle.Sponge as RandomOracle
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, compilePure, makeSolver, runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (createCRS, createProverIndex)
import Snarky.Backend.Kimchi.Types (ProverIndex)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, assertEqual_, assert_)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Circuit.Kimchi.GroupMap (groupMapParams)
import Snarky.Circuit.Schnorr (SignatureVar(..), pallasScalarOps, verifies)
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (endoScalar, fromAffine, fromBigInt, generator, pow, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.SizedF (SizedF(..), coerceViaBits)
import Snarky.Types.Shifted (Type1, fromShifted, toShifted)
import Test.Pickles.Linearization (buildFFIInput)
import Test.Pickles.ProofFFI (OraclesResult, Proof)
import Test.Pickles.ProofFFI as ProofFFI
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied, satisfied_)
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

-- | Create a fixed valid Schnorr signature for deterministic testing.
-- | Uses constant private key and message to ensure reproducible results.
fixedValidSignature :: VerifyInput 4 (F Vesta.ScalarField) Boolean
fixedValidSignature =
  let
    -- Fixed private key (arbitrary non-zero scalar)
    privateKey :: Pallas.ScalarField
    privateKey = fromBigInt (BigInt.fromInt 12345)

    -- Fixed message (4 field elements)
    message :: Vector 4 Vesta.ScalarField
    message = unsafePartial $ fromJust $ Vector.toVector
      [ fromBigInt (BigInt.fromInt 1)
      , fromBigInt (BigInt.fromInt 2)
      , fromBigInt (BigInt.fromInt 3)
      , fromBigInt (BigInt.fromInt 4)
      ]

    -- Compute public key = privateKey * generator
    publicKey :: AffinePoint Vesta.ScalarField
    publicKey = unsafePartial fromJust $ toAffine $ scalarMul privateKey (generator @_ @Pallas.G)

    -- Compute k' = H(pk.x, pk.y, message)
    kPrimeBase = Poseidon.hash $ publicKey.x : publicKey.y : Vector.toUnfoldable message

    kPrime :: Pallas.ScalarField
    kPrime = truncateFieldCoerce kPrimeBase

    -- R = k' * G
    { x: r, y: ry } = unsafePartial fromJust $ toAffine $ scalarMul kPrime (generator @_ @Pallas.G)

    -- Adjust k for even y coordinate
    k = if isEven ry then kPrime else negate kPrime

    -- e = H(pk.x, pk.y, r, message)
    eBase = Poseidon.hash $ publicKey.x : publicKey.y : r : Vector.toUnfoldable message

    e :: Pallas.ScalarField
    e = fromBigInt (toBigInt eBase)

    -- s = k + e * privateKey
    s :: Pallas.ScalarField
    s = k + e * privateKey
  in
    { signature: { r: F r, s: toShifted $ F s }
    , publicKey: { x: F publicKey.x, y: F publicKey.y }
    , message: map F message
    }

-- | Create the shared test context.
-- | Uses a fixed Schnorr signature for deterministic testing.
createTestContext :: Aff TestContext
createTestContext = do
  let input = fixedValidSignature

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
-- | Uses fixed challenges (not proof-derived) to test gate constraint evaluation.
gateConstraintTest :: TestContext -> Aff Unit
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

-- | Test that PureScript ftEval0 matches the Rust FFI value.
-- | This validates the composition: ftEval0 = permContribution + publicEval - gateConstraints
ftEval0Test :: TestContext -> Aff Unit
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

    -- Compute public input polynomial evaluation (same as permutationTest)
    publicEval = computePublicEval ctx.publicInputs ctx.domainLog2 ctx.oracles.zeta

    -- Compute ftEval0 using our composition function
    computed = ftEval0
      { permContribution: permResult
      , publicEval
      , gateConstraints: gateResult
      }

  -- Compare against Rust FFI ground truth
  liftEffect $ computed `shouldEqual` ctx.oracles.ftEval0

-- | Circuit test for ftEval0Circuit.
-- | Verifies the in-circuit computation matches the Rust FFI ftEval0 value.
ftEval0CircuitTest :: TestContext -> Aff Unit
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
      , beta: F ctx.oracles.beta
      , gamma: F ctx.oracles.gamma
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
      , beta: F ctx.oracles.beta
      , gamma: F ctx.oracles.gamma
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
      result <- ftEval0Circuit PallasTokens.constantTermTokens input
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
combinedInnerProductCorrectCircuitTest :: TestContext -> Aff Unit
combinedInnerProductCorrectCircuitTest ctx = do
  let
    -- Shared values used in multiple places
    witnessEvals = ProofFFI.proofWitnessEvals ctx.proof
    zEvals = ProofFFI.proofZEvals ctx.proof
    sigmaEvals = ProofFFI.proofSigmaEvals ctx.proof
    indexEvals = evalSelectorPolys ctx.proverIndex ctx.oracles.zeta
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt ctx.domainLog2)
    omega = ProofFFI.domainGenerator ctx.domainLog2

    circuitInput :: CombinedInnerProductCheckInput (F Vesta.ScalarField)
    circuitInput =
      { permInput:
          { w: map (F <<< _.zeta) (Vector.take @7 witnessEvals)
          , sigma: map (F <<< _.zeta) sigmaEvals
          , z: coerce zEvals
          , shifts: map F (ProofFFI.proverIndexShifts ctx.proverIndex)
          , alpha: F ctx.oracles.alpha
          , beta: F ctx.oracles.beta
          , gamma: F ctx.oracles.gamma
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
          , beta: F ctx.oracles.beta
          , gamma: F ctx.oracles.gamma
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
      , polyscale: F ctx.oracles.v
      , evalscale: F ctx.oracles.u
      }

    circuit
      :: forall t m
       . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
      => CombinedInnerProductCheckInput (FVar Vesta.ScalarField)
      -> Snarky (KimchiConstraint Vesta.ScalarField) t m Unit
    circuit input = do
      cipResult <- combinedInnerProductCheckCircuit PallasTokens.constantTermTokens input
      assertEqual_ cipResult (const_ ctx.oracles.combinedInnerProduct)

  circuitSpecPureInputs
    { builtState: compilePure
        (Proxy @(CombinedInnerProductCheckInput (F Vesta.ScalarField)))
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

-- | Test xi_correct: verify that claimed xi (polyscale) was computed correctly.
-- | Replays Fr-sponge absorptions and compares squeezed+endo result to claimed xi.
xiCorrectTest :: TestContext -> Aff Unit
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

    -- Build XiCorrectInput
    xiInput :: XiCorrectInput Vesta.ScalarField
    xiInput =
      { fqDigest: ctx.oracles.fqDigest
      , prevChallengeDigest: emptyPrevChallengeDigest -- no previous recursion in our test
      , ftEval1: ctx.oracles.ftEval1
      , publicEvals
      , zEvals
      , indexEvals
      , witnessEvals
      , coeffEvals
      , sigmaEvals
      , endo: endoScalar @Vesta.BaseField @Vesta.ScalarField
      , claimedXi: ctx.oracles.v
      }

    -- Compute xi using PureScript
    psXi = xiCorrectPure xiInput

  -- Compare PureScript computed xi against Rust's v (polyscale)
  liftEffect $ psXi `shouldEqual` ctx.oracles.v

-- | Circuit test for xi_correct.
-- | Replays Fr-sponge in-circuit and asserts equality with claimed xi.
xiCorrectCircuitTest :: TestContext -> Aff Unit
xiCorrectCircuitTest ctx = do
  let
    -- Get proof evaluations
    witnessEvals = ProofFFI.proofWitnessEvals ctx.proof
    zEvals = ProofFFI.proofZEvals ctx.proof
    sigmaEvals = ProofFFI.proofSigmaEvals ctx.proof
    coeffEvals = ProofFFI.proofCoefficientEvals ctx.proof
    indexEvals = evalSelectorPolys ctx.proverIndex ctx.oracles.zeta

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
      , endo: F $ endoScalar @Vesta.BaseField @Vesta.ScalarField
      , claimedXi: F ctx.oracles.v
      }

    circuit
      :: forall t m
       . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
      => XiCorrectInput (FVar Vesta.ScalarField)
      -> Snarky (KimchiConstraint Vesta.ScalarField) t m Unit
    circuit = xiCorrectCircuit

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

-- | Test that bCorrectCircuit verifies using Rust-provided values.
-- | Uses circuitSpec infrastructure to verify constraint satisfaction.
bCorrectCircuitTest :: TestContext -> Aff Unit
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
extractChallengesCircuitTest :: TestContext -> Aff Unit
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
          (\raw128 -> unwrap $ toFieldPure (coerceViaBits raw128) (endoScalar :: Pallas.BaseField))
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
bulletReduceCircuitTest :: TestContext -> Aff Unit
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
        expectedLrProd = ProofFFI.pallasProofLrProd ctx.proverIndex
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
ipaFinalCheckCircuitTest :: TestContext -> Aff Unit
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
      , b: toShifted $ (coerce :: Vesta.ScalarField -> F Vesta.ScalarField) $ ProofFFI.computeB0
          { challenges: Vector.toUnfoldable challenges
          , zeta: ctx.oracles.zeta
          , zetaOmega: ctx.oracles.zeta * omega
          , evalscale: ctx.oracles.u
          }
      , blindingGenerator: coerce $ ProofFFI.pallasProverIndexBlindingGenerator ctx.proverIndex
      }

    circuit
      :: forall t m
       . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
      => IpaFinalCheckInput 16 (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField))
      -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
    circuit input = do
      result <- IPA.ipaFinalCheckCircuit @Pallas.ScalarField @Vesta.G
        IPA.type1ScalarOps
        (groupMapParams $ Proxy @Vesta.G)
        (Pickles.Sponge.spongeFromConstants spongeState)
        input
      assert_ result

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
debugVerifyTest :: TestContext -> Aff Unit
debugVerifyTest ctx = do
  let
    _ = ProofFFI.pallasDebugVerify ctx.proverIndex
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

--------------------------------------------------------------------------------
type IPATestContext =
  { challenges :: Vector 16 Vesta.ScalarField
  , spongeState :: Sponge Pallas.ScalarField
  , combinedPolynomial :: AffinePoint Pallas.ScalarField
  , omega :: Vesta.ScalarField
  }

mkIpaTestContext :: TestContext -> IPATestContext
mkIpaTestContext ctx =
  let

    -- Get sponge checkpoint (state before L/R processing)
    checkpoint = ProofFFI.pallasSpongeCheckpointBeforeChallenges ctx.proverIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Parse checkpoint into sponge state
    spongeMode = case checkpoint.spongeMode of
      "Absorbed" -> RandomOracle.Absorbed (unsafeFinite checkpoint.modeCount)
      _ -> RandomOracle.Squeezed (unsafeFinite checkpoint.modeCount)

    -- Combined polynomial commitment
    combinedPolynomial :: AffinePoint Pallas.ScalarField
    combinedPolynomial = ProofFFI.pallasCombinedPolynomialCommitment ctx.proverIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }

    -- Compute b = bPoly(challenges, zeta) + evalscale * bPoly(challenges, zetaOmega)
    challengesArray = ProofFFI.proofBulletproofChallenges ctx.proverIndex
      { proof: ctx.proof, publicInput: ctx.publicInputs }
    omega = ProofFFI.domainGenerator ctx.domainLog2
  in
    { challenges: unsafePartial $ fromJust $ Vector.toVector @16 challengesArray
    , spongeState: { state: checkpoint.state, spongeState: spongeMode }
    , combinedPolynomial
    , omega
    }

-------------------------------------------------------------------------------
-- | Main spec
-------------------------------------------------------------------------------

spec :: SpecT Aff Unit Aff Unit
spec = beforeAll createTestContext $
  describe "E2E Schnorr Circuit" do
    it "PS gate constraint evaluation matches Rust for valid Schnorr witness" gateConstraintTest
    it "PS permContribution matches ftEval0 - publicEval + gateConstraints" permutationTest
    it "PS ftEval0 matches Rust FFI ftEval0" ftEval0Test
    it "ftEval0Circuit matches Rust FFI ftEval0" ftEval0CircuitTest
    it "combined_inner_product_correct circuit integration" combinedInnerProductCorrectCircuitTest
    it "PS combinedInnerProduct matches Rust combined_inner_product" combinedInnerProductTest
    it "PS xiCorrect computes xi matching Rust polyscale" xiCorrectTest
    it "xiCorrectCircuit verifies claimed xi" xiCorrectCircuitTest
    it "opening proof verifies" openingProofTest
    it "PS computeB matches Rust computeB0" computeBTest
    it "IPA rounds matches domain log2" ipaRoundsTest
    it "bCorrectCircuit verifies with Rust-provided values" bCorrectCircuitTest
    it "extractScalarChallenges circuit matches pure and Rust" extractChallengesCircuitTest
    it "bulletReduceCircuit matches Rust lr_prod" bulletReduceCircuitTest
    it "debug verify traces intermediate IPA values" debugVerifyTest
    it "ipaFinalCheckCircuit verifies with Rust proof values" ipaFinalCheckCircuitTest
