module Test.Pickles.E2E
  ( TestContext
  , IPATestContext
  , computePublicEval
  , createTestContext
  , mkIpaTestContext
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
import Data.Newtype (un)
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
import Pickles.IPA (BCorrectInput, CheckBulletproofInput, IpaFinalCheckInput, bCorrect, computeB)
import Pickles.IPA as IPA
import Pickles.Linearization as Linearization
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (PointEval, evalCoefficientPolys, evalLinearization, evalSelectorPolys, evalWitnessPolys, proverIndexDomainLog2, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.PlonkChecks (PlonkChecksInput, plonkChecksCircuit)
import Pickles.PlonkChecks.CombinedInnerProduct (BatchingScalars, CombinedInnerProductCheckInput, combinedInnerProductCheckCircuit)
import Pickles.PlonkChecks.FtEval (ftEval0, ftEval0Circuit)
import Pickles.PlonkChecks.GateConstraints (GateConstraintInput, buildChallenges, buildEvalPoint, parseHex)
import Pickles.PlonkChecks.Permutation (PermutationInput, permContribution, permScalar)
import Pickles.PlonkChecks.XiCorrect (FrSpongeInput, XiCorrectInput, emptyPrevChallengeDigest, frSpongeChallengesPure, xiCorrectCircuit)
import Pickles.Sponge (evalPureSpongeM, evalSpongeM, initialSponge, initialSpongeCircuit, liftSnarky, runPureSpongeM)
import Pickles.Sponge as Pickles.Sponge
import Pickles.Step.FqSpongeTranscript (FqSpongeInput, spongeTranscriptCircuit, spongeTranscriptPure)
import Pickles.Step.IncrementallyVerifyProof (IncrementallyVerifyProofInput, IncrementallyVerifyProofParams, incrementallyVerifyProof)
import Poseidon as Poseidon
import RandomOracle.Sponge (Sponge)
import RandomOracle.Sponge as RandomOracle
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, compilePure, makeSolver, runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (createCRS, createProverIndex, createVerifierIndex)
import Snarky.Backend.Kimchi.Types (ProverIndex, VerifierIndex)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, SizedF, Snarky, assertEqual_, assert_, coerceViaBits, const_)
import Snarky.Circuit.Kimchi (Type1(..), expandToEndoScalar, fieldSizeBits, fromShifted, groupMapParams, toShifted)
import Snarky.Circuit.Schnorr (SignatureVar(..), pallasScalarOps, verifies)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (curveParams, endoScalar, fromAffine, fromBigInt, generator, pow, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
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
  => VerifyInput 4 (FVar Vesta.ScalarField)
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
  (Proxy @(VerifyInput 4 (F Vesta.ScalarField)))
  (Proxy @Boolean)
  (Proxy @(KimchiConstraint Vesta.ScalarField))
  schnorrCircuit
  Kimchi.initialState

-- | Solver for the Schnorr circuit.
schnorrSolver :: Solver Vesta.ScalarField (KimchiGate Vesta.ScalarField) (VerifyInput 4 (F Vesta.ScalarField)) Boolean
schnorrSolver = makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) schnorrCircuit

-------------------------------------------------------------------------------
-- | Test setup types
-------------------------------------------------------------------------------

-- | Shared test context created once by beforeAll.
-- | Contains prover index, witness, proof, and oracles.
type TestContext =
  { proverIndex :: ProverIndex Vesta.G Vesta.ScalarField
  , verifierIndex :: VerifierIndex Vesta.G Vesta.ScalarField
  , witness :: Vector 15 (Array Vesta.ScalarField)
  , publicInputs :: Array Vesta.ScalarField
  , domainLog2 :: Int
  , proof :: Proof Vesta.G Vesta.ScalarField
  , oracles :: OraclesResult Vesta.ScalarField
  }

-- | Create a fixed valid Schnorr signature for deterministic testing.
-- | Uses constant private key and message to ensure reproducible results.
fixedValidSignature :: VerifyInput 4 (F Vesta.ScalarField)
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

    -- The circuit uses scaleFast2' which computes [value + 2^n] * base.
    -- For Schnorr: [s + 2^n]*G - [e + 2^n]*Pk = k*G
    -- So: s = k + (e + 2^n)*d - 2^n
    n = fieldSizeBits (Proxy @Vesta.ScalarField)

    twoToN :: Pallas.ScalarField
    twoToN = fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)

    e :: Pallas.ScalarField
    e = fromBigInt (toBigInt eBase) + twoToN

    s :: Pallas.ScalarField
    s = k + e * privateKey - twoToN
  in
    { signature: { r: F r, s: F $ fromBigInt $ toBigInt s }
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
        verifierIndex = createVerifierIndex @Vesta.ScalarField @Vesta.G proverIndex
        domainLog2 = proverIndexDomainLog2 proverIndex

        -- Create proof and get oracles
        proof = ProofFFI.createProof { proverIndex, witness }
        oracles = ProofFFI.proofOracles verifierIndex { proof, publicInput: publicInputs }

      pure { proverIndex, verifierIndex, witness, publicInputs, domainLog2, proof, oracles }

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

-- | Test xi_correct and r_correct: verify that claimed xi (polyscale) and r (evalscale)
-- | were computed correctly via Fr-sponge Fiat-Shamir.
-- |
-- | This test verifies that our Fr-sponge implementation produces the same scalar
-- | challenges as Rust, and that when expanded via endo, they match Rust's
-- | polyscale (v) and evalscale (u).
-- |
-- | Reference: mina/src/lib/pickles/step_verifier.ml (lines 946-954)
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
      , endo: endoScalar @Vesta.BaseField @Vesta.ScalarField
      }

    -- Compute scalar challenges using PureScript Fr-sponge
    result = frSpongeChallengesPure spongeInput

  -- Compare PureScript computed xi (endo-expanded) against Rust's v (polyscale)
  liftEffect $ result.xi `shouldEqual` ctx.oracles.v
  -- Compare PureScript computed evalscale (endo-expanded) against Rust's u (evalscale)
  liftEffect $ result.evalscale `shouldEqual` ctx.oracles.u

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
      , endo: endoScalar @Vesta.BaseField @Vesta.ScalarField
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
      , endo: F $ endoScalar @Vesta.BaseField @Vesta.ScalarField
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
plonkChecksCircuitTest :: TestContext -> Aff Unit
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
      , endo: endoScalar @Vesta.BaseField @Vesta.ScalarField
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
      , endo: F $ endoScalar @Vesta.BaseField @Vesta.ScalarField
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

-- | Test that the opening proof verifies.
openingProofTest :: TestContext -> Aff Unit
openingProofTest ctx = do
  let verified = ProofFFI.verifyOpeningProof ctx.verifierIndex { proof: ctx.proof, publicInput: ctx.publicInputs }
  liftEffect $ verified `shouldEqual` true

-- | Test that PureScript computeB matches the Rust FFI computeB0.
computeBTest :: TestContext -> Aff Unit
computeBTest ctx = do
  let
    -- Get bulletproof challenges from the proof
    challengesArray = ProofFFI.proofBulletproofChallenges ctx.verifierIndex
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
    challengesArray = ProofFFI.proofBulletproofChallenges ctx.verifierIndex
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
debugVerifyTest :: TestContext -> Aff Unit
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
checkBulletproofTest :: TestContext -> Aff Unit
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
      in
        if endoMapped /= Vector.toUnfoldable rustChallenges then unsafeThrow "checkBulletproof: extracted challenges don't match Rust"
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
    commitments = ProofFFI.pallasProofCommitments ctx.proof
    publicCommArray = ProofFFI.pallasPublicComm ctx.verifierIndex ctx.publicInputs

    spongeInput :: FqSpongeInput 0 7 Pallas.ScalarField
    spongeInput =
      { indexDigest: ProofFFI.pallasVerifierIndexDigest ctx.verifierIndex
      , sgOld: Vector.nil
      , publicComm: unsafePartial fromJust $ Array.head publicCommArray
      , wComm: commitments.wComm
      , zComm: commitments.zComm
      , tComm: unsafePartial fromJust $ Vector.toVector @7 commitments.tComm
      }

    -- Run sponge transcript, then absorb shift_scalar(CIP)
    Tuple _ computedSponge = runPureSpongeM initialSponge do
      _ <- spongeTranscriptPure spongeInput
      let Type1 (F absorbValue) = toShifted (F ctx.oracles.combinedInnerProduct)
      Pickles.Sponge.absorb absorbValue
      pure unit

    ffiSponge =
      let

        -- Get sponge checkpoint (state before L/R processing)
        checkpoint = ProofFFI.pallasSpongeCheckpointBeforeChallenges ctx.verifierIndex
          { proof: ctx.proof, publicInput: ctx.publicInputs }

        -- Parse checkpoint into sponge state
        spongeMode = case checkpoint.spongeMode of
          "Absorbed" -> RandomOracle.Absorbed (unsafeFinite checkpoint.modeCount)
          _ -> RandomOracle.Squeezed (unsafeFinite checkpoint.modeCount)
      in
        { state: checkpoint.state, spongeState: spongeMode }
  in

    if ffiSponge /= computedSponge then unsafeThrow "Mismatch between ffiSponge and computedSpong"
    else
      let
        combinedPolynomial :: AffinePoint Pallas.ScalarField
        combinedPolynomial = ProofFFI.pallasCombinedPolynomialCommitment ctx.verifierIndex
          { proof: ctx.proof, publicInput: ctx.publicInputs }

        challengesArray = ProofFFI.proofBulletproofChallenges ctx.verifierIndex
          { proof: ctx.proof, publicInput: ctx.publicInputs }
        omega = ProofFFI.domainGenerator ctx.domainLog2
      in
        { challenges: unsafePartial $ fromJust $ Vector.toVector @16 challengesArray
        , spongeState: computedSponge
        , combinedPolynomial
        , omega
        }

-------------------------------------------------------------------------------
-- | incrementallyVerifyProof test
-------------------------------------------------------------------------------

-- | Full incrementallyVerifyProof circuit test.
-- | Wires together publicInputCommitment, sponge transcript, ftComm, and
-- | checkBulletproof in a single circuit and verifies satisfiability.
incrementallyVerifyProofTest :: TestContext -> Aff Unit
incrementallyVerifyProofTest ctx = do
  let
    -- Oracle values are natively Fq (from the Fq-sponge over commitment coords),
    -- but the FFI types them as Vesta.ScalarField (the application circuit field).
    -- Re-interpret as Pallas.ScalarField (the IVP circuit field) — same integers.
    fpToFq :: Vesta.ScalarField -> Pallas.ScalarField
    fpToFq x = fromBigInt (toBigInt x)

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
      , beta: ctx.oracles.beta
      , gamma: ctx.oracles.gamma
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
              { alpha: coerce (coerceViaBits ctx.oracles.alphaChal :: SizedF 128 Pallas.ScalarField)
              , beta: F (fpToFq ctx.oracles.beta)
              , gamma: F (fpToFq ctx.oracles.gamma)
              , zeta: coerce (coerceViaBits ctx.oracles.zetaChal :: SizedF 128 Pallas.ScalarField)
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
    it "PS Fr-sponge challenges (xi, evalscale) match Rust" xiCorrectTest
    it "xiCorrectCircuit verifies claimed xi" xiCorrectCircuitTest
    it "plonkChecksCircuit verifies xi, evalscale, and combined_inner_product" plonkChecksCircuitTest
    it "opening proof verifies" openingProofTest
    it "PS computeB matches Rust computeB0" computeBTest
    it "IPA rounds matches domain log2" ipaRoundsTest
    it "bCorrectCircuit verifies with Rust-provided values" bCorrectCircuitTest
    it "extractScalarChallenges circuit matches pure and Rust" extractChallengesCircuitTest
    it "bulletReduceCircuit matches Rust lr_prod" bulletReduceCircuitTest
    it "debug verify traces intermediate IPA values" debugVerifyTest
    it "ipaFinalCheckCircuit verifies with Rust proof values" ipaFinalCheckCircuitTest
    it "checkBulletproof composes transcript and IPA verification" checkBulletproofTest
    it "incrementallyVerifyProof wires all components together" incrementallyVerifyProofTest
