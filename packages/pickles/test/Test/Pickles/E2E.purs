module Test.Pickles.E2E
  ( computePublicEval
  , gateConstraintTest
  , permutationTest
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
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Identity (Identity(..))
import Data.Maybe (fromJust)
import Data.Newtype (un)
import Data.Schnorr.Gen (VerifyInput, genValidSignature)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (error)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (evalCoefficientPolys, evalLinearization, evalSelectorPolys, evalWitnessPolys, proverIndexDomainLog2, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.PlonkChecks.GateConstraints (buildChallenges, buildEvalPoint, parseHex)
import Pickles.PlonkChecks.Permutation (permContribution)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, compilePure, makeSolver, runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (createCRS, createProverIndex)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky)
import Snarky.Circuit.Schnorr (SignatureVar(..), verifies)
import Snarky.Circuit.Types (F)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (endoBase, fromBigInt, generator, pow, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.Linearization (buildFFIInput)
import Test.Pickles.ProofFFI as ProofFFI
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Spec (Spec, describe, it)
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
-- | Tests
-------------------------------------------------------------------------------

-- | Test that PureScript linearization matches Rust for a valid Schnorr circuit.
-- | Uses Pallas linearization (Fp) with a Schnorr circuit over Vesta scalar field
-- | (which equals Pallas base field = Fp).
-- |
-- | Note: The linearization polynomial does NOT evaluate to zero at an arbitrary
-- | point zeta. It evaluates to t(zeta) * Z_H(zeta) where t is the quotient
-- | polynomial. What we test here is that our PureScript interpreter produces
-- | the same result as Rust when given real circuit witness evaluations.
gateConstraintTest :: Spec Unit
gateConstraintTest = do
  it "PS gate constraint evaluation matches Rust for valid Schnorr witness" do
    let gen = genValidSignature (Proxy @Pallas.G) (Proxy @4)

    -- Generate a valid input and run the solver
    input <- liftEffect $ randomSampleOne gen
    crs <- liftEffect $ createCRS @Vesta.ScalarField

    -- Run the solver
    let
      nat :: Identity ~> Effect
      nat = pure <<< un Identity

    eRes <- liftEffect $ runSolverT (\a -> hoist nat $ schnorrSolver a) input
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
          { witness, publicInputs: _ } = makeWitness
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

        -- Generate random challenges
        zeta <- liftEffect $ randomSampleOne (arbitrary @Vesta.ScalarField)
        alpha <- liftEffect $ randomSampleOne (arbitrary @Vesta.ScalarField)
        beta <- liftEffect $ randomSampleOne (arbitrary @Vesta.ScalarField)
        gamma <- liftEffect $ randomSampleOne (arbitrary @Vesta.ScalarField)
        jointCombiner <- liftEffect $ randomSampleOne (arbitrary @Vesta.ScalarField)

        let
          -- Compute evaluations using FFI from prover index
          witnessEvals = evalWitnessPolys proverIndex witness zeta
          coeffEvals = evalCoefficientPolys proverIndex zeta
          indexEvals = evalSelectorPolys proverIndex zeta

          -- Domain log2 from prover index
          domainLog2 = proverIndexDomainLog2 proverIndex

          -- Compute domain-dependent values
          vanishesOnZk' = vanishesOnZkAndPreviousRows
            { domainLog2, zkRows, pt: zeta }
          lagrangeFalse0 = unnormalizedLagrangeBasis
            { domainLog2, zkRows: 0, offset: 0, pt: zeta }
          lagrangeTrue1 = unnormalizedLagrangeBasis
            { domainLog2, zkRows, offset: -1, pt: zeta }

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
            , domainLog2
            }

          -- Evaluate using Rust
          rustResult = evalLinearization ffiInput

        -- PureScript should match Rust
        liftEffect $ psResult `shouldEqual` rustResult

-------------------------------------------------------------------------------
-- | Permutation E2E test
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

-- | Test that PureScript permContribution matches the oracle ft_eval0 value.
-- |
-- | Verifies: permContribution = ftEval0 - publicEval + gateConstraints
-- |
-- | This uses a real proof created from the Schnorr circuit, with oracles
-- | derived via Fiat-Shamir, ensuring the permutation argument implementation
-- | is correct against the Kimchi prover.
permutationTest :: Spec Unit
permutationTest = do
  it "PS permContribution matches ftEval0 - publicEval + gateConstraints" do
    let gen = genValidSignature (Proxy @Pallas.G) (Proxy @4)

    -- Generate a valid input and run the solver
    input <- liftEffect $ randomSampleOne gen
    crs <- liftEffect $ createCRS @Vesta.ScalarField

    let
      nat :: Identity ~> Effect
      nat = pure <<< un Identity

    eRes <- liftEffect $ runSolverT (\a -> hoist nat $ schnorrSolver a) input
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

        -- Create a real proof and get oracles via Fiat-Shamir
        let
          proof = ProofFFI.createProof { proverIndex, witness }
          oracles = ProofFFI.proofOracles proverIndex { proof, publicInput: publicInputs }

        -- Get proof evaluations
        let
          witnessEvals = ProofFFI.proofWitnessEvals proof
          zEvals = ProofFFI.proofZEvals proof
          sigmaEvals = ProofFFI.proofSigmaEvals proof
          shifts = ProofFFI.proverIndexShifts proverIndex
          domainLog2 = proverIndexDomainLog2 proverIndex

        -- Compute domain-related values for permutation
        let
          n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt domainLog2)
          omega = ProofFFI.domainGenerator domainLog2
          zetaToNMinus1 = pow oracles.zeta n - one
          zkPoly = ProofFFI.permutationVanishingPolynomial
            { domainLog2, zkRows, pt: oracles.zeta }
          omegaToMinusZkRows = pow omega (n - BigInt.fromInt zkRows)

        -- Build permutation input and compute contribution
        let
          permInput =
            { w: map _.zeta (Vector.take @7 witnessEvals)
            , sigma: map _.zeta sigmaEvals
            , z: zEvals
            , shifts
            , alpha: oracles.alpha
            , beta: oracles.beta
            , gamma: oracles.gamma
            , zkPolynomial: zkPoly
            , zetaToNMinus1
            , omegaToMinusZkRows
            , zeta: oracles.zeta
            }
          permResult = permContribution permInput

        -- Compute gate constraints using proof witness evals
        let
          coeffEvals = evalCoefficientPolys proverIndex oracles.zeta
          indexEvals = evalSelectorPolys proverIndex oracles.zeta
          vanishesOnZk' = vanishesOnZkAndPreviousRows
            { domainLog2, zkRows, pt: oracles.zeta }
          lagrangeFalse0 = unnormalizedLagrangeBasis
            { domainLog2, zkRows: 0, offset: 0, pt: oracles.zeta }
          lagrangeTrue1 = unnormalizedLagrangeBasis
            { domainLog2, zkRows, offset: -1, pt: oracles.zeta }
          evalPoint = buildEvalPoint
            { witnessEvals
            , coeffEvals
            , indexEvals
            , defaultVal: zero
            }
          challenges = buildChallenges
            { alpha: oracles.alpha
            , beta: oracles.beta
            , gamma: oracles.gamma
            , jointCombiner: zero
            , vanishesOnZk: vanishesOnZk'
            , lagrangeFalse0
            , lagrangeTrue1
            }
          env = fieldEnv evalPoint challenges parseHex
          gateResult = evaluate PallasTokens.constantTermTokens env

        -- Compute public input polynomial evaluation
        let publicEval = computePublicEval publicInputs domainLog2 oracles.zeta

        -- Verify: permContribution = ftEval0 - publicEval + gateConstraints
        -- (The verifier subtracts -p(zeta) from ft_eval0, adding p(zeta),
        --  so permContrib = ft_eval0 - p(zeta) + gateConstTerm)
        liftEffect $ permResult `shouldEqual` (oracles.ftEval0 - publicEval + gateResult)

-------------------------------------------------------------------------------
-- | Main spec
-------------------------------------------------------------------------------

spec :: Spec Unit
spec = describe "E2E Schnorr Circuit" do
  describe "Gate Constraints" do
    gateConstraintTest
  describe "Permutation" do
    permutationTest
