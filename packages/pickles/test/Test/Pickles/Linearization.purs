module Test.Pickles.Linearization where

-- | This module tests the equivalence of the PureScript Kimchi linearization
-- | interpreter against the Rust FFI evaluator.
-- |
-- | The `buildEvalPoint` function uses a `defaultVal` parameter. This parameter
-- | serves as a fallback for any column evaluations that are not explicitly
-- | provided by the test inputs (e.g., `witnessEvals`, `coeffEvals`,
-- | `indexEvals`). For specific lookup-related evaluations, `defaultVal` is
-- | always returned.
-- |
-- | By typically setting `defaultVal` to `zero` (the field's zero element),
-- | this test effectively asserts the equivalence of the linearization
-- | polynomial in a "vanilla" proof system configuration. In this configuration,
-- | features like lookups, which are not explicitly provided or relevant to the
-- | `constantTermTokens` being evaluated, are treated as "off" or "zeroed out".
-- | This is consistent with the Rust FFI evaluator's internal logic, which
-- | treats all feature flags as disabled to match the OCaml implementation.
-- | For example, if the Kimchi linearization in `constantTermTokens` refers to
-- | a lookup column, its value in this test will be zero, as if the lookup
-- | feature were disabled.

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Morph (hoist)
import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Identity (Identity(..))
import Data.Maybe (fromJust)
import Data.Newtype (un, unwrap, wrap)
import Data.Reflectable (class Reflectable)
import Data.Schnorr.Gen (VerifyInput, genValidSignature)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, toUnfoldable)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (error)
import Partial.Unsafe (unsafePartial)
import Pickles.Linearization.Env (Env, circuitEnv, fieldEnv)
import Pickles.Linearization.FFI (class LinearizationFFI, evaluateLinearization, proverIndexCoefficientEvaluations, proverIndexSelectorEvaluations, proverIndexWitnessEvaluations, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.Linearization.FFI as FFI
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.Linearization.Types (PolishToken)
import Pickles.Linearization.Vesta as VestaTokens
import Pickles.PlonkChecks.GateConstraints (buildChallenges, buildEvalPoint, parseHex)
import Poseidon (class PoseidonField)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, compilePure, makeSolver, runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (createCRS, createProverIndex)
import Snarky.Circuit.CVar (CVar(..), const_)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky)
import Snarky.Circuit.Schnorr (SignatureVar(..), verifies)
import Snarky.Circuit.Types (F)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (class HasEndo, class PrimeField, endoBase, generator, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.QuickCheck (arbitrary, quickCheckGen, (===))
import Test.QuickCheck.Gen (Gen, randomSampleOne)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main =
  runSpecAndExitProcess [ consoleReporter ] do
    spec

-- Standard Kimchi constants
domainLog2 :: Int
domainLog2 = 16

zkRows :: Int
zkRows = 3

-------------------------------------------------------------------------------
-- | Helper functions (test-specific)
-------------------------------------------------------------------------------

-- | Build FFI input from vectors and challenges
buildFFIInput
  :: forall f g
   . LinearizationFFI f g
  => { witnessEvals :: Vector 30 f
     , coeffEvals :: Vector 15 f
     , indexEvals :: Vector 12 f
     , alpha :: f
     , beta :: f
     , gamma :: f
     , jointCombiner :: f
     , zeta :: f
     }
  -> FFI.LinearizationInput f
buildFFIInput { witnessEvals, coeffEvals, indexEvals, alpha, beta, gamma, jointCombiner, zeta } =
  let
    witnessArr = toUnfoldable witnessEvals :: Array f
    indexArr = toUnfoldable indexEvals :: Array f
  in
    { alpha
    , beta
    , gamma
    , jointCombiner
    , witnessEvals: witnessArr
    , coefficientEvals: toUnfoldable coeffEvals
    , poseidonIndex: Array.slice 0 2 indexArr
    , genericIndex: Array.slice 2 4 indexArr
    , varbasemulIndex: Array.slice 4 6 indexArr
    , endomulIndex: Array.slice 6 8 indexArr
    , endomulScalarIndex: Array.slice 8 10 indexArr
    , completeAddIndex: Array.slice 10 12 indexArr
    , vanishesOnZk: vanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }
    , zeta
    , domainLog2
    }

-- | Generate a sized vector of arbitrary field elements
genFieldVector :: forall f n. PrimeField f => Reflectable n Int => Proxy n -> Gen (Vector n f)
genFieldVector p = Vector.generator p arbitrary

-------------------------------------------------------------------------------
-- | Parameterized test types and functions
-------------------------------------------------------------------------------

-- | Input record for linearization circuit test (VALUE type)
-- | All sizes are statically known from Kimchi protocol parameters
type LinearizationInput f =
  { witnessEvals :: Vector 30 (F f)
  , coeffEvals :: Vector 15 (F f)
  , indexEvals :: Vector 12 (F f)
  , alpha :: F f
  , beta :: F f
  , gamma :: F f
  , jointCombiner :: F f
  , vanishesOnZk :: F f
  , lagrangeFalse0 :: F f -- UnnormalizedLagrangeBasis(false, 0)
  , lagrangeTrue1 :: F f -- UnnormalizedLagrangeBasis(true, -1)
  }

-- | VAR type corresponding to LinearizationInput
type LinearizationInputVar f =
  { witnessEvals :: Vector 30 (FVar f)
  , coeffEvals :: Vector 15 (FVar f)
  , indexEvals :: Vector 12 (FVar f)
  , alpha :: FVar f
  , beta :: FVar f
  , gamma :: FVar f
  , jointCombiner :: FVar f
  , vanishesOnZk :: FVar f
  , lagrangeFalse0 :: FVar f
  , lagrangeTrue1 :: FVar f
  }

-- | Circuit that evaluates the linearization polynomial (parameterized)
linearizationCircuit
  :: forall f f' t m
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => Array PolishToken
  -> LinearizationInputVar f
  -> Snarky (KimchiConstraint f) t m (FVar f)
linearizationCircuit tokens input =
  let
    evalPoint = buildEvalPoint
      { witnessEvals: input.witnessEvals
      , coeffEvals: input.coeffEvals
      , indexEvals: input.indexEvals
      , defaultVal: Const zero
      }

    challenges = buildChallenges
      { alpha: input.alpha
      , beta: input.beta
      , gamma: input.gamma
      , jointCombiner: input.jointCombiner
      , vanishesOnZk: input.vanishesOnZk
      , lagrangeFalse0: input.lagrangeFalse0
      , lagrangeTrue1: input.lagrangeTrue1
      }

    env = circuitEnv evalPoint challenges parseHex
  in
    evaluate tokens env

-- | Reference function for field evaluation (parameterized)
linearizationReference
  :: forall f f'
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => Array PolishToken
  -> LinearizationInput f
  -> F f
linearizationReference tokens input =
  let
    evalPoint = buildEvalPoint
      { witnessEvals: map unwrap input.witnessEvals
      , coeffEvals: map unwrap input.coeffEvals
      , indexEvals: map unwrap input.indexEvals
      , defaultVal: zero
      }

    challenges = buildChallenges
      { alpha: unwrap input.alpha
      , beta: unwrap input.beta
      , gamma: unwrap input.gamma
      , jointCombiner: unwrap input.jointCombiner
      , vanishesOnZk: unwrap input.vanishesOnZk
      , lagrangeFalse0: unwrap input.lagrangeFalse0
      , lagrangeTrue1: unwrap input.lagrangeTrue1
      }

    env = fieldEnv evalPoint challenges parseHex
  in
    wrap $ evaluate tokens env

-- | Generate arbitrary LinearizationInput using FFI for domain-dependent values
genLinearizationInput
  :: forall f g
   . PrimeField f
  => LinearizationFFI f g
  => Gen (LinearizationInput f)
genLinearizationInput = do
  witnessEvals <- map wrap <$> genFieldVector (Proxy @30)
  coeffEvals <- map wrap <$> genFieldVector (Proxy @15)
  indexEvals <- map wrap <$> genFieldVector (Proxy @12)
  alpha <- wrap <$> arbitrary
  beta <- wrap <$> arbitrary
  gamma <- wrap <$> arbitrary
  jointCombiner <- wrap <$> arbitrary
  zeta <- arbitrary

  -- Compute domain-dependent values using FFI
  let
    vanishesOnZk = wrap $ vanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }
    lagrangeFalse0 = wrap $ unnormalizedLagrangeBasis { domainLog2, zkRows: 0, offset: 0, pt: zeta }
    lagrangeTrue1 = wrap $ unnormalizedLagrangeBasis { domainLog2, zkRows, offset: -1, pt: zeta }

  pure
    { witnessEvals
    , coeffEvals
    , indexEvals
    , alpha
    , beta
    , gamma
    , jointCombiner
    , vanishesOnZk
    , lagrangeFalse0
    , lagrangeTrue1
    }

-------------------------------------------------------------------------------
-- | Parameterized test suite
-------------------------------------------------------------------------------

linearizationTests
  :: forall f f' g
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => Kimchi.KimchiVerify f f'
  => LinearizationFFI f g
  => Proxy f
  -> Array PolishToken
  -> Spec Unit
linearizationTests _ tokens = do
  it "PureScript interpreter matches Rust evaluator on arbitrary inputs" do
    liftEffect $ quickCheckGen do
      -- Generate arbitrary field elements
      (witnessEvals :: Vector 30 f) <- genFieldVector (Proxy @30)
      coeffEvals <- genFieldVector (Proxy @15)
      indexEvals <- genFieldVector (Proxy @12)
      alpha <- arbitrary
      beta <- arbitrary
      gamma <- arbitrary
      jointCombiner <- arbitrary
      zeta <- arbitrary

      -- Build PureScript structures using FFI for domain values
      let
        vanishesOnZk' = vanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }
        lagrangeFalse0 = unnormalizedLagrangeBasis { domainLog2, zkRows: 0, offset: 0, pt: zeta }
        lagrangeTrue1 = unnormalizedLagrangeBasis { domainLog2, zkRows, offset: -1, pt: zeta }

      let evalPoint = buildEvalPoint { witnessEvals, coeffEvals, indexEvals, defaultVal: zero }
      let challenges = buildChallenges { alpha, beta, gamma, jointCombiner, vanishesOnZk: vanishesOnZk', lagrangeFalse0, lagrangeTrue1 }
      let env = fieldEnv evalPoint challenges parseHex
      let
        psResult = (evaluate :: Array PolishToken -> Env f -> f)
          tokens
          env

      -- Build FFI input for Rust
      let ffiInput = buildFFIInput { witnessEvals, coeffEvals, indexEvals, alpha, beta, gamma, jointCombiner, zeta }

      -- Call Rust evaluator
      let rustResult = evaluateLinearization ffiInput

      -- Both should produce the same result
      pure $ psResult === rustResult

  it "Circuit evaluation matches field evaluation" do
    let
      circuit
        :: forall t m
         . CircuitM f (KimchiConstraint f) t m
        => LinearizationInputVar f
        -> Snarky (KimchiConstraint f) t m (FVar f)
      circuit = linearizationCircuit tokens

      solver = makeSolver (Proxy @(KimchiConstraint f)) circuit

      builtState = compilePure
        (Proxy @(LinearizationInput f))
        (Proxy @(F f))
        (Proxy @(KimchiConstraint f))
        circuit
        Kimchi.initialState

    circuitSpecPure' 1
      { builtState
      , checker: Kimchi.eval
      , solver
      , testFunction: satisfied (linearizationReference tokens)
      , postCondition: Kimchi.postCondition
      }
      (genLinearizationInput :: Gen (LinearizationInput f))

-------------------------------------------------------------------------------
-- | Test linearization for valid Schnorr circuit witness
-------------------------------------------------------------------------------

-- | Test that PureScript linearization matches Rust for a valid Schnorr circuit.
-- | Uses Pallas linearization (Fp) with a Schnorr circuit over Vesta scalar field
-- | (which equals Pallas base field = Fp).
-- |
-- | Note: The linearization polynomial does NOT evaluate to zero at an arbitrary
-- | point zeta. It evaluates to t(zeta) * Z_H(zeta) where t is the quotient
-- | polynomial. What we test here is that our PureScript interpreter produces
-- | the same result as Rust when given real circuit witness evaluations.
validWitnessLinearizationTest :: Spec Unit
validWitnessLinearizationTest = do
  it "Pallas linearization: PS interpreter matches Rust for valid Schnorr witness" do
    let
      -- Schnorr circuit function over Vesta.ScalarField (= Pallas.BaseField = Fp)
      genPointVar :: AffinePoint (FVar Vesta.ScalarField)
      genPointVar =
        let
          { x, y } = unsafePartial fromJust $ toAffine (generator @_ @Pallas.G)
        in
          { x: const_ x, y: const_ y }

      circuit
        :: forall t
         . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t Identity
        => VerifyInput 4 (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField)
        -> Snarky (KimchiConstraint Vesta.ScalarField) t Identity (BoolVar Vesta.ScalarField)
      circuit { signature: { r: sigR, s: sigS }, publicKey, message } =
        let
          signature = SignatureVar { r: sigR, s: sigS }
        in
          verifies @51 genPointVar { signature, publicKey, message }

      solver :: Solver Vesta.ScalarField (KimchiGate Vesta.ScalarField) (VerifyInput 4 (F Vesta.ScalarField) Boolean) Boolean
      solver = makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit

      -- Compile the circuit
      builtState :: CircuitBuilderState (KimchiGate Vesta.ScalarField) (AuxState Vesta.ScalarField)
      builtState = compilePure
        (Proxy @(VerifyInput 4 (F Vesta.ScalarField) Boolean))
        (Proxy @Boolean)
        (Proxy @(KimchiConstraint Vesta.ScalarField))
        circuit
        Kimchi.initialState

      gen = genValidSignature (Proxy @Pallas.G) (Proxy @4)

    -- Generate a valid input and run the solver
    input <- liftEffect $ randomSampleOne gen
    crs <- liftEffect $ createCRS @Vesta.ScalarField

    -- Run the solver
    let
      nat :: Identity ~> Effect
      nat = pure <<< un Identity

    eRes <- liftEffect $ runSolverT (\a -> hoist nat $ solver a) input
    case eRes of
      Left e -> liftEffect $ throwError $ error (show e)
      Right (Tuple _ assignments) -> do
        let
          -- Build constraint system and witness
          { constraintSystem, constraints } = makeConstraintSystem @Vesta.ScalarField
            { constraints: concatMap toKimchiRows builtState.constraints
            , publicInputs: builtState.publicInputs
            , unionFind: (un AuxState builtState.aux).wireState.unionFind
            }
          { witness, publicInputs: _ } = makeWitness
            { assignments
            , constraints: map _.variables constraints
            , publicInputs: builtState.publicInputs
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
          -- Get witness columns as Array (Array f) for FFI
          witnessColumns :: Array (Array Vesta.ScalarField)
          witnessColumns = toUnfoldable witness

          -- Compute evaluations using FFI from prover index
          witnessEvals = concatMap (\r -> [ r.zeta, r.omegaTimesZeta ])
            $ proverIndexWitnessEvaluations { proverIndex, witnessColumns, zeta }
          coeffEvals = proverIndexCoefficientEvaluations
            { proverIndex, zeta }
          indexEvals = concatMap (\r -> [ r.zeta, r.omegaTimesZeta ])
            $ proverIndexSelectorEvaluations { proverIndex, zeta }

          -- Domain log2 is determined by the circuit size
          domainLog2' = 16

          -- Compute domain-dependent values
          vanishesOnZk' = vanishesOnZkAndPreviousRows
            { domainLog2: domainLog2', zkRows, pt: zeta }
          lagrangeFalse0 = unnormalizedLagrangeBasis
            { domainLog2: domainLog2', zkRows: 0, offset: 0, pt: zeta }
          lagrangeTrue1 = unnormalizedLagrangeBasis
            { domainLog2: domainLog2', zkRows, offset: -1, pt: zeta }

          -- Build PureScript evaluation structures
          witnessEvalsV = unsafePartial fromJust $ Vector.toVector @30 witnessEvals
          coeffEvalsV = unsafePartial fromJust $ Vector.toVector @15 coeffEvals
          indexEvalsV = unsafePartial fromJust $ Vector.toVector @12 indexEvals

          evalPoint = buildEvalPoint
            { witnessEvals: witnessEvalsV
            , coeffEvals: coeffEvalsV
            , indexEvals: indexEvalsV
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
            { witnessEvals: witnessEvalsV
            , coeffEvals: coeffEvalsV
            , indexEvals: indexEvalsV
            , alpha
            , beta
            , gamma
            , jointCombiner
            , zeta
            }

          -- Evaluate using Rust
          rustResult = evaluateLinearization ffiInput

        -- PureScript should match Rust
        liftEffect $ psResult `shouldEqual` rustResult

-------------------------------------------------------------------------------
-- | Main spec
-------------------------------------------------------------------------------

spec :: Spec Unit
spec = describe "Linearization Interpreter" do
  describe "Pallas" do
    linearizationTests (Proxy @Pallas.BaseField) PallasTokens.constantTermTokens
  describe "Vesta" do
    linearizationTests (Proxy @Vesta.BaseField) VestaTokens.constantTermTokens
  describe "Real Circuit Evaluation" do
    validWitnessLinearizationTest
