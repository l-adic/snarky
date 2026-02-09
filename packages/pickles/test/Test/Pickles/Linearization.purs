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

import Data.Fin (unsafeFinite)
import Data.Newtype (unwrap, wrap)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector, (!!))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (liftEffect)
import Pickles.Linearization.Env (Env, circuitEnv, fieldEnv)
import Pickles.Linearization.FFI (class LinearizationFFI, PointEval, evalLinearization, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.Linearization.FFI as FFI
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.Linearization.Types (PolishToken)
import Pickles.Linearization.Vesta as VestaTokens
import Pickles.PlonkChecks.GateConstraints (buildChallenges, buildEvalPoint, parseHex)
import Poseidon (class PoseidonField)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.CVar (CVar(..))
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class HasEndo, class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (arbitrary, quickCheckGen, (===))
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
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
  :: forall f g r
   . LinearizationFFI f g
  => { witnessEvals :: Vector 15 (PointEval f)
     , coeffEvals :: Vector 15 f
     , indexEvals :: Vector 6 (PointEval f)
     , alpha :: f
     , beta :: f
     , gamma :: f
     , jointCombiner :: f
     , zeta :: f
     | r
     }
  -> FFI.LinearizationInput f
buildFFIInput { witnessEvals, coeffEvals, indexEvals, alpha, beta, gamma, jointCombiner, zeta } =
  let
    index = unsafeFinite @6
  in
    { alpha
    , beta
    , gamma
    , jointCombiner
    , witnessEvals
    , coefficientEvals: coeffEvals
    -- Index order matches Kimchi verifier: Generic, Poseidon, CompleteAdd, VarBaseMul, EndoMul, EndoMulScalar
    -- See kimchi/src/verifier.rs lines 485-490
    , genericIndex: indexEvals !! index 0
    , poseidonIndex: indexEvals !! index 1
    , completeAddIndex: indexEvals !! index 2
    , varbasemulIndex: indexEvals !! index 3
    , endomulIndex: indexEvals !! index 4
    , endomulScalarIndex: indexEvals !! index 5
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

-- | Input record for linearization test, parameterized by element type.
-- | Use as `LinearizationInput (F f)` for values or `LinearizationInput (FVar f)` for circuit variables.
type LinearizationInput a =
  { witnessEvals :: Vector 15 (PointEval a)
  , coeffEvals :: Vector 15 a
  , indexEvals :: Vector 6 (PointEval a)
  , alpha :: a
  , beta :: a
  , gamma :: a
  , jointCombiner :: a
  , vanishesOnZk :: a
  , lagrangeFalse0 :: a
  , lagrangeTrue1 :: a
  }

-- | Circuit that evaluates the linearization polynomial (parameterized)
linearizationCircuit
  :: forall f f' t m
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => Array PolishToken
  -> LinearizationInput (FVar f)
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
  -> LinearizationInput (F f)
  -> F f
linearizationReference tokens input' =
  let
    input :: LinearizationInput f
    input = coerce input'

    evalPoint = buildEvalPoint
      { witnessEvals: input.witnessEvals
      , coeffEvals: input.coeffEvals
      , indexEvals: input.indexEvals
      , defaultVal: zero
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

    env = fieldEnv evalPoint challenges parseHex
  in
    coerce $ evaluate tokens env

-- | Generate an arbitrary PointEval
genPointEval :: forall f. PrimeField f => Gen (PointEval f)
genPointEval = do
  zeta <- arbitrary
  omegaTimesZeta <- arbitrary
  pure { zeta, omegaTimesZeta }

-- | Generate arbitrary LinearizationInput using FFI for domain-dependent values
genLinearizationInput
  :: forall f g
   . PrimeField f
  => LinearizationFFI f g
  => Gen (LinearizationInput (F f))
genLinearizationInput = do
  witnessEvals <- Vector.generator (Proxy @15) genPointEval
  coeffEvals <- genFieldVector (Proxy @15)
  indexEvals <- Vector.generator (Proxy @6) genPointEval
  alpha <- arbitrary
  beta <- arbitrary
  gamma <- arbitrary
  jointCombiner <- arbitrary
  zeta :: F f <- arbitrary

  -- Compute domain-dependent values using FFI
  let
    vanishesOnZk = wrap $ vanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: unwrap zeta }
    lagrangeFalse0 = wrap $ unnormalizedLagrangeBasis { domainLog2, zkRows: 0, offset: 0, pt: unwrap zeta }
    lagrangeTrue1 = wrap $ unnormalizedLagrangeBasis { domainLog2, zkRows, offset: -1, pt: unwrap zeta }

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
      (witnessEvals :: Vector 15 (PointEval f)) <- Vector.generator (Proxy @15) genPointEval
      coeffEvals <- genFieldVector (Proxy @15)
      (indexEvals :: Vector 6 (PointEval f)) <- Vector.generator (Proxy @6) genPointEval
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
      let rustResult = evalLinearization ffiInput

      -- Both should produce the same result
      pure $ psResult === rustResult

  it "Circuit evaluation matches field evaluation" do
    let
      circuit
        :: forall t m
         . CircuitM f (KimchiConstraint f) t m
        => LinearizationInput (FVar f)
        -> Snarky (KimchiConstraint f) t m (FVar f)
      circuit = linearizationCircuit tokens

      solver = makeSolver (Proxy @(KimchiConstraint f)) circuit

      builtState = compilePure
        (Proxy @(LinearizationInput (F f)))
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
      (genLinearizationInput :: Gen (LinearizationInput (F f)))

-------------------------------------------------------------------------------
-- | Main spec
-------------------------------------------------------------------------------

spec :: Spec Unit
spec = describe "Linearization Interpreter" do
  describe "Pallas" do
    linearizationTests (Proxy @Pallas.BaseField) PallasTokens.constantTermTokens
  describe "Vesta" do
    linearizationTests (Proxy @Vesta.BaseField) VestaTokens.constantTermTokens
