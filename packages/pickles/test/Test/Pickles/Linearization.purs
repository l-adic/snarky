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

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap, wrap)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector, toUnfoldable)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafeCrashWith)
import Pickles.Linearization.Env (Challenges, Env, EvalPoint, circuitEnv, fieldEnv)
import Pickles.Linearization.FFI as FFI
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.Linearization.Types (CurrOrNext(..), GateType(..), PolishToken)
import Pickles.Linearization.Vesta as VestaTokens
import Poseidon (class PoseidonField)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.CVar (CVar(..))
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky)
import Snarky.Circuit.Types (F)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class HasEndo, class PrimeField, fromBigInt)
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
-- | Curve-specific FFI operations record
-------------------------------------------------------------------------------

-- | Record type to abstract over curve-specific linearization FFI operations
type LinearizationFFI f =
  { evaluateLinearization ::
      { alpha :: f
      , beta :: f
      , gamma :: f
      , jointCombiner :: f
      , witnessEvals :: Array f
      , coefficientEvals :: Array f
      , poseidonIndex :: Array f
      , genericIndex :: Array f
      , varbasemulIndex :: Array f
      , endomulIndex :: Array f
      , endomulScalarIndex :: Array f
      , completeAddIndex :: Array f
      , vanishesOnZk :: f
      , zeta :: f
      , domainLog2 :: Int
      }
      -> f
  , unnormalizedLagrangeBasis ::
      { domainLog2 :: Int
      , zkRows :: Int
      , offset :: Int
      , pt :: f
      }
      -> f
  , vanishesOnZkAndPreviousRows ::
      { domainLog2 :: Int
      , zkRows :: Int
      , pt :: f
      }
      -> f
  , constantTermTokens :: Array PolishToken
  }

pallasLinearizationFFI :: LinearizationFFI Pallas.BaseField
pallasLinearizationFFI =
  { evaluateLinearization: FFI.evaluatePallasLinearization
  , unnormalizedLagrangeBasis: FFI.pallasUnnormalizedLagrangeBasis
  , vanishesOnZkAndPreviousRows: FFI.pallasVanishesOnZkAndPreviousRows
  , constantTermTokens: PallasTokens.constantTermTokens
  }

vestaLinearizationFFI :: LinearizationFFI Vesta.BaseField
vestaLinearizationFFI =
  { evaluateLinearization: FFI.evaluateVestaLinearization
  , unnormalizedLagrangeBasis: FFI.vestaUnnormalizedLagrangeBasis
  , vanishesOnZkAndPreviousRows: FFI.vestaVanishesOnZkAndPreviousRows
  , constantTermTokens: VestaTokens.constantTermTokens
  }

-------------------------------------------------------------------------------
-- | Helper functions (parameterized)
-------------------------------------------------------------------------------

-- | Build EvalPoint from witness/coefficient/index vectors
-- | Witness: 30 elements (15 cols × 2 curr/next)
-- | Coefficients: 15 elements
-- | Index: 12 elements (6 gate types × 2 curr/next)
buildEvalPoint
  :: forall a
   . { witnessEvals :: Vector 30 a
     , coeffEvals :: Vector 15 a
     , indexEvals :: Vector 12 a
     , defaultVal :: a
     }
  -> EvalPoint a
buildEvalPoint { witnessEvals, coeffEvals, indexEvals, defaultVal } =
  let
    -- Convert to arrays for Int-based indexing
    witnessArr = toUnfoldable witnessEvals :: Array a
    coeffArr = toUnfoldable coeffEvals :: Array a
    indexArr = toUnfoldable indexEvals :: Array a
  in
    { witness: \row col ->
        let
          rowOffset = case row of
            Curr -> 0
            Next -> 1
          idx = col * 2 + rowOffset
        in
          fromMaybe defaultVal (Array.index witnessArr idx)
    , coefficient: \col ->
        fromMaybe defaultVal (Array.index coeffArr col)
    , index: \row gt ->
        let
          gateIdx = case gt of
            Poseidon -> 0
            Generic -> 1
            VarBaseMul -> 2
            EndoMul -> 3
            EndoMulScalar -> 4
            CompleteAdd -> 5
            _ -> 0
          rowOffset = case row of
            Curr -> 0
            Next -> 1
          idx = gateIdx * 2 + rowOffset
        in
          fromMaybe defaultVal (Array.index indexArr idx)
    , lookupAggreg: \_ -> defaultVal
    , lookupSorted: \_ _ -> defaultVal
    , lookupTable: \_ -> defaultVal
    , lookupRuntimeTable: \_ -> defaultVal
    , lookupRuntimeSelector: \_ -> defaultVal
    , lookupKindIndex: \_ -> defaultVal
    }

-- | Build Challenges with precomputed domain-dependent values
-- | The two UnnormalizedLagrangeBasis calls in the linearization are:
-- |   { zk_rows: false, offset: 0 }
-- |   { zk_rows: true, offset: -1 }
buildChallenges
  :: forall a
   . { alpha :: a
     , beta :: a
     , gamma :: a
     , jointCombiner :: a
     , vanishesOnZk :: a
     , lagrangeFalse0 :: a -- unnormalizedLagrangeBasis(false, 0)
     , lagrangeTrue1 :: a -- unnormalizedLagrangeBasis(true, -1)
     }
  -> Challenges a
buildChallenges { alpha, beta, gamma, jointCombiner, vanishesOnZk, lagrangeFalse0, lagrangeTrue1 } =
  { alpha
  , beta
  , gamma
  , jointCombiner
  , vanishesOnZeroKnowledgeAndPreviousRows: vanishesOnZk
  , unnormalizedLagrangeBasis: \{ zkRows: zk, offset } ->
      -- Match the two known calls in the linearization expression
      if not zk && offset == 0 then lagrangeFalse0
      else if zk && offset == (-1) then lagrangeTrue1
      else lagrangeFalse0 -- Default (shouldn't happen)
  }

-- | Build FFI input from vectors and challenges (parameterized)
buildFFIInput
  :: forall f
   . LinearizationFFI f
  -> { witnessEvals :: Vector 30 f
     , coeffEvals :: Vector 15 f
     , indexEvals :: Vector 12 f
     , alpha :: f
     , beta :: f
     , gamma :: f
     , jointCombiner :: f
     , zeta :: f
     }
  -> { alpha :: f
     , beta :: f
     , gamma :: f
     , jointCombiner :: f
     , witnessEvals :: Array f
     , coefficientEvals :: Array f
     , poseidonIndex :: Array f
     , genericIndex :: Array f
     , varbasemulIndex :: Array f
     , endomulIndex :: Array f
     , endomulScalarIndex :: Array f
     , completeAddIndex :: Array f
     , vanishesOnZk :: f
     , zeta :: f
     , domainLog2 :: Int
     }
buildFFIInput ffi { witnessEvals, coeffEvals, indexEvals, alpha, beta, gamma, jointCombiner, zeta } =
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
    , vanishesOnZk: ffi.vanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }
    , zeta
    , domainLog2
    }

-- | Generate a sized vector of arbitrary field elements
genFieldVector :: forall f n. PrimeField f => Reflectable n Int => Proxy n -> Gen (Vector n f)
genFieldVector p = Vector.generator p arbitrary

-- | Parse hex string to field element using BigInt
parseHex :: forall f. PrimeField f => String -> f
parseHex hex = case fromBigInt <$> BigInt.fromString hex of
  Nothing -> unsafeCrashWith $ "Failed to parse Hex to BigInt: " <> hex
  Just a -> a

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
  => LinearizationFFI f
  -> LinearizationInputVar f
  -> Snarky (KimchiConstraint f) t m (FVar f)
linearizationCircuit ffi input =
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
    -- Evaluate the linearization polynomial using circuit operations
    evaluate ffi.constantTermTokens env

-- | Reference function for field evaluation (parameterized)
linearizationReference
  :: forall f f'
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => LinearizationFFI f
  -> LinearizationInput f
  -> F f
linearizationReference ffi input =
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
    wrap $ evaluate ffi.constantTermTokens env

-- | Generate arbitrary LinearizationInput using FFI for domain-dependent values
genLinearizationInput
  :: forall f
   . PrimeField f
  => LinearizationFFI f
  -> Gen (LinearizationInput f)
genLinearizationInput ffi = do
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
    vanishesOnZk = wrap $ ffi.vanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }
    lagrangeFalse0 = wrap $ ffi.unnormalizedLagrangeBasis { domainLog2, zkRows: 0, offset: 0, pt: zeta }
    lagrangeTrue1 = wrap $ ffi.unnormalizedLagrangeBasis { domainLog2, zkRows, offset: -1, pt: zeta }

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
  :: forall f f'
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => Kimchi.KimchiVerify f f'
  => Proxy f
  -> LinearizationFFI f
  -> Spec Unit
linearizationTests _ ffi = do
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
        vanishesOnZk = ffi.vanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }
        lagrangeFalse0 = ffi.unnormalizedLagrangeBasis { domainLog2, zkRows: 0, offset: 0, pt: zeta }
        lagrangeTrue1 = ffi.unnormalizedLagrangeBasis { domainLog2, zkRows, offset: -1, pt: zeta }

      let evalPoint = buildEvalPoint { witnessEvals, coeffEvals, indexEvals, defaultVal: zero }
      let challenges = buildChallenges { alpha, beta, gamma, jointCombiner, vanishesOnZk, lagrangeFalse0, lagrangeTrue1 }
      let env = fieldEnv evalPoint challenges parseHex
      let
        psResult = (evaluate :: Array PolishToken -> Env f -> f)
          ffi.constantTermTokens
          env

      -- Build FFI input for Rust
      let ffiInput = buildFFIInput ffi { witnessEvals, coeffEvals, indexEvals, alpha, beta, gamma, jointCombiner, zeta }

      -- Call Rust evaluator
      let rustResult = ffi.evaluateLinearization ffiInput

      -- Both should produce the same result
      pure $ psResult === rustResult

  it "Circuit evaluation matches field evaluation" do
    let
      circuit
        :: forall t m
         . CircuitM f (KimchiConstraint f) t m
        => LinearizationInputVar f
        -> Snarky (KimchiConstraint f) t m (FVar f)
      circuit = linearizationCircuit ffi

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
      , testFunction: satisfied (linearizationReference ffi)
      , postCondition: Kimchi.postCondition
      }
      (genLinearizationInput ffi)

-------------------------------------------------------------------------------
-- | Main spec
-------------------------------------------------------------------------------

spec :: Spec Unit
spec = describe "Linearization Interpreter" do
  describe "Pallas" do
    linearizationTests (Proxy @Pallas.BaseField) pallasLinearizationFFI
  describe "Vesta" do
    linearizationTests (Proxy @Vesta.BaseField) vestaLinearizationFFI
