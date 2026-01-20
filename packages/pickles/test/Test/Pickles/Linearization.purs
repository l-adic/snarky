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
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.CVar (CVar(..))
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky)
import Snarky.Circuit.Types (F)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class PrimeField, fromBigInt)
import Snarky.Curves.Pallas as Pallas
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

-- | Build FFI input from vectors and challenges (for Rust comparison test)
buildFFIInput
  :: { witnessEvals :: Vector 30 Pallas.BaseField
     , coeffEvals :: Vector 15 Pallas.BaseField
     , indexEvals :: Vector 12 Pallas.BaseField
     , alpha :: Pallas.BaseField
     , beta :: Pallas.BaseField
     , gamma :: Pallas.BaseField
     , jointCombiner :: Pallas.BaseField
     , zeta :: Pallas.BaseField
     }
  -> FFI.PallasLinearizationInput
buildFFIInput { witnessEvals, coeffEvals, indexEvals, alpha, beta, gamma, jointCombiner, zeta } =
  let
    witnessArr = toUnfoldable witnessEvals :: Array Pallas.BaseField
    indexArr = toUnfoldable indexEvals :: Array Pallas.BaseField
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
    , vanishesOnZk: FFI.pallasVanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }
    , zeta
    , domainLog2
    }

-- | Generate a sized vector of arbitrary field elements
genFieldVector :: forall n. Reflectable n Int => Proxy n -> Gen (Vector n Pallas.BaseField)
genFieldVector p = Vector.generator p arbitrary

-- | Parse hex string to field element using BigInt
parseHex :: forall f. PrimeField f => String -> f
parseHex hex = case fromBigInt <$> BigInt.fromString hex of
  Nothing -> unsafeCrashWith $ "Failed to pase Hex to BigInt: " <> hex
  Just a -> a

-- | Input record for linearization circuit test (VALUE type)
-- | All sizes are statically known from Kimchi protocol parameters
-- | Using a type alias (not newtype) so CircuitType instance for Record applies
type LinearizationInput =
  { witnessEvals :: Vector 30 (F Pallas.BaseField)
  , coeffEvals :: Vector 15 (F Pallas.BaseField)
  , indexEvals :: Vector 12 (F Pallas.BaseField)
  , alpha :: F Pallas.BaseField
  , beta :: F Pallas.BaseField
  , gamma :: F Pallas.BaseField
  , jointCombiner :: F Pallas.BaseField
  , vanishesOnZk :: F Pallas.BaseField
  , lagrangeFalse0 :: F Pallas.BaseField -- UnnormalizedLagrangeBasis(false, 0)
  , lagrangeTrue1 :: F Pallas.BaseField -- UnnormalizedLagrangeBasis(true, -1)
  }

-- | VAR type corresponding to LinearizationInput
-- | This is what the circuit function receives
type LinearizationInputVar =
  { witnessEvals :: Vector 30 (FVar Pallas.BaseField)
  , coeffEvals :: Vector 15 (FVar Pallas.BaseField)
  , indexEvals :: Vector 12 (FVar Pallas.BaseField)
  , alpha :: FVar Pallas.BaseField
  , beta :: FVar Pallas.BaseField
  , gamma :: FVar Pallas.BaseField
  , jointCombiner :: FVar Pallas.BaseField
  , vanishesOnZk :: FVar Pallas.BaseField
  , lagrangeFalse0 :: FVar Pallas.BaseField
  , lagrangeTrue1 :: FVar Pallas.BaseField
  }

-- | Circuit that evaluates the linearization polynomial
-- | Takes circuit variables and returns a circuit variable
linearizationCircuit
  :: forall t m
   . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t m
  => LinearizationInputVar
  -> Snarky (KimchiConstraint Pallas.BaseField) t m (FVar Pallas.BaseField)
linearizationCircuit input =
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
    evaluate PallasTokens.constantTermTokens env

-- | Reference function for field evaluation
linearizationReference :: LinearizationInput -> F Pallas.BaseField
linearizationReference input =
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
    wrap $ evaluate PallasTokens.constantTermTokens env

-- | Generate arbitrary LinearizationInput using FFI for domain-dependent values
genLinearizationInput :: Gen LinearizationInput
genLinearizationInput = do
  witnessEvals <- map wrap <$> genFieldVector (Proxy @30)
  coeffEvals <- map wrap <$> genFieldVector (Proxy @15)
  indexEvals <- map wrap <$> genFieldVector (Proxy @12)
  alpha <- wrap <$> arbitrary
  beta <- wrap <$> arbitrary
  gamma <- wrap <$> arbitrary
  jointCombiner <- wrap <$> arbitrary
  zeta <- arbitrary :: Gen Pallas.BaseField

  -- Compute domain-dependent values using FFI
  let
    vanishesOnZk = wrap $ FFI.pallasVanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }
    lagrangeFalse0 = wrap $ FFI.pallasUnnormalizedLagrangeBasis { domainLog2, zkRows: 0, offset: 0, pt: zeta }
    lagrangeTrue1 = wrap $ FFI.pallasUnnormalizedLagrangeBasis { domainLog2, zkRows, offset: -1, pt: zeta }

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

spec :: Spec Unit
spec = describe "Linearization Interpreter" do
  it "PureScript interpreter matches Rust evaluator on arbitrary inputs" do
    liftEffect $ quickCheckGen do
      -- Generate arbitrary field elements
      witnessEvals <- genFieldVector (Proxy @30)
      coeffEvals <- genFieldVector (Proxy @15)
      indexEvals <- genFieldVector (Proxy @12)
      alpha <- arbitrary
      beta <- arbitrary
      gamma <- arbitrary
      jointCombiner <- arbitrary
      zeta <- arbitrary

      -- Build PureScript structures using FFI for domain values
      let
        vanishesOnZk = FFI.pallasVanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }
        lagrangeFalse0 = FFI.pallasUnnormalizedLagrangeBasis { domainLog2, zkRows: 0, offset: 0, pt: zeta }
        lagrangeTrue1 = FFI.pallasUnnormalizedLagrangeBasis { domainLog2, zkRows, offset: -1, pt: zeta }

      let evalPoint = buildEvalPoint { witnessEvals, coeffEvals, indexEvals, defaultVal: zero }
      let challenges = buildChallenges { alpha, beta, gamma, jointCombiner, vanishesOnZk, lagrangeFalse0, lagrangeTrue1 }
      let env = fieldEnv evalPoint challenges parseHex
      let
        psResult = (evaluate :: Array PolishToken -> Env Pallas.BaseField -> Pallas.BaseField)
          PallasTokens.constantTermTokens
          env

      -- Build FFI input for Rust
      let ffiInput = buildFFIInput { witnessEvals, coeffEvals, indexEvals, alpha, beta, gamma, jointCombiner, zeta }

      -- Call Rust evaluator
      let rustResult = FFI.evaluatePallasLinearization ffiInput

      -- Both should produce the same result
      pure $ psResult === rustResult

  it "Circuit evaluation matches field evaluation" do
    let
      solver = makeSolver (Proxy @(KimchiConstraint Pallas.BaseField)) linearizationCircuit

      builtState = compilePure
        (Proxy @LinearizationInput)
        (Proxy @(F Pallas.BaseField))
        (Proxy @(KimchiConstraint Pallas.BaseField))
        linearizationCircuit
        Kimchi.initialState

    circuitSpecPure'
      { builtState
      , checker: Kimchi.eval
      , solver
      , testFunction: satisfied linearizationReference
      , postCondition: Kimchi.postCondition
      }
      genLinearizationInput
