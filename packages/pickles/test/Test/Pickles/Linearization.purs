module Test.Pickles.Linearization where

import Prelude

import Data.Array as Array
import Data.Maybe (fromMaybe)
import Data.Traversable (sequence)
import Effect (Effect)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Pickles.Linearization.Env (Challenges, Env, EvalPoint, fieldEnv)
import Pickles.Linearization.FFI as FFI
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.Linearization.Types (CurrOrNext(..), GateType(..), PolishToken)
import Snarky.Curves.Class (class PrimeField, fromBigInt)
import Snarky.Curves.Pallas as Pallas
import Test.QuickCheck (arbitrary, quickCheckGen, (===))
import Test.QuickCheck.Gen (Gen)
import Test.Spec (Spec, describe, it)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main :: Effect Unit
main =
  runSpecAndExitProcess [ consoleReporter ] do
    spec

-- Standard Kimchi constants
domainLog2 :: Int
domainLog2 = 16

zkRows :: Int
zkRows = 3

-- | Build EvalPoint from arbitrary witness/coefficient/index arrays
buildEvalPoint
  :: Array Pallas.BaseField -- 30 witness evals (15 cols * 2 for curr/next)
  -> Array Pallas.BaseField -- 15 coefficient evals
  -> Array Pallas.BaseField -- 12 index evals (6 gate types * 2 for curr/next)
  -> EvalPoint Pallas.BaseField
buildEvalPoint witnessEvals coeffEvals indexEvals =
  { witness: \row col ->
      let
        rowOffset = case row of
          Curr -> 0
          Next -> 1
        idx = col * 2 + rowOffset
      in
        fromMaybe zero (Array.index witnessEvals idx)
  , coefficient: \col ->
      fromMaybe zero (Array.index coeffEvals col)
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
        fromMaybe zero (Array.index indexEvals idx)
  , lookupAggreg: \_ -> zero
  , lookupSorted: \_ _ -> zero
  , lookupTable: \_ -> zero
  , lookupRuntimeTable: \_ -> zero
  , lookupRuntimeSelector: \_ -> zero
  , lookupKindIndex: \_ -> zero
  }

-- | Build Challenges using FFI to compute domain-dependent values
buildChallenges
  :: Pallas.BaseField -- alpha
  -> Pallas.BaseField -- beta
  -> Pallas.BaseField -- gamma
  -> Pallas.BaseField -- jointCombiner
  -> Pallas.BaseField -- zeta (evaluation point)
  -> Challenges Pallas.BaseField
buildChallenges alpha beta gamma jointCombiner zeta =
  { alpha
  , beta
  , gamma
  , jointCombiner
  , vanishesOnZeroKnowledgeAndPreviousRows:
      FFI.pallasVanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }
  , unnormalizedLagrangeBasis: \rowOffset ->
      FFI.pallasUnnormalizedLagrangeBasis
        { domainLog2
        -- Convert Boolean flag to actual zkRows count
        , zkRows: if rowOffset.zkRows then zkRows else 0
        , offset: rowOffset.offset
        , pt: zeta
        }
  }

-- | Build FFI input from arrays and challenges
buildFFIInput
  :: Array Pallas.BaseField -- 30 witness evals
  -> Array Pallas.BaseField -- 15 coefficient evals
  -> Array Pallas.BaseField -- 12 index evals
  -> Pallas.BaseField -- alpha
  -> Pallas.BaseField -- beta
  -> Pallas.BaseField -- gamma
  -> Pallas.BaseField -- jointCombiner
  -> Pallas.BaseField -- zeta
  -> { alpha :: Pallas.BaseField
     , beta :: Pallas.BaseField
     , gamma :: Pallas.BaseField
     , jointCombiner :: Pallas.BaseField
     , witnessEvals :: Array Pallas.BaseField
     , coefficientEvals :: Array Pallas.BaseField
     , poseidonIndex :: Array Pallas.BaseField
     , genericIndex :: Array Pallas.BaseField
     , varbasemulIndex :: Array Pallas.BaseField
     , endomulIndex :: Array Pallas.BaseField
     , endomulScalarIndex :: Array Pallas.BaseField
     , completeAddIndex :: Array Pallas.BaseField
     , vanishesOnZk :: Pallas.BaseField
     , zeta :: Pallas.BaseField
     , domainLog2 :: Int
     }
buildFFIInput witnessEvals coeffEvals indexEvals alpha beta gamma jointCombiner zeta =
  { alpha
  , beta
  , gamma
  , jointCombiner
  , witnessEvals
  , coefficientEvals: coeffEvals
  -- Extract index pairs from the flat array
  , poseidonIndex: Array.slice 0 2 indexEvals
  , genericIndex: Array.slice 2 4 indexEvals
  , varbasemulIndex: Array.slice 4 6 indexEvals
  , endomulIndex: Array.slice 6 8 indexEvals
  , endomulScalarIndex: Array.slice 8 10 indexEvals
  , completeAddIndex: Array.slice 10 12 indexEvals
  , vanishesOnZk: FFI.pallasVanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }
  , zeta
  , domainLog2
  }

-- | Generate array of n arbitrary field elements
genFieldArray :: Int -> Gen (Array Pallas.BaseField)
genFieldArray n = Array.fromFoldable <$> sequence (Array.replicate n arbitrary)

-- | Parse hex string to field element using BigInt
parseHex :: forall f. PrimeField f => String -> f
parseHex hex = fromMaybe zero (fromBigInt <$> BigInt.fromString hex)

spec :: Spec Unit
spec = describe "Linearization Interpreter" do
  it "PureScript interpreter matches Rust evaluator on arbitrary inputs" do
    liftEffect $ quickCheckGen do
      -- Generate arbitrary field elements
      witnessEvals <- genFieldArray 30 -- 15 columns * 2 (curr/next)
      coeffEvals <- genFieldArray 15 -- 15 coefficient columns
      indexEvals <- genFieldArray 12 -- 6 gate types * 2 (curr/next)
      alpha <- arbitrary
      beta <- arbitrary
      gamma <- arbitrary
      jointCombiner <- arbitrary
      zeta <- arbitrary

      -- Build PureScript structures
      let evalPoint = buildEvalPoint witnessEvals coeffEvals indexEvals
      let challenges = buildChallenges alpha beta gamma jointCombiner zeta
      let env = fieldEnv evalPoint challenges parseHex
      let
        psResult = (evaluate :: Array PolishToken -> Env Pallas.BaseField -> Pallas.BaseField)
          PallasTokens.constantTermTokens
          env

      -- Build FFI input for Rust
      let
        ffiInput = buildFFIInput witnessEvals coeffEvals indexEvals
          alpha
          beta
          gamma
          jointCombiner
          zeta

      -- Call Rust evaluator
      let rustResult = FFI.evaluatePallasLinearization ffiInput

      -- Both should produce the same result
      pure $ psResult === rustResult
