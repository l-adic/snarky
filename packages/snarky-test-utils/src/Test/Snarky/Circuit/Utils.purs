module Test.Snarky.Circuit.Utils where

import Prelude

import Control.Monad.Except (Except, runExcept, throwError)
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Identity (Identity(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Unsafe (unsafePerformEffect)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Checker, SolverT, runSolverT)
import Snarky.Circuit.CVar (EvaluationError(..), Variable)
import Snarky.Circuit.Types (class CircuitType)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, Result(..), arbitrary, withHelp, quickCheck)
import Test.QuickCheck.Gen (Gen)

data Expectation a
  = Satisfied a
  | Unsatisfied
  | ProverError (EvaluationError -> Boolean)

instance Show a => Show (Expectation a) where
  show = case _ of
    Unsatisfied -> "Unsatisfiable"
    Satisfied a -> "Satisfied " <> show a
    ProverError _ -> "[ProverError]"

derive instance Functor Expectation

satisfied :: forall a b. (a -> b) -> a -> Expectation b
satisfied f a = Satisfied (f a)

satisfied_ :: forall a. a -> Expectation Unit
satisfied_ _ = Satisfied unit

unsatisfied :: forall a b. a -> Expectation b
unsatisfied _ = Unsatisfied

expectDivideByZero :: forall a b. a -> Expectation b
expectDivideByZero _ = ProverError \e -> case e of
  DivisionByZero _ -> true
  _ -> false

type PostCondition f c r =
  (Variable -> Except EvaluationError f)
  -> CircuitBuilderState c r
  -> Except EvaluationError Boolean

nullPostCondition :: forall f c r. PostCondition f c r
nullPostCondition _ _ = pure true

type CircuitSpec :: forall k. Type -> Type -> Type -> (Type -> Type) -> Type -> k -> Type -> Type
type CircuitSpec f c r m a avar b =
  { builtState :: CircuitBuilderState c r
  , solver :: SolverT f c m a b
  , checker :: Checker f c
  , testFunction :: a -> Expectation b
  , postCondition :: PostCondition f c r
  }

runCircuitSpec
  :: forall f c r m a avar b
   . CircuitType f a avar
  => Monad m
  => Eq b
  => Show b
  => PrimeField f
  => CircuitSpec f c r m a avar b
  -> a
  -> m Result
runCircuitSpec { builtState, solver, checker, testFunction, postCondition } inputs = do
  runSolverT solver inputs <#> case _ of
    Left e ->
      case testFunction inputs of
        ProverError f -> withHelp (f e) ("Prover exited with error " <> show e)
        _ -> withHelp false ("Encountered unexpected  error when proving circuit: " <> show e)
    Right (Tuple b assignments) ->
      let
        lookup :: Variable -> Except EvaluationError f
        lookup v = case Map.lookup v assignments of
          Nothing -> throwError $ MissingVariable v
          Just res -> pure res

        checks = foldM (\acc c -> conj acc <$> checker lookup c) true
        satisfiedRes = do
          constraintsResult <- checks builtState.constraints
          postConditionResult <- postCondition lookup builtState
          pure { constraintsResult, postConditionResult }
      in
        case runExcept satisfiedRes of
          Left e -> withHelp false ("Encountered unexpected error when checking circuit: " <> show e)
          Right s@{ constraintsResult, postConditionResult } -> case testFunction inputs of
            Satisfied expected | constraintsResult && postConditionResult ->
              withHelp (expected == b) ("Circuit disagrees with test function, circuit got " <> show b <> " expected " <> show expected <> " from test function")
            Unsatisfied | not (constraintsResult && postConditionResult) -> Success
            res -> withHelp false ("Circuit satisfiability: " <> show s <> ", checker exited with " <> show res)

circuitSpecPure
  :: forall a avar b bvar f c r
   . CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Arbitrary a
  => CircuitSpec f c r Identity a avar b
  -> Aff Unit
circuitSpecPure arg =
  circuitSpecPure' arg arbitrary

circuitSpecPure'
  :: forall a b avar bvar f c r
   . CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => CircuitSpec f c r Identity a avar b
  -> Gen a
  -> Aff Unit
circuitSpecPure' arg g = liftEffect
  let
    spc = un Identity <<<
      runCircuitSpec arg
  in
    quickCheck $
      g <#> spc

-- Warning: circuitSpec and circuitSpec' use unsafePerformEffect
-- to run their effects layer, use with caution
circuitSpec
  :: forall a avar b bvar f m c r
   . CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Monad m
  => Arbitrary a
  => (m ~> Effect)
  -> CircuitSpec f c r m a avar b
  -> Aff Unit
circuitSpec nat spc =
  circuitSpec' nat spc arbitrary

circuitSpec'
  :: forall a avar b bvar f m c r
   . CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Monad m
  => (m ~> Effect)
  -> CircuitSpec f c r m a avar b
  -> Gen a
  -> Aff Unit
circuitSpec' nat spec g =
  let
    spc = runCircuitSpec spec
  in
    liftEffect (quickCheck $ g <#> \a -> unsafePerformEffect $ nat $ spc a)