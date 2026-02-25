module Test.Snarky.Circuit.Utils where

import Prelude

import Control.Monad.Except (Except, runExcept, throwError)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Either (Either(..))
import Data.Foldable (foldM, intercalate, traverse_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Unsafe (unsafePerformEffect)
import Snarky.Backend.Builder (class CompileCircuit, CircuitBuilderState)
import Snarky.Backend.Compile (Checker, Solver, SolverT, compile, compilePure, makeSolver, runSolverT)
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Circuit.DSL (class CheckedType, class CircuitM, class CircuitType, EvaluationError(..), Snarky, Variable)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (Result(..), quickCheck', withHelp)
import Test.QuickCheck.Gen (Gen)
import Test.Spec.Assertions (fail)
import Type.Proxy (Proxy(..))

-- | How to provide test inputs: either via a QuickCheck generator or as exact values.
data TestInput a
  = QuickCheck Int (Gen a)
  | Exact (NonEmptyArray a)

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

-- | Render an EvaluationError with variable birth context from the builder state.
decorateError :: forall c r. CircuitBuilderState c r -> EvaluationError -> String
decorateError builtState = go
  where
  go = case _ of
    WithContext ctx inner -> "[" <> ctx <> "] " <> go inner
    FailedAssertion msg -> "FailedAssertion: " <> msg
    MissingVariable v ->
      let
        context = maybe "" formatContext (Map.lookup v builtState.varMetadata)
      in
        "MissingVariable " <> show v <> context
    e -> show e
  formatContext labels
    | Array.null labels = ""
    | otherwise = " (" <> intercalate " > " labels <> ")"

-- | Backend-specific configuration for circuit tests.
-- | Define one value per constraint family to avoid repeating these three fields everywhere.
type TestConfig f c r =
  { checker :: Checker f c
  , postCondition :: PostCondition f c r
  , initState :: CircuitBuilderState c r
  }

-- | Core test runner: given a solver, checker, and inputs, produce a QuickCheck Result.
runTest
  :: forall f c c' r a avar b
   . CircuitType f a avar
  => PrimeField f
  => Eq b
  => Show b
  => { builtState :: CircuitBuilderState c r
     , solver :: Solver f c' a b
     , checker :: Checker f c
     , postCondition :: PostCondition f c r
     }
  -> (a -> Expectation b)
  -> a
  -> Result
runTest { builtState, solver, checker, postCondition } testFunction inputs =
  let
    solverResult = un Identity $ runSolverT solver inputs
  in
    checkResult builtState checker postCondition testFunction inputs solverResult

-- | Core test runner for effectful solvers.
runTestM
  :: forall f c c' r m a avar b
   . CircuitType f a avar
  => Monad m
  => PrimeField f
  => Eq b
  => Show b
  => { builtState :: CircuitBuilderState c r
     , solver :: SolverT f c' m a b
     , checker :: Checker f c
     , postCondition :: PostCondition f c r
     }
  -> (a -> Expectation b)
  -> a
  -> m Result
runTestM { builtState, solver, checker, postCondition } testFunction inputs =
  runSolverT solver inputs <#>
    checkResult builtState checker postCondition testFunction inputs

-- | Check a solver result against the circuit constraints and test function.
checkResult
  :: forall f c r a b
   . PrimeField f
  => Eq b
  => Show b
  => CircuitBuilderState c r
  -> Checker f c
  -> PostCondition f c r
  -> (a -> Expectation b)
  -> a
  -> Either EvaluationError (Tuple b (Map Variable f))
  -> Result
checkResult builtState checker postCondition testFunction inputs = case _ of
  Left e ->
    case testFunction inputs of
      ProverError f -> withHelp (f e) ("Prover exited with error " <> decorateError builtState e)
      _ -> withHelp false ("Encountered unexpected error when proving circuit: " <> decorateError builtState e)
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
        Left e -> withHelp false ("Encountered unexpected error when checking circuit: " <> decorateError builtState e)
        Right s@{ constraintsResult, postConditionResult } -> case testFunction inputs of
          Satisfied expected | constraintsResult && postConditionResult ->
            withHelp (expected == b) ("Circuit disagrees with test function, circuit got " <> show b <> " expected " <> show expected <> " from test function")
          Unsatisfied | not (constraintsResult && postConditionResult) -> Success
          res -> withHelp false ("Circuit satisfiability: " <> show s <> ", checker exited with " <> show res)

-- | Compile a circuit and run tests against it.
-- |
-- | Takes a `NonEmptyArray` of `{ testFunction, input }` pairs so you can compile
-- | once and test multiple scenarios (e.g. satisfiable and unsatisfiable inputs).
-- | Each scenario provides inputs via `QuickCheck n gen` or `Exact values`.
circuitTest'
  :: forall @f c c' r a b avar bvar
   . CompileCircuit f c c' r
  => SolveCircuit f c'
  => CheckedType f c' avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => TestConfig f c r
  -> NonEmptyArray { testFunction :: a -> Expectation b, input :: TestInput a }
  -> (forall t. CircuitM f c' t Identity => avar -> Snarky c' t Identity bvar)
  -> Aff { builtState :: CircuitBuilderState c r, solver :: Solver f c' a b }
circuitTest' { checker, postCondition, initState } scenarios circuit = do
  let
    builtState = compilePure (Proxy @a) (Proxy @b) (Proxy @c') circuit initState
    solver = makeSolver (Proxy @c') circuit
  forWithIndex_ scenarios \idx { testFunction, input } ->
    runScenario idx (runTest { builtState, solver, checker, postCondition } testFunction) input
  pure { builtState, solver }

-- | Like `circuitTest'` but for circuits with an effectful base monad.
-- | Takes a natural transformation `m ~> Effect` to run the monad.
circuitTestM'
  :: forall @f c c' r a b avar bvar m
   . CompileCircuit f c c' r
  => SolveCircuit f c'
  => CheckedType f c' avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Monad m
  => (m ~> Effect)
  -> TestConfig f c r
  -> NonEmptyArray { testFunction :: a -> Expectation b, input :: TestInput a }
  -> (forall t. CircuitM f c' t m => avar -> Snarky c' t m bvar)
  -> Aff { builtState :: CircuitBuilderState c r, solver :: SolverT f c' m a b }
circuitTestM' nat { checker, postCondition, initState } scenarios circuit = do
  builtState <- liftEffect $ nat $ compile (Proxy @a) (Proxy @b) (Proxy @c') circuit initState
  let solver = makeSolver (Proxy @c') circuit
  forWithIndex_ scenarios \idx { testFunction, input } ->
    runScenarioM idx nat (runTestM { builtState, solver, checker, postCondition } testFunction) input
  pure { builtState, solver }

-- | Run a single test scenario with the given test runner.
runScenario :: forall a. Int -> (a -> Result) -> TestInput a -> Aff Unit
runScenario idx run = case _ of
  QuickCheck n gen ->
    liftEffect $ quickCheck' n $ gen <#> run
  Exact inputs ->
    traverse_
      ( \a -> case run a of
          Success -> pure unit
          Failed msg -> fail $ "Scenario #" <> show idx <> " failed: " <> msg
      )
      inputs

-- | Run a single test scenario with an effectful test runner.
runScenarioM :: forall a m. Monad m => Int -> (m ~> Effect) -> (a -> m Result) -> TestInput a -> Aff Unit
runScenarioM idx nat run = case _ of
  QuickCheck n gen ->
    liftEffect $ quickCheck' n $ gen <#> \a ->
      unsafePerformEffect $ nat $ run a
  Exact inputs ->
    traverse_
      ( \a -> do
          result <- liftEffect $ nat $ run a
          case result of
            Success -> pure unit
            Failed msg -> fail $ "Scenario #" <> show idx <> " failed: " <> msg
      )
      inputs
