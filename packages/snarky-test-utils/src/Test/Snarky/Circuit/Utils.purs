module Test.Snarky.Circuit.Utils where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Either (Either(..))
import Data.Foldable (foldM, for_, intercalate, traverse_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Run (EFFECT, Run)
import Run as Run
import Snarky.Backend.Assignments as Assignments
import Snarky.Backend.Builder (class CompileCircuit, CircuitBuilderState, constraintsToArray)
import Snarky.Backend.Compile (Checker, Solver, SolverT, compile, makeSolver', runSolverT)
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, EvaluationError(..), Snarky, Variable)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (Result(..), withHelp)
import Test.QuickCheck.Gen (Gen, randomSampleOne)
import Test.Spec.Assertions (fail)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

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

type PostCondition f c aux =
  (Variable -> Either EvaluationError f)
  -> CircuitBuilderState c aux
  -> Effect (Either EvaluationError Boolean)

nullPostCondition :: forall f c aux. PostCondition f c aux
nullPostCondition _ _ = pure (Right true)

-- | Render an EvaluationError with variable birth context from the builder state.
decorateError :: (Variable -> Maybe (Array String)) -> EvaluationError -> String
decorateError metaLookup = go
  where
  go = case _ of
    WithContext ctx inner -> "[" <> ctx <> "] " <> go inner
    FailedAssertion msg -> "FailedAssertion: " <> msg
    MissingVariable v ->
      let
        context = maybe "" formatContext (metaLookup v)
      in
        "MissingVariable " <> show v <> context
    e -> show e
  formatContext labels
    | Array.null labels = ""
    | otherwise = " (" <> intercalate " > " labels <> ")"

isFailedAssertion :: EvaluationError -> Boolean
isFailedAssertion = case _ of
  FailedAssertion _ -> true
  WithContext _ inner -> isFailedAssertion inner
  _ -> false

-- | Backend-specific configuration for circuit tests.
-- | Define one value per constraint family to avoid repeating these three fields everywhere.
type TestConfig f c aux =
  { checker :: Checker f c
  , postCondition :: PostCondition f c aux
  }

-- | Core test runner: given a solver, checker, and inputs, produce a QuickCheck Result.
runTest
  :: forall f c c' aux a avar b
   . CircuitType f a avar
  => PrimeField f
  => Eq b
  => Show b
  => { builtState :: CircuitBuilderState c aux
     , solver :: Solver f c' a b
     , checker :: Checker f c
     , postCondition :: PostCondition f c aux
     }
  -> (a -> Expectation b)
  -> a
  -> Effect Result
runTest { builtState, solver, checker, postCondition } testFunction inputs = do
  solverResult <- Run.runBaseEffect $ runSolverT solver inputs
  checkResult builtState checker postCondition testFunction inputs solverResult

-- | Core test runner for effectful solvers.
runTestM
  :: forall f c c' aux r a avar b
   . CircuitType f a avar
  => PrimeField f
  => Eq b
  => Show b
  => { builtState :: CircuitBuilderState c aux
     , solver :: SolverT f c' r a b
     , checker :: Checker f c
     , postCondition :: PostCondition f c aux
     }
  -> (a -> Expectation b)
  -> a
  -> Run (EFFECT + r) Result
runTestM { builtState, solver, checker, postCondition } testFunction inputs =
  runSolverT solver inputs >>= \res ->
    Run.liftEffect (checkResult builtState checker postCondition testFunction inputs res)

-- | Check a solver result against the circuit constraints and test function.
checkResult
  :: forall f c aux a b
   . PrimeField f
  => Eq b
  => Show b
  => CircuitBuilderState c aux
  -> Checker f c
  -> PostCondition f c aux
  -> (a -> Expectation b)
  -> a
  -> Either EvaluationError (Tuple b (Map Variable f))
  -> Effect Result
checkResult builtState checker postCondition testFunction inputs result = do
  metaLookup <- Assignments.toLookup builtState.varMetadata
  case result of
    Left e -> pure
      case testFunction inputs of
        ProverError f -> withHelp (f e) ("Prover exited with error " <> decorateError metaLookup e)
        Unsatisfied | isFailedAssertion e -> Success
        _ -> withHelp false ("Encountered unexpected error when proving circuit: " <> decorateError metaLookup e)
    Right (Tuple b assignments) -> do
      let
        lookup :: Variable -> Either EvaluationError f
        lookup v = case Map.lookup v assignments of
          Nothing -> Left $ MissingVariable v
          Just res -> pure res

        checks = foldM (\acc c -> conj acc <$> checker lookup c.constraint) true
      postConditionRes <- postCondition lookup builtState
      let
        satisfiedRes = do
          constraintsResult <- checks (constraintsToArray builtState.constraints)
          postConditionResult <- postConditionRes
          pure { constraintsResult, postConditionResult }
      pure
        case satisfiedRes of
          Left e -> withHelp false ("Encountered unexpected error when checking circuit: " <> decorateError metaLookup e)
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
  :: forall @f c c' aux a b avar bvar
   . CompileCircuit f c c' aux
  => SolveCircuit f c'
  => CheckedType f c' avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => TestConfig f c aux
  -> NonEmptyArray { testFunction :: a -> Expectation b, input :: TestInput a }
  -> (avar -> Snarky f c' () bvar)
  -> Aff { builtState :: CircuitBuilderState c aux, solver :: Solver f c' a b }
circuitTest' { checker, postCondition } scenarios circuit = do
  builtState <- liftEffect $ Run.runBaseEffect $ compile (Proxy @a) (Proxy @b) (Proxy @c') circuit
  let solver = makeSolver' { debug: true } (Proxy @c') circuit
  forWithIndex_ scenarios \idx { testFunction, input } ->
    runScenario idx (runTest { builtState, solver, checker, postCondition } testFunction) input
  pure { builtState, solver }

-- | Like `circuitTest'` but for circuits with an effectful base monad.
-- | Takes a natural transformation `m ~> Effect` to run the monad.
circuitTestM'
  :: forall @f c c' aux a b avar bvar r
   . CompileCircuit f c c' aux
  => SolveCircuit f c'
  => CheckedType f c' avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => (Run (EFFECT + r) ~> Effect)
  -> TestConfig f c aux
  -> NonEmptyArray { testFunction :: a -> Expectation b, input :: TestInput a }
  -> (avar -> Snarky f c' r bvar)
  -> Aff { builtState :: CircuitBuilderState c aux, solver :: SolverT f c' r a b }
circuitTestM' nat { checker, postCondition } scenarios circuit = do
  builtState <- liftEffect $ nat $ compile (Proxy @a) (Proxy @b) (Proxy @c') circuit
  let solver = makeSolver' { debug: true } (Proxy @c') circuit
  forWithIndex_ scenarios \idx { testFunction, input } ->
    runScenarioM idx nat (runTestM { builtState, solver, checker, postCondition } testFunction) input
  pure { builtState, solver }

-- | Run a single test scenario with the given test runner.
runScenario :: forall a. Int -> (a -> Effect Result) -> TestInput a -> Aff Unit
runScenario idx run = case _ of
  QuickCheck n gen ->
    for_ (Array.range 1 n) \_ -> do
      a <- liftEffect (randomSampleOne gen)
      result <- liftEffect (run a)
      case result of
        Success -> pure unit
        Failed msg -> fail $ "Scenario #" <> show idx <> " failed: " <> msg
  Exact inputs ->
    traverse_
      ( \a -> do
          result <- liftEffect (run a)
          case result of
            Success -> pure unit
            Failed msg -> fail $ "Scenario #" <> show idx <> " failed: " <> msg
      )
      inputs

-- | Run a single test scenario with an effectful test runner.
runScenarioM :: forall a r. Int -> (Run (EFFECT + r) ~> Effect) -> (a -> Run (EFFECT + r) Result) -> TestInput a -> Aff Unit
runScenarioM idx nat run = case _ of
  QuickCheck n gen ->
    for_ (Array.range 1 n) \_ -> do
      a <- liftEffect (randomSampleOne gen)
      result <- liftEffect (nat (run a))
      case result of
        Success -> pure unit
        Failed msg -> fail $ "Scenario #" <> show idx <> " failed: " <> msg
  Exact inputs ->
    traverse_
      ( \a -> do
          result <- liftEffect $ nat $ run a
          case result of
            Success -> pure unit
            Failed msg -> fail $ "Scenario #" <> show idx <> " failed: " <> msg
      )
      inputs
