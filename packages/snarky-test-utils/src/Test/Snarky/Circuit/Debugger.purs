-- | Diagnostic utility for circuit debugging.
-- |
-- | Runs the same polymorphic circuit through `ProverT` with debug mode enabled
-- | for eager constraint checking. When a constraint fails, you get a precise
-- | `EvaluationError` at the exact point in circuit execution where it occurred.
-- |
-- | ```purescript
-- | -- When circuitTest' with Exact inputs fails, diagnose with:
-- | debugCircuitPure (Proxy @(KimchiConstraint f)) circuit failingInput
-- | -- → Left (FailedAssertion "R1CS constraint unsatisfied: ...")
-- | ```
module Test.Snarky.Circuit.Debugger
  ( debugCircuit
  , debugCircuitPure
  , debugCircuitInputs
  , debugCircuitPureInputs
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Foldable (traverse_)
import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (fst)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Snarky.Backend.Builder (class CompileCircuit, CircuitBuilderState)
import Snarky.Backend.Compile (Checker, makeSolver, makeSolver', runSolverT)
import Snarky.Backend.Prover (class SolveCircuit, emptyProverState)
import Snarky.Circuit.CVar (EvaluationError)
import Snarky.Circuit.DSL.Monad (class CheckedType, class CircuitM, Snarky)
import Snarky.Circuit.Types (class CircuitType)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (Result(..))
import Test.Snarky.Circuit.Utils (Expectation, PostCondition, runTestM)
import Test.Spec.Assertions (fail)
import Type.Proxy (Proxy(..))

-- | Run a circuit through `ProverT` with debug mode for eager constraint checking.
-- |
-- | Mirrors `makeSolver` but evaluates constraints immediately during witness
-- | computation. On failure, returns the exact `EvaluationError` at the point
-- | where the circuit went wrong.
debugCircuit
  :: forall f c m a b avar bvar
   . SolveCircuit f c
  => CheckedType f c avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => Monad m
  => Proxy c
  -> (forall t. CircuitM f c t m => avar -> Snarky c t m bvar)
  -> a
  -> m (Either EvaluationError b)
debugCircuit pc circuit inputs = do
  result <- runSolverT (makeSolver' (emptyProverState { debug = true }) pc circuit) inputs
  pure $ map fst result

-- | Pure variant of `debugCircuit` for circuits with `Identity` base monad.
debugCircuitPure
  :: forall f c a b avar bvar
   . SolveCircuit f c
  => CheckedType f c avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => Proxy c
  -> (forall t. CircuitM f c t Identity => avar -> Snarky c t Identity bvar)
  -> a
  -> Either EvaluationError b
debugCircuitPure pc circuit inputs = un Identity $ debugCircuit pc circuit inputs

-- | Run circuit tests with automatic debugger re-run on failure.
-- |
-- | Same interface as `circuitTestM'` with `Exact` inputs but takes the circuit function directly.
-- | On failure, re-runs the failing input through `ProverT` with debug mode
-- | and prints the labeled error for diagnosis.
debugCircuitInputs
  :: forall f c c' r m a b avar bvar
   . CompileCircuit f c c' r
  => SolveCircuit f c'
  => CheckedType f c' avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Show a
  => Monad m
  => (m ~> Effect)
  -> (forall t. CircuitM f c' t m => avar -> Snarky c' t m bvar)
  -> (a -> Expectation b)
  -> Checker f c
  -> PostCondition f c r
  -> CircuitBuilderState c r
  -> Array a
  -> Aff Unit
debugCircuitInputs nat circuit testFunction checker postCondition builtState inputs =
  let
    solver = makeSolver (Proxy @c') circuit
  in
    traverse_
      ( \a -> do
          result <- liftEffect $ nat $ runTestM { builtState, solver, checker, postCondition } testFunction a
          case result of
            Success -> pure unit
            Failed msg -> do
              debugResult <- liftEffect $ nat $ (debugCircuit (Proxy @c') circuit a :: m (Either EvaluationError b))
              case debugResult of
                Left e ->
                  fail $ "Failed on input " <> show a <> ": " <> msg <> "\n  Debugger: " <> show e
                Right _ ->
                  fail $ "Failed on input " <> show a <> ": " <> msg <> "\n  Debugger: no error (constraint satisfaction or post-condition issue)"
      )
      inputs

-- | Pure variant of `debugCircuitInputs`.
debugCircuitPureInputs
  :: forall f c c' r a b avar bvar
   . CompileCircuit f c c' r
  => SolveCircuit f c'
  => CheckedType f c' avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Show a
  => (forall t. CircuitM f c' t Identity => avar -> Snarky c' t Identity bvar)
  -> (a -> Expectation b)
  -> Checker f c
  -> PostCondition f c r
  -> CircuitBuilderState c r
  -> Array a
  -> Aff Unit
debugCircuitPureInputs circuit testFunction checker postCondition builtState inputs =
  debugCircuitInputs (pure <<< un Identity) circuit testFunction checker postCondition builtState inputs
