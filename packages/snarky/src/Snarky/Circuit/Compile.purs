module Snarky.Circuit.Compile
  ( compile
  , compile_
  , SolverT
  , runSolverT
  , Solver
  , runSolver
  , Checker
  , makeChecker
  , makeCircuitSpec
  , makeAssertionSpec
  ) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (Except, ExceptT(..), lift, runExcept, runExceptT, withExceptT)
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Snarky.Circuit.Builder (emptyCircuitBuilderState, runCircuitBuilderT)
import Snarky.Circuit.CVar (CVar, EvaluationError(..))
import Snarky.Circuit.Constraint.Class (class R1CSSystem)
import Snarky.Circuit.DSL (class CircuitM, read, runAsProverT)
import Snarky.Circuit.Prover (ProverError(..), assignPublicInputs, emptyProverState, runProverT)
import Snarky.Circuit.Types (class ConstrainedType, Variable)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (Result, withHelp)
import Test.QuickCheck.Gen (Gen)

compile
  :: forall f c a b n avar bvar
   . PrimeField f
  => R1CSSystem (CVar f Variable) c
  => ConstrainedType f a c avar
  => ConstrainedType f b c bvar
  => Monad n
  => (forall m. CircuitM f c m n => m bvar)
  -> n
       { constraints :: Array c
       , solver :: SolverT f n a b
       }
compile circuit = do
  Tuple _ { constraints, publicInputs } <-
    runCircuitBuilderT circuit emptyCircuitBuilderState
  pure
    { constraints
    , solver: mkSolverT publicInputs
    }
  where

  mkSolverT publicInputs = \inputs -> do
    Tuple resultVar (assignments :: Map Variable f) <- do
      let proverState = emptyProverState { publicInputs = publicInputs }
      res <- lift $ runProverT (assignPublicInputs inputs *> circuit) proverState
      case res of
        Tuple (Left e) _ -> throwError e
        Tuple (Right c) { assignments } -> pure $ Tuple c assignments
    res <- withExceptT EvalError $ ExceptT $ runAsProverT (read resultVar) assignments
    pure $ Tuple res assignments

compile_
  :: forall f c a n avar
   . PrimeField f
  => R1CSSystem (CVar f Variable) c
  => ConstrainedType f a c avar
  => Monad n
  => (forall m. CircuitM f c m n => m Unit)
  -> n
       { constraints :: Array c
       , solver :: SolverT f n a Unit
       }
compile_ circuit = do
  Tuple _ { constraints, publicInputs } <-
    runCircuitBuilderT circuit emptyCircuitBuilderState
  pure
    { constraints
    , solver: mkSolverT publicInputs
    }
  where

  mkSolverT publicInputs = \inputs -> do
    Tuple _ (assignments :: Map Variable f) <- do
      let proverState = emptyProverState { publicInputs = publicInputs }
      res <- lift $ runProverT (assignPublicInputs inputs *> circuit) proverState
      case res of
        Tuple (Left e) _ -> throwError e
        Tuple (Right c) { assignments } -> pure $ Tuple c assignments
    pure $ Tuple unit assignments

type SolverResult f a =
  { result :: a
  , assignments :: Map Variable f
  }

type SolverT f m a b = a -> ExceptT ProverError m (Tuple b (Map Variable f))

runSolverT :: forall f m a b. SolverT f m a b -> a -> m (Either ProverError (Tuple b (Map Variable f)))
runSolverT f a = runExceptT (f a)

type Solver f a b = SolverT f Identity a b

runSolver :: forall f a b. Solver f a b -> a -> Either ProverError (Tuple b (Map Variable f))
runSolver c a = un Identity $ runSolverT c a

type Checker c = Array c -> Except (EvaluationError Variable) Boolean

makeChecker :: forall c. (c -> Except (EvaluationError Variable) Boolean) -> Checker c
makeChecker f = foldM (\acc c -> f c <#> \a -> acc && a) true

makeCircuitSpec
  :: forall f c a b avar bvar
   . ConstrainedType f a c avar
  => ConstrainedType f b c bvar
  => Eq b
  => Gen a
  -> { constraints :: Array c
     , solver :: Solver f a b
     , evalConstraint ::
         (Variable -> Except (EvaluationError Variable) f)
         -> c
         -> Except (EvaluationError Variable) Boolean
     , f :: a -> b
     }
  -> Gen Result
makeCircuitSpec inputsGen { constraints, solver, evalConstraint, f } = inputsGen <#> \inputs ->
  case runSolver solver inputs of
    Left e -> withHelp false ("Prover error when solving ciruit: " <> show e)
    Right (Tuple b assignments) ->
      let
        checker =
          let
            lookup v = case Map.lookup v assignments of
              Nothing -> throwError $ MissingVariable v
              Just res -> pure res
          in
            makeChecker (evalConstraint lookup)
      in
        case runExcept $ checker constraints of
          Left e -> withHelp false ("Error during constraint checking: " <> show e)
          Right isSatisfied ->
            withHelp (isSatisfied && (f inputs == b)) "Circuit is satisfied and agrees with spec"

makeAssertionSpec
  :: forall f c a avar
   . ConstrainedType f a c avar
  => Gen a
  -> { constraints :: Array c
     , solver :: Solver f a Unit
     , evalConstraint ::
         (Variable -> Except (EvaluationError Variable) f)
         -> c
         -> Except (EvaluationError Variable) Boolean
     , isValid :: a -> Boolean
     }
  -> Gen Result
makeAssertionSpec inputsGen { constraints, solver, evalConstraint, isValid } = inputsGen <#> \inputs ->
  case runSolver solver inputs of
    Left e -> withHelp false ("Prover error when solving ciruit: " <> show e)
    Right (Tuple _ assignments) ->
      let
        checker =
          let
            lookup v = case Map.lookup v assignments of
              Nothing -> throwError $ MissingVariable v
              Just res -> pure res
          in
            makeChecker (evalConstraint lookup)
      in
        case runExcept $ checker constraints of
          Left e -> withHelp false ("Error during constraint checking: " <> show e)
          Right isSatisfied ->
            withHelp (isSatisfied == isValid inputs) "Circuit is satisfied and agrees with spec"