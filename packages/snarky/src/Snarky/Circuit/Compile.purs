module Snarky.Circuit.Compile
  ( Checker
  , Solver
  , SolverT
  , compile
  , makeSolver
  , makeAssertionSpec
  , makeChecker
  , makeCircuitSpec
  , runSolver
  , runSolverT
  ) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (Except, ExceptT, lift, runExcept, runExceptT)
import Control.Monad.State (gets, modify_)
import Data.Array (foldl, zip)
import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Foldable (foldM, for_)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (replicateA)
import Snarky.Circuit.Builder (CircuitBuilderState, emptyCircuitBuilderState, runCircuitBuilderT)
import Snarky.Circuit.CVar (CVar(..), EvaluationError(..))
import Snarky.Circuit.Constraint.Class (class R1CSSystem)
import Snarky.Circuit.DSL (class CircuitM, fresh, read, runAsProverT)
import Snarky.Circuit.DSL.Assert (assertEqual)
import Snarky.Circuit.Prover (ProverError(..), emptyProverState, runProverT)
import Snarky.Circuit.Types (class ConstrainedType, Variable, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (Result, withHelp)
import Type.Proxy (Proxy(..))

compile
  :: forall f c m a b avar bvar
   . PrimeField f
  => ConstrainedType f a c avar
  => ConstrainedType f b c bvar
  => Monad m
  => R1CSSystem (CVar f Variable) c
  => Proxy a
  -> Proxy b
  -> (forall t. CircuitM f c t m => avar -> t m bvar)
  -> m (CircuitBuilderState c)
compile _ _ circuit = do
  Tuple _ s <-
    flip runCircuitBuilderT emptyCircuitBuilderState do
      let
        n = sizeInFields @f (Proxy @a)
        m = sizeInFields @f (Proxy @b)
      vars <- replicateA (n + m) fresh
      let { before: avars, after: bvars } = Array.splitAt n vars
      modify_ \s ->
        s { publicInputs = vars }
      let avar = fieldsToVar @f @a (map Var avars)
      out <- circuit avar
      for_ (zip (varToFields @f @b out) (map Var bvars)) \(Tuple v1 v2) ->
        assertEqual v1 v2
      pure out
  pure s

makeSolver
  :: forall f c m a b avar bvar
   . PrimeField f
  => ConstrainedType f a c avar
  => ConstrainedType f b c bvar
  => Monad m
  => R1CSSystem (CVar f Variable) c
  => Proxy c
  -> (forall t. CircuitM f c t m => avar -> t m bvar)
  -> SolverT f m a b
makeSolver _ circuit = \inputs -> do
  eres <- lift $ flip runProverT emptyProverState do
    let n = sizeInFields @f (Proxy @a)
    let m = sizeInFields @f (Proxy @b)
    vars <- replicateA (n + m) fresh
    let { before: avars, after: bvars } = Array.splitAt n vars
    modify_ \s ->
      let
        fs = valueToFields inputs
      in
        s { assignments = foldl (\acc (Tuple v f) -> Map.insert v f acc) s.assignments (zip avars fs) }
    outVar <- circuit (fieldsToVar @f @a (map Var avars))
    eres <- gets _.assignments >>= runAsProverT (read outVar)
    either (throwError <<< EvalError)
      ( \output -> do
          modify_ \s ->
            let
              fs = valueToFields output
            in
              s { assignments = foldl (\acc (Tuple v f) -> Map.insert v f acc) s.assignments (zip bvars fs) }
          pure output
      )
      eres
  case eres of
    Tuple (Left e) _ -> throwError e
    Tuple (Right c) { assignments } -> pure $ Tuple c assignments

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
  :: forall f c a b avar bvar m
   . ConstrainedType f a c avar
  => ConstrainedType f b c bvar
  => Eq b
  => Monad m
  => { constraints :: Array c
     , solver :: SolverT f m a b
     , evalConstraint ::
         (Variable -> Except (EvaluationError Variable) f)
         -> c
         -> Except (EvaluationError Variable) Boolean
     , f :: a -> b
     }
  -> a
  -> m Result
makeCircuitSpec { constraints, solver, evalConstraint, f } inputs = do
  runSolverT solver inputs <#> case _ of
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
  :: forall f c a avar m
   . ConstrainedType f a c avar
  => Monad m
  => { constraints :: Array c
     , solver :: SolverT f m a Unit
     , evalConstraint ::
         (Variable -> Except (EvaluationError Variable) f)
         -> c
         -> Except (EvaluationError Variable) Boolean
     , isValid :: a -> Boolean
     }
  -> a
  -> m Result
makeAssertionSpec { constraints, solver, evalConstraint, isValid } inputs = do
  runSolverT solver inputs <#> case _ of
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