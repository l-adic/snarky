module Snarky.Circuit.Compile
  ( Checker
  , Solver
  , SolverT
  , compilePure
  , compile
  , makeSolver
  , makeChecker
  , runSolver
  , runSolverT
  ) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (Except, ExceptT, lift, runExceptT)
import Data.Array (zip)
import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Foldable (foldM, for_)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (replicateA)
import Snarky.Circuit.Builder (CircuitBuilderState, emptyCircuitBuilderState, runCircuitBuilderT, setPublicInputVars)
import Snarky.Circuit.CVar (CVar(..), EvaluationError)
import Snarky.Circuit.Constraint.Class (class R1CSSystem)
import Snarky.Circuit.DSL.Assert (assertEqual)
import Snarky.Circuit.DSL.Monad (class CircuitM, fresh, read, runAsProverT)
import Snarky.Circuit.Prover (emptyProverState, getAssignments, runProverT, setAssignments, throwProverError)
import Snarky.Circuit.Types (class ConstrainedType, Variable, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

compilePure
  :: forall f c a b avar bvar
   . PrimeField f
  => ConstrainedType f a c avar
  => ConstrainedType f b c bvar
  => R1CSSystem (CVar f Variable) c
  => Proxy a
  -> Proxy b
  -> (forall t. CircuitM f c t Identity => avar -> t Identity bvar)
  -> CircuitBuilderState c
compilePure pa pb circuit = un Identity $ compile pa pb circuit

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
      setPublicInputVars vars
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
    setAssignments $ zip avars (valueToFields inputs)
    outVar <- circuit (fieldsToVar @f @a (map Var avars))
    eres <- getAssignments >>= runAsProverT (read outVar)
    either throwProverError
      ( \output -> do
          setAssignments $ (zip bvars (valueToFields output))
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

type SolverT f m a b = a -> ExceptT (EvaluationError f Variable) m (Tuple b (Map Variable f))

runSolverT :: forall f m a b. SolverT f m a b -> a -> m (Either (EvaluationError f Variable) (Tuple b (Map Variable f)))
runSolverT f a = runExceptT (f a)

type Solver f a b = SolverT f Identity a b

runSolver :: forall f a b. Solver f a b -> a -> Either (EvaluationError f Variable) (Tuple b (Map Variable f))
runSolver c a = un Identity $ runSolverT c a

type Checker f c = Array c -> Except ((EvaluationError f Variable)) Boolean

makeChecker :: forall f c. (c -> Except (EvaluationError f Variable) Boolean) -> Checker f c
makeChecker f = foldM (\acc c -> f c <#> \a -> acc && a) true
