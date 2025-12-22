module Snarky.Backend.Compile
  ( Checker
  , Solver
  , SolverT
  , compilePure
  , compile
  , makeSolver
  , runSolver
  , runSolverT
  ) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (Except, ExceptT, lift, runExceptT)
import Data.Array (zip)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (replicateA)
import Snarky.Backend.Builder (CircuitBuilderState, CircuitBuilderT, runCircuitBuilderT, setPublicInputVars)
import Snarky.Backend.Prover (ProverT, emptyProverState, getAssignments, runProverT, setAssignments, throwProverError)
import Snarky.Circuit.CVar (CVar(..), EvaluationError, Variable)
import Snarky.Circuit.DSL.Assert (assertEqual_)
import Snarky.Circuit.DSL.Monad (class CircuitM, class ConstraintM, Snarky, fresh, read, runAsProverT, runSnarky)
import Snarky.Circuit.Types (class CircuitType, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

compilePure
  :: forall f c c' a b avar bvar r
   . PrimeField f
  => CircuitType f a avar
  => CircuitType f b bvar
  => BasicSystem f c'
  => ConstraintM (CircuitBuilderT c r) c'
  => Proxy a
  -> Proxy b
  -> Proxy c'
  -> (forall t. CircuitM f c' t Identity => avar -> Snarky c' t Identity bvar)
  -> CircuitBuilderState c r
  -> CircuitBuilderState c r
compilePure pa pb pc circuit cbs = un Identity $ compile pa pb pc circuit cbs

compile
  :: forall f c c' m a b avar bvar r
   . PrimeField f
  => CircuitType f a avar
  => CircuitType f b bvar
  => Monad m
  => BasicSystem f c'
  => ConstraintM (CircuitBuilderT c r) c'
  => Proxy a
  -> Proxy b
  -> Proxy c'
  -> (forall t. CircuitM f c' t m => avar -> Snarky c' t m bvar)
  -> CircuitBuilderState c r
  -> m (CircuitBuilderState c r)
compile _ _ _ circuit cbs = do
  Tuple _ s <-
    flip runCircuitBuilderT cbs do
      let
        n = sizeInFields (Proxy @f) (Proxy @a)
        m = sizeInFields (Proxy @f) (Proxy @b)
      vars <- replicateA (n + m) fresh
      let { before: avars, after: bvars } = Array.splitAt n vars
      setPublicInputVars vars
      let avar = fieldsToVar @f @a (map Var avars)
      out <- runSnarky $ do
        out <- circuit avar
        for_ (zip (varToFields @f @b out) (map Var bvars)) \(Tuple v1 v2) ->
          assertEqual_ v1 v2
      pure out
  pure s

makeSolver
  :: forall f a b c m avar bvar
   . PrimeField f
  => CircuitType f a avar
  => CircuitType f b bvar
  => Monad m
  => BasicSystem f c
  => ConstraintM (ProverT f) c
  => Proxy c
  -> (forall t. CircuitM f c t m => avar -> Snarky c t m bvar)
  -> SolverT f c m a b
makeSolver _ circuit = \inputs -> do
  eres <- lift $ flip runProverT emptyProverState do
    let n = sizeInFields (Proxy @f) (Proxy @a)
    let m = sizeInFields (Proxy @f) (Proxy @b)
    vars <- replicateA (n + m) fresh
    let { before: avars, after: bvars } = Array.splitAt n vars
    setAssignments $ zip avars (valueToFields inputs)
    outVar <- runSnarky $ do
      result <- circuit (fieldsToVar @f @a (map Var avars))
      pure result
    eres <- getAssignments >>= runAsProverT (read outVar)
    case eres of
      Left e -> throwProverError e
      Right output -> do
        setAssignments $ zip bvars (valueToFields output)
        runSnarky $
          for_ (zip (varToFields @f @b outVar) (map Var bvars)) \(Tuple v1 v2) -> do
            assertEqual_ v1 v2 :: Snarky c (ProverT f) m Unit
        pure output
  case eres of
    Tuple (Left e) _ -> throwError e
    Tuple (Right c) { assignments } -> pure $ Tuple c assignments

type SolverT :: Type -> Type -> (Type -> Type) -> Type -> Type -> Type
type SolverT f c m a b = a -> ExceptT (EvaluationError f) m (Tuple b (Map Variable f))

runSolverT :: forall f c m a b. SolverT f c m a b -> a -> m (Either (EvaluationError f) (Tuple b (Map Variable f)))
runSolverT f a = runExceptT (f a)

type Solver f c a b = SolverT f c Identity a b

runSolver :: forall f c a b. Solver f c a b -> a -> Either (EvaluationError f) (Tuple b (Map Variable f))
runSolver c a = un Identity $ runSolverT c a

type Checker f c =
  (Variable -> Except (EvaluationError f) f)
  -> c
  -> Except (EvaluationError f) Boolean