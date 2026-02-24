-- | Eager constraint-checking backend for circuit debugging.
-- |
-- | `CircuitDebuggerT` is like `ProverT` but evaluates constraints immediately
-- | against current assignments. When a constraint fails, you get a precise error
-- | at the exact point in circuit execution where it occurred, rather than a
-- | post-hoc "constraint unsatisfied" with no location.
-- |
-- | Usage: run the same polymorphic circuit through `CircuitDebuggerT` instead of
-- | the normal compile+prove pipeline when you need to diagnose failures.
module Snarky.Backend.Debugger
  ( CircuitDebuggerT
  , runCircuitDebuggerT
  , CircuitDebugger
  , runCircuitDebugger
  , throwDebuggerError
  , setAssignments
  , getAssignments
  , getState
  , putState
  , class DebugCircuit
  ) where

import Prelude

import Control.Monad.Except (Except, ExceptT(..), catchError, lift, runExcept, runExceptT, throwError)
import Control.Monad.State (StateT, get, gets, modify_, put, runStateT)
import Control.Monad.Trans.Class (class MonadTrans)
import Data.Array (foldl, zip)
import Data.Either (Either(..))
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (replicateA)
import Snarky.Backend.Prover (ProverState)
import Snarky.Circuit.CVar (CVar(Var), EvaluationError(..), Variable, incrementVariable)
import Snarky.Circuit.DSL.Monad (class CheckedType, class CircuitM, class ConstraintM, class MonadFresh, class WithLabel, AsProverT, Snarky(..), check, fresh, runAsProverT)
import Snarky.Circuit.Types (class CircuitType, fieldsToVar, sizeInFields, valueToFields)
import Snarky.Constraint.Basic (class BasicSystem, Basic(..))
import Snarky.Constraint.Basic as Basic
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

newtype CircuitDebuggerT f m a = CircuitDebuggerT (ExceptT EvaluationError (StateT (ProverState f) m) a)

derive newtype instance Functor m => Functor (CircuitDebuggerT f m)
derive newtype instance Monad m => Apply (CircuitDebuggerT f m)
derive newtype instance Monad m => Bind (CircuitDebuggerT f m)
derive newtype instance Monad m => Applicative (CircuitDebuggerT f m)
derive newtype instance Monad m => Monad (CircuitDebuggerT f m)

instance MonadTrans (CircuitDebuggerT f) where
  lift m = CircuitDebuggerT $ lift $ lift m

runCircuitDebuggerT
  :: forall f a m
   . Monad m
  => CircuitDebuggerT f m a
  -> ProverState f
  -> m (Tuple (Either EvaluationError a) (ProverState f))
runCircuitDebuggerT (CircuitDebuggerT m) s = runStateT (runExceptT m) s

type CircuitDebugger f = CircuitDebuggerT f Identity

runCircuitDebugger
  :: forall f a
   . CircuitDebugger f a
  -> ProverState f
  -> Tuple (Either EvaluationError a) (ProverState f)
runCircuitDebugger (CircuitDebuggerT m) s = un Identity $ runStateT (runExceptT m) s

-- | Eagerly evaluate Basic constraints against current assignments.
instance PrimeField f => ConstraintM (CircuitDebuggerT f) (Basic f) where
  addConstraint' c = CircuitDebuggerT do
    assignments <- gets _.assignments
    let
      lookup :: Variable -> Except EvaluationError f
      lookup v = case Map.lookup v assignments of
        Nothing -> throwError $ MissingVariable v
        Just val -> pure val
    case runExcept (Basic.eval lookup c) of
      Left e -> throwError e
      Right satisfied -> unless satisfied $
        throwError $ FailedAssertion $ constraintName c
    where
    constraintName = case _ of
      R1CS _ -> "R1CS constraint unsatisfied: left * right != output"
      Equal _ _ -> "Equality constraint unsatisfied"
      Square _ _ -> "Square constraint unsatisfied: a^2 != c"
      Boolean _ -> "Boolean constraint unsatisfied: value not in {0,1}"

class
  ( BasicSystem f c
  , ConstraintM (CircuitDebuggerT f) c
  ) <=
  DebugCircuit f c
  | c -> f

instance PrimeField f => DebugCircuit f (Basic f)

instance
  ( Monad m
  , PrimeField f
  , BasicSystem f c
  , ConstraintM (CircuitDebuggerT f) c
  ) =>
  CircuitM f c (CircuitDebuggerT f) m where
  exists
    :: forall a var
     . CircuitType f a var
    => CheckedType f c var
    => AsProverT f m a
    -> Snarky c (CircuitDebuggerT f) m var
  exists m = do
    res <- Snarky do
      assignments <- getAssignments
      let n = sizeInFields (Proxy @f) (Proxy @a)
      vars <- replicateA n fresh
      a <- CircuitDebuggerT $ ExceptT $ lift $ runAsProverT m assignments
      let
        aFieldElems = valueToFields a
      setAssignments (zip vars aFieldElems)
      pure $ fieldsToVar @f @a (map Var vars)
    check res
    pure res

instance Monad m => MonadFresh (CircuitDebuggerT f m) where
  fresh = CircuitDebuggerT do
    { nextVar } <- get
    modify_ _ { nextVar = incrementVariable nextVar }
    pure nextVar

throwDebuggerError
  :: forall f m a
   . Monad m
  => EvaluationError
  -> CircuitDebuggerT f m a
throwDebuggerError = CircuitDebuggerT <<< throwError

setAssignments
  :: forall f m
   . Monad m
  => Array (Tuple Variable f)
  -> CircuitDebuggerT f m Unit
setAssignments vs = CircuitDebuggerT $
  modify_ \s ->
    s { assignments = foldl (\acc (Tuple v f) -> Map.insert v f acc) s.assignments vs }

getAssignments
  :: forall f m
   . Monad m
  => CircuitDebuggerT f m (Map Variable f)
getAssignments = CircuitDebuggerT $ gets _.assignments

getState
  :: forall f m
   . Monad m
  => CircuitDebuggerT f m (ProverState f)
getState = CircuitDebuggerT $ get

putState
  :: forall f m
   . Monad m
  => ProverState f
  -> CircuitDebuggerT f m Unit
putState = CircuitDebuggerT <<< put

instance WithLabel (CircuitDebuggerT f) where
  withLabel s (CircuitDebuggerT action) = CircuitDebuggerT $
    catchError action \e -> throwError $ WithContext s e
