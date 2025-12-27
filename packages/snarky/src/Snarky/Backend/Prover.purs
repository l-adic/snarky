module Snarky.Backend.Prover
  ( ProverT
  , runProverT
  , ProverState
  , emptyProverState
  , Prover
  , runProver
  , throwProverError
  , setAssignments
  , getAssignments
  , getState
  , putState
  ) where

import Prelude

import Control.Monad.Except (ExceptT(..), lift, runExceptT, throwError)
import Control.Monad.State (StateT, get, gets, modify_, put, runStateT)
import Control.Monad.Trans.Class (class MonadTrans)
import Data.Array (foldl, zip)
import Data.Either (Either)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (replicateA)
import Snarky.Circuit.CVar (CVar(Var), EvaluationError, Variable, incrementVariable, v0)
import Snarky.Circuit.DSL.Monad (class CircuitM, class MonadFresh, class ConstraintM, AsProverT, Snarky(..), fresh, runAsProverT)
import Snarky.Circuit.Types (class CircuitType, fieldsToVar, sizeInFields, valueToFields)
import Snarky.Constraint.Basic (class BasicSystem, Basic)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

type ProverState f =
  { nextVar :: Variable
  , assignments :: Map Variable f
  }

emptyProverState :: forall f. ProverState f
emptyProverState =
  { nextVar: v0
  , assignments: Map.empty
  }

newtype ProverT f m a = ProverT (ExceptT EvaluationError (StateT (ProverState f) m) a)

derive newtype instance Functor m => Functor (ProverT f m)
derive newtype instance Monad m => Apply (ProverT f m)
derive newtype instance Monad m => Bind (ProverT f m)
derive newtype instance Monad m => Applicative (ProverT f m)
derive newtype instance Monad m => Monad (ProverT f m)

-- TODO: why is this not newtype derivable
instance MonadTrans (ProverT f) where
  lift m = ProverT $ lift $ lift m

runProverT :: forall f a m. Monad m => ProverT f m a -> ProverState f -> m (Tuple (Either EvaluationError a) (ProverState f))
runProverT (ProverT m) s = runStateT (runExceptT m) s

type Prover f = ProverT f Identity

runProver :: forall f a. Prover f a -> ProverState f -> Tuple (Either EvaluationError a) (ProverState f)
runProver (ProverT m) s = un Identity $ runStateT (runExceptT m) s

instance ConstraintM (ProverT f) (Basic f) where
  addConstraint' _ = pure unit

instance (Monad m, PrimeField f, BasicSystem f c, ConstraintM (ProverT f) c) => CircuitM f c (ProverT f) m where
  exists :: forall a var. CircuitType f a var => AsProverT f m a -> Snarky c (ProverT f) m var
  exists m = Snarky do
    assignments <- getAssignments
    let n = sizeInFields (Proxy @f) (Proxy @a)
    vars <- replicateA n fresh
    a <- ProverT $ ExceptT $ lift $ runAsProverT m assignments
    let
      aFieldElems = valueToFields a
    setAssignments (zip vars aFieldElems)
    pure $ fieldsToVar @f @a (map Var vars)

instance Monad m => MonadFresh (ProverT f m) where
  fresh = ProverT do
    { nextVar } <- get
    modify_ _ { nextVar = incrementVariable nextVar }
    pure nextVar

throwProverError :: forall f m a. Monad m => EvaluationError -> ProverT f m a
throwProverError = ProverT <<< throwError

setAssignments :: forall f m. Monad m => Array (Tuple Variable f) -> ProverT f m Unit
setAssignments vs = ProverT $
  modify_ \s ->
    s { assignments = foldl (\acc (Tuple v f) -> Map.insert v f acc) s.assignments vs }

getAssignments :: forall f m. Monad m => ProverT f m (Map Variable f)
getAssignments = ProverT $ gets _.assignments

getState
  :: forall f m
   . Monad m
  => ProverT f m (ProverState f)
getState = ProverT $ get

putState
  :: forall f m
   . Monad m
  => ProverState f
  -> ProverT f m Unit
putState = ProverT <<< put