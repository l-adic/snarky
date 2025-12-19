module Snarky.Backend.Builder
  ( CircuitBuilderT
  , runCircuitBuilderT
  , execCircuitBuilderT
  , CircuitBuilderState
  , emptyCircuitBuilderState
  , CircuitBuilder
  , runCircuitBuilder
  , setPublicInputVars
  , appendConstraint
  , putState
  , getState
  ) where

import Prelude

import Control.Monad.State (StateT, execStateT, get, modify_, put, runStateT)
import Control.Monad.Trans.Class (class MonadTrans)
import Data.Array (snoc)
import Data.Foldable (traverse_)
import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (Tuple)
import Data.Unfoldable (replicateA)
import Snarky.Circuit.CVar (CVar(Var), Variable, incrementVariable, v0)
import Snarky.Circuit.DSL.Monad (class CircuitM, class ConstraintM, class MonadFresh, AsProverT, Snarky, addConstraint, fresh)
import Snarky.Circuit.Types (class CheckedType, class CircuitType, check, fieldsToVar, sizeInFields)
import Snarky.Constraint.Basic (class BasicSystem, Basic)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

type CircuitBuilderState c =
  { nextVar :: Variable
  , constraints :: Array c
  , publicInputs :: Array Variable
  }

emptyCircuitBuilderState :: forall c. CircuitBuilderState c
emptyCircuitBuilderState =
  { nextVar: v0
  , constraints: mempty
  , publicInputs: mempty
  }

newtype CircuitBuilderT c m a = CircuitBuilderT (StateT (CircuitBuilderState c) m a)

derive newtype instance Functor m => Functor (CircuitBuilderT c m)
derive newtype instance Monad m => Apply (CircuitBuilderT c m)
derive newtype instance Monad m => Bind (CircuitBuilderT c m)
derive newtype instance Monad m => Applicative (CircuitBuilderT c m)
derive newtype instance Monad m => Monad (CircuitBuilderT c m)
derive newtype instance MonadTrans (CircuitBuilderT c)

runCircuitBuilderT :: forall c m a. Monad m => CircuitBuilderT c m a -> CircuitBuilderState c -> m (Tuple a (CircuitBuilderState c))
runCircuitBuilderT (CircuitBuilderT m) s = runStateT m s

execCircuitBuilderT :: forall c m a. Monad m => CircuitBuilderT c m a -> CircuitBuilderState c -> m (CircuitBuilderState c)
execCircuitBuilderT (CircuitBuilderT m) s = execStateT m s

type CircuitBuilder c = CircuitBuilderT c Identity

runCircuitBuilder :: forall c a. CircuitBuilder c a -> CircuitBuilderState c -> Tuple a (CircuitBuilderState c)
runCircuitBuilder (CircuitBuilderT m) s = un Identity $ runStateT m s

instance Monad m => MonadFresh (CircuitBuilderT c m) where
  fresh = CircuitBuilderT do
    { nextVar } <- get
    modify_ _ { nextVar = incrementVariable nextVar }
    pure nextVar

instance ConstraintM (CircuitBuilderT (Basic f)) (Basic f) where
  addConstraint' = appendConstraint

instance (Monad m, PrimeField f, BasicSystem f c', ConstraintM (CircuitBuilderT c) c') => CircuitM f c' (CircuitBuilderT c) m where
  exists :: forall a var. CheckedType var c' => CircuitType f a var => ConstraintM (CircuitBuilderT c) c' => AsProverT f m a -> Snarky c' (CircuitBuilderT c) m var
  exists _ = do
    let n = sizeInFields (Proxy @f) (Proxy @a)
    vars <- replicateA n fresh
    let v = fieldsToVar @f @a (map Var vars)
    traverse_ addConstraint (check v)
    pure v

setPublicInputVars :: forall f m. Monad m => Array Variable -> CircuitBuilderT f m Unit
setPublicInputVars vars = CircuitBuilderT $ modify_ \s ->
  s { publicInputs = vars }

appendConstraint :: forall m c. Monad m => c -> CircuitBuilderT c m Unit
appendConstraint c = CircuitBuilderT $ modify_ \s ->
  s { constraints = s.constraints `snoc` c }

getState
  :: forall m c
   . Monad m
  => CircuitBuilderT c m (CircuitBuilderState c)
getState = CircuitBuilderT $ get

putState
  :: forall m c
   . Monad m
  => (CircuitBuilderState c)
  -> CircuitBuilderT c m Unit
putState = CircuitBuilderT <<< put