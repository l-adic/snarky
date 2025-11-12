module Snarky.Circuit.Builder
  ( CircuitBuilderT
  , runCircuitBuilderT
  , execCircuitBuilderT
  , CircuitBuilderState
  , emptyCircuitBuilderState
  , CircuitBuilder
  , runCircuitBuilder
  ) where

import Prelude

import Control.Monad.State (class MonadState, StateT, execStateT, get, modify_, runStateT)
import Control.Monad.Trans.Class (class MonadTrans)
import Data.Array (snoc)
import Data.Foldable (traverse_)
import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (Tuple)
import Data.Unfoldable (replicateA)
import Snarky.Circuit.CVar (CVar(Var))
import Snarky.Circuit.Constraint.Class (class R1CSSystem)
import Snarky.Circuit.DSL (class CircuitM, class MonadFresh, AsProverT, addConstraint, fresh)
import Snarky.Circuit.Types (class ConstrainedType, Variable(..), check, fieldsToVar, sizeInFields)
import Snarky.Curves.Types (class PrimeField)
import Type.Proxy (Proxy(..))

type CircuitBuilderState :: Type -> Type -> Type
type CircuitBuilderState f c =
  { nextVar :: Int
  , constraints :: Array c
  , publicInputs :: Array Variable
  }

emptyCircuitBuilderState :: forall f c. CircuitBuilderState f c
emptyCircuitBuilderState =
  { nextVar: 0
  , constraints: mempty
  , publicInputs: mempty
  }

newtype CircuitBuilderT f c m a = CircuitBuilderT (StateT (CircuitBuilderState f c) m a)

derive newtype instance Functor m => Functor (CircuitBuilderT c f m)
derive newtype instance Monad m => Apply (CircuitBuilderT f c m)
derive newtype instance Monad m => Bind (CircuitBuilderT f c m)
derive newtype instance Monad m => Applicative (CircuitBuilderT f c m)
derive newtype instance Monad m => Monad (CircuitBuilderT f c m)
derive newtype instance Monad m => MonadState (CircuitBuilderState f c) (CircuitBuilderT f c m)
derive newtype instance MonadTrans (CircuitBuilderT f c)

runCircuitBuilderT :: forall f a m c. Monad m => CircuitBuilderT f c m a -> CircuitBuilderState f c -> m (Tuple a (CircuitBuilderState f c))
runCircuitBuilderT (CircuitBuilderT m) s = runStateT m s

execCircuitBuilderT :: forall f a m c. Monad m => CircuitBuilderT f c m a -> CircuitBuilderState f c -> m (CircuitBuilderState f c)
execCircuitBuilderT (CircuitBuilderT m) s = execStateT m s

type CircuitBuilder f c = CircuitBuilderT f c Identity

runCircuitBuilder :: forall f a c. CircuitBuilder f c a -> CircuitBuilderState f c -> Tuple a (CircuitBuilderState f c)
runCircuitBuilder (CircuitBuilderT m) s = un Identity $ runStateT m s

instance Monad m => MonadFresh (CircuitBuilderT f c m) where
  fresh = do
    { nextVar } <- get
    modify_ _ { nextVar = nextVar + 1 }
    pure $ Variable nextVar

instance (Monad m, PrimeField f, R1CSSystem (CVar f Variable) c) => CircuitM f c (CircuitBuilderT f c m) m where
  addConstraint c = modify_ \s ->
    s { constraints = s.constraints `snoc` c }
  exists :: forall a var. ConstrainedType f var a c => AsProverT f m a -> CircuitBuilderT f c m var
  exists _ = do
    let n = sizeInFields @f (Proxy @a)
    vars <- replicateA n fresh
    let v = fieldsToVar @f @var @a (map Var vars)
    traverse_ (addConstraint @f @c) (check @f @var @a v)
    pure v

  publicInputs :: forall a var. ConstrainedType f var a c => Proxy a -> CircuitBuilderT f c m var
  publicInputs proxy = do
    let n = sizeInFields @f proxy
    vars <- replicateA n fresh
    modify_ \s ->
      s { publicInputs = vars }
    pure $ fieldsToVar @f @var @a (map Var vars)