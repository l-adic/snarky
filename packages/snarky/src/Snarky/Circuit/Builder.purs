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
import Snarky.Circuit.Constraint (R1CS)
import Snarky.Circuit.DSL (class CircuitM, class MonadFresh, AsProverT, addConstraint, fresh)
import Snarky.Circuit.Types (class ConstrainedType, Variable(..), check, fieldsToVar, sizeInFields)
import Snarky.Curves.Types (class PrimeField)
import Type.Proxy (Proxy(..))

type CircuitBuilderState f =
  { nextVar :: Int
  , constraints :: Array (R1CS f Variable)
  , publicInputs :: Array Variable
  }

emptyCircuitBuilderState :: forall f. CircuitBuilderState f
emptyCircuitBuilderState =
  { nextVar: 0
  , constraints: mempty
  , publicInputs: mempty
  }

newtype CircuitBuilderT f m a = CircuitBuilderT (StateT (CircuitBuilderState f) m a)

derive newtype instance Functor m => Functor (CircuitBuilderT f m)
derive newtype instance Monad m => Apply (CircuitBuilderT f m)
derive newtype instance Monad m => Bind (CircuitBuilderT f m)
derive newtype instance Monad m => Applicative (CircuitBuilderT f m)
derive newtype instance Monad m => Monad (CircuitBuilderT f m)
derive newtype instance Monad m => MonadState (CircuitBuilderState f) (CircuitBuilderT f m)
derive newtype instance MonadTrans (CircuitBuilderT f)

runCircuitBuilderT :: forall f a m. Monad m => CircuitBuilderT f m a -> CircuitBuilderState f -> m (Tuple a (CircuitBuilderState f))
runCircuitBuilderT (CircuitBuilderT m) s = runStateT m s

execCircuitBuilderT :: forall f a m. Monad m => CircuitBuilderT f m a -> CircuitBuilderState f -> m (CircuitBuilderState f)
execCircuitBuilderT (CircuitBuilderT m) s = execStateT m s

type CircuitBuilder f = CircuitBuilderT f Identity

runCircuitBuilder :: forall f a. CircuitBuilder f a -> CircuitBuilderState f -> Tuple a (CircuitBuilderState f)
runCircuitBuilder (CircuitBuilderT m) s = un Identity $ runStateT m s

instance Monad m => MonadFresh (CircuitBuilderT f m) where
  fresh = do
    { nextVar } <- get
    modify_ _ { nextVar = nextVar + 1 }
    pure $ Variable nextVar

instance (Monad m, PrimeField f) => CircuitM f (CircuitBuilderT f m) m where
  addConstraint c = modify_ \s ->
    s { constraints = s.constraints `snoc` c }
  exists :: forall a var n. ConstrainedType f var a => Monad n => AsProverT f n a -> CircuitBuilderT f n var
  exists _ = do
    let n = sizeInFields @f (Proxy @a)
    vars <- replicateA n fresh
    let v = fieldsToVar @f @var @a (map Var vars)
    traverse_ addConstraint (check @f @var @a v)
    pure v

  publicInputs :: forall a var. ConstrainedType f var a => Proxy a -> CircuitBuilderT f m var
  publicInputs proxy = do
    let n = sizeInFields @f proxy
    vars <- replicateA n fresh
    modify_ \s ->
      s { publicInputs = vars }
    pure $ fieldsToVar @f @var @a (map Var vars)