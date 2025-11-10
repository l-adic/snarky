module Snarky.Circuit.Builder
  ( CircuitBuilderM
  , runCircuitBuilderM
  , CircuitBuilderState
  , emptyCircuitBuilderState
  ) where

import Prelude

import Control.Monad.State (class MonadState, State, get, modify_, runState)
import Data.Array (snoc)
import Data.Tuple (Tuple)
import Data.Unfoldable (replicateA)
import Snarky.Circuit.CVar (CVar(Var))
import Snarky.Circuit.Constraint (R1CS)
import Snarky.Circuit.DSL (class CircuitM, class MonadFresh, AsProver, fresh)
import Snarky.Circuit.Types (class ConstrainedType, Variable(..), fieldsToVar, sizeInFields)
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

newtype CircuitBuilderM f a = CircuitBuilderM (State (CircuitBuilderState f) a)

derive newtype instance Functor (CircuitBuilderM f)
derive newtype instance Apply (CircuitBuilderM f)
derive newtype instance Bind (CircuitBuilderM f)
derive newtype instance Applicative (CircuitBuilderM f)
derive newtype instance Monad (CircuitBuilderM f)
derive newtype instance MonadState (CircuitBuilderState f) (CircuitBuilderM f)

runCircuitBuilderM :: forall f a. CircuitBuilderM f a -> CircuitBuilderState f -> Tuple a (CircuitBuilderState f)
runCircuitBuilderM (CircuitBuilderM m) = runState m

instance MonadFresh (CircuitBuilderM f) where
  fresh = do
    { nextVar } <- get
    modify_ _ { nextVar = nextVar + 1 }
    pure $ Variable nextVar

instance CircuitM f (CircuitBuilderM f) where
  addConstraint c = modify_ \s ->
    s { constraints = s.constraints `snoc` c }
  exists :: forall a var. ConstrainedType f var a => AsProver f a -> CircuitBuilderM f var
  exists _ = do
    let n = sizeInFields @f (Proxy @a)
    vars <- replicateA n fresh
    pure $ fieldsToVar @f @var @a (map Var vars)
  publicInputs :: forall a var. ConstrainedType f var a => Proxy a -> CircuitBuilderM f var
  publicInputs proxy = do
    let n = sizeInFields @f proxy
    vars <- replicateA n fresh
    modify_ \s ->
      s { publicInputs = vars }
    pure $ fieldsToVar @f @var @a (map Var vars)