module Snarky.Circuit.Prover
  ( ProverT
  , runProverT
  , ProverError(..)
  , ProverState
  , emptyProverState
  , Prover
  , runProver
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except (ExceptT, lift, runExceptT)
import Control.Monad.State (class MonadState, StateT, get, modify_, runStateT)
import Control.Monad.Trans.Class (class MonadTrans)
import Data.Array (foldl, zip)
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Newtype (un)
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (replicateA)
import Snarky.Circuit.CVar (CVar(Var), EvaluationError)
import Snarky.Circuit.Constraint.Class (class R1CSSystem)
import Snarky.Circuit.DSL (class CircuitM, class MonadFresh, AsProverT, fresh, runAsProverT)
import Snarky.Circuit.Types (class ConstrainedType, Variable(..), fieldsToVar, sizeInFields, valueToFields)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

data ProverError
  = EvalError (EvaluationError Variable)
  | PublicInputsMismatch { expected :: Int, found :: Int }

derive instance Generic ProverError _
derive instance Eq ProverError
instance Show ProverError where
  show = genericShow

type ProverState f =
  { nextVar :: Int
  , assignments :: Map Variable f
  }

emptyProverState :: forall f. ProverState f
emptyProverState =
  { nextVar: 0
  , assignments: Map.empty
  }

newtype ProverT f m a = ProverT (ExceptT ProverError (StateT (ProverState f) m) a)

derive newtype instance Functor m => Functor (ProverT f m)
derive newtype instance Monad m => Apply (ProverT f m)
derive newtype instance Monad m => Bind (ProverT f m)
derive newtype instance Monad m => Applicative (ProverT f m)
derive newtype instance Monad m => Monad (ProverT f m)
derive newtype instance Monad m => MonadState (ProverState f) (ProverT f m)
derive newtype instance Monad m => MonadThrow ProverError (ProverT f m)
-- derive newtype instance MonadTrans (ProverT f)

-- TODO: why is this not newtype derivable
instance MonadTrans (ProverT f) where
  lift m = ProverT $ lift $ lift m

runProverT :: forall f a m. Monad m => ProverT f m a -> ProverState f -> m (Tuple (Either ProverError a) (ProverState f))
runProverT (ProverT m) s = runStateT (runExceptT m) s

type Prover f = ProverT f Identity

runProver :: forall f a. Prover f a -> ProverState f -> Tuple (Either ProverError a) (ProverState f)
runProver (ProverT m) s = un Identity $ runStateT (runExceptT m) s

instance (Monad m, PrimeField f, R1CSSystem (CVar f Variable) c) => CircuitM f c (ProverT f) m where
  addConstraint _ = pure unit
  exists :: forall a var. ConstrainedType f a c var => AsProverT f m a -> ProverT f m var
  exists m = do
    let n = sizeInFields @f (Proxy @a)
    { assignments } <- get
    res <- lift $ runAsProverT m assignments
    a <- case res of
      Left e -> throwError (EvalError e)
      Right a -> pure a
    vars <- replicateA n fresh
    do
      let aFieldElems = valueToFields a
      modify_ _ { assignments = foldl (\acc (Tuple v f) -> Map.insert v f acc) assignments (zip vars aFieldElems) }
    pure $ fieldsToVar @f @a (map Var vars)

instance Monad m => MonadFresh (ProverT f m) where
  fresh = do
    { nextVar } <- get
    modify_ _ { nextVar = nextVar + 1 }
    pure $ Variable nextVar