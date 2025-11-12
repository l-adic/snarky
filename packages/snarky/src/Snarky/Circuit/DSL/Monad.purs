module Snarky.Circuit.DSL
  ( AsProverT
  , AsProver
  , addConstraint
  , class CircuitM
  , class MonadFresh
  , exists
  , fresh
  , publicInputs
  , read
  , readCVar
  , runAsProver
  , runAsProverT
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (class MonadAsk, ReaderT, ask, runReaderT)
import Control.Monad.Trans.Class (class MonadTrans, lift)
import Data.Either (Either)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (maybe)
import Data.Newtype (un)
import Data.Traversable (traverse)
import Snarky.Circuit.CVar (CVar, EvaluationError(..))
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Constraint.Class (class R1CSSystem)
import Snarky.Circuit.Types (class ConstrainedType, Variable, fieldsToValue, varToFields)
import Snarky.Curves.Types (class PrimeField)
import Type.Proxy (Proxy)

newtype AsProverT f m a = AsProverT (ExceptT (EvaluationError Variable) (ReaderT (Map Variable f) m) a)

runAsProverT
  :: forall f a m
   . Monad m
  => AsProverT f m a
  -> Map Variable f
  -> m (Either (EvaluationError Variable) a)
runAsProverT (AsProverT m) env = runReaderT (runExceptT m) env

type AsProver f = AsProverT f Identity

runAsProver
  :: forall f a
   . AsProver f a
  -> Map Variable f
  -> Either (EvaluationError Variable) a
runAsProver m e = un Identity $ runAsProverT m e

read
  :: forall f var a m c
   . ConstrainedType f var a c
  => PrimeField f
  => Monad m
  => var
  -> AsProverT f m a
read var = do
  let fieldVars = varToFields @_ @_ @a var
  m <- ask
  let _lookup v = maybe (throwError $ MissingVariable v) pure $ Map.lookup v m
  fields <- traverse (CVar.eval _lookup) fieldVars
  pure $ fieldsToValue fields

derive newtype instance Functor m => Functor (AsProverT f m)
derive newtype instance Monad m => Apply (AsProverT f m)
derive newtype instance Monad m => Bind (AsProverT f m)
derive newtype instance Monad m => Applicative (AsProverT f m)
derive newtype instance Monad m => Monad (AsProverT f m)
derive newtype instance Monad m => MonadAsk (Map Variable f) (AsProverT f m)
derive newtype instance Monad m => MonadThrow (EvaluationError Variable) (AsProverT f m)

instance MonadTrans (AsProverT f) where
  lift m = AsProverT $ lift $ lift m

class Monad m <= MonadFresh m where
  fresh :: m Variable

class (Monad n, MonadFresh m, PrimeField f, R1CSSystem (CVar f Variable) c) <= CircuitM f c m n | m -> n c f, c -> f where
  exists :: forall a var. ConstrainedType f var a c => AsProverT f n a -> m var
  addConstraint :: c -> m Unit
  publicInputs :: forall a var. ConstrainedType f var a c => Proxy a -> m var

readCVar :: forall f m. PrimeField f => Monad m => CVar f Variable -> AsProverT f m f
readCVar v = do
  m <- ask
  let _lookup var = maybe (throwError $ MissingVariable var) pure $ Map.lookup var m
  CVar.eval _lookup v