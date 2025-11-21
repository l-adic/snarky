module Snarky.Circuit.DSL.Monad
  ( AsProverT
  , AsProver
  , addConstraint
  , class CircuitM
  , class MonadFresh
  , exists
  , fresh
  , read
  , readCVar
  , runAsProver
  , runAsProverT
  , throwAsProver
  ) where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
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
import Snarky.Circuit.Types (class CircuitType, Variable, fieldsToValue, varToFields)
import Snarky.Curves.Class (class PrimeField)

newtype AsProverT f m a = AsProverT (ExceptT (EvaluationError f Variable) (ReaderT (Map Variable f) m) a)

runAsProverT
  :: forall f a m
   . Monad m
  => AsProverT f m a
  -> Map Variable f
  -> m (Either (EvaluationError f Variable) a)
runAsProverT (AsProverT m) env = runReaderT (runExceptT m) env

type AsProver f = AsProverT f Identity

runAsProver
  :: forall f a
   . AsProver f a
  -> Map Variable f
  -> Either (EvaluationError f Variable) a
runAsProver m e = un Identity $ runAsProverT m e

readCVar :: forall f m. PrimeField f => Monad m => CVar f Variable -> AsProverT f m f
readCVar v = AsProverT do
  m <- ask
  let _lookup var = maybe (throwError $ MissingVariable var) pure $ Map.lookup var m
  CVar.eval _lookup v

read
  :: forall f var a m c
   . CircuitType f a var
  => PrimeField f
  => Monad m
  => var
  -> AsProverT f m a
read var = AsProverT do
  let fieldVars = varToFields @f @a var
  m <- ask
  let _lookup v = maybe (throwError $ MissingVariable v) pure $ Map.lookup v m
  fields <- traverse (CVar.eval _lookup) fieldVars
  pure $ fieldsToValue fields

derive newtype instance Functor m => Functor (AsProverT f m)
derive newtype instance Monad m => Apply (AsProverT f m)
derive newtype instance Monad m => Bind (AsProverT f m)
derive newtype instance Monad m => Applicative (AsProverT f m)
derive newtype instance Monad m => Monad (AsProverT f m)

instance MonadTrans (AsProverT f) where
  lift m = AsProverT $ lift $ lift m

class Monad m <= MonadFresh m where
  fresh :: m Variable

class (Monad m, MonadFresh (t m), PrimeField f, R1CSSystem (CVar f Variable) c) <= CircuitM f c t m | t -> c f, c -> f where
  exists :: forall a var. CircuitType f a var => AsProverT f m a -> t m var
  addConstraint :: c -> t m Unit

throwAsProver :: forall f m a. Monad m => EvaluationError f Variable -> AsProverT f m a
throwAsProver = AsProverT <<< throwError