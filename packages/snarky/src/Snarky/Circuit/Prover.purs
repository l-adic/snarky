module Snarky.Circuit.Prover
  ( ProverT
  , runProverT
  , ProverState
  , emptyProverState
  , Prover
  , runProver
  , throwProverError
  , setAssignments
  , getAssignments
  ) where

import Prelude

import Control.Monad.Except (ExceptT(..), lift, runExceptT, throwError)
import Control.Monad.State (StateT, get, gets, modify_, runStateT)
import Control.Monad.Trans.Class (class MonadTrans)
import Data.Array (foldl, zip, (..))
import Data.Either (Either)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Snarky.Circuit.CVar (CVar(Var), EvaluationError)
import Snarky.Circuit.Constraint.Class (class R1CSSystem)
import Snarky.Circuit.DSL.Monad (class CircuitM, class MonadFresh, AsProverT, runAsProverT)
import Snarky.Circuit.Types (class CircuitType, Variable(..), fieldsToVar, sizeInFields, valueToFields)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

type ProverState f =
  { nextVar :: Int
  , assignments :: Map Variable f
  }

emptyProverState :: forall f. ProverState f
emptyProverState =
  { nextVar: 0
  , assignments: Map.empty
  }

newtype ProverT f m a = ProverT (ExceptT (EvaluationError f Variable) (StateT (ProverState f) m) a)

derive newtype instance Functor m => Functor (ProverT f m)
derive newtype instance Monad m => Apply (ProverT f m)
derive newtype instance Monad m => Bind (ProverT f m)
derive newtype instance Monad m => Applicative (ProverT f m)
derive newtype instance Monad m => Monad (ProverT f m)

-- TODO: why is this not newtype derivable
instance MonadTrans (ProverT f) where
  lift m = ProverT $ lift $ lift m

runProverT :: forall f a m. Monad m => ProverT f m a -> ProverState f -> m (Tuple (Either (EvaluationError f Variable) a) (ProverState f))
runProverT (ProverT m) s = runStateT (runExceptT m) s

type Prover f = ProverT f Identity

runProver :: forall f a. Prover f a -> ProverState f -> Tuple (Either (EvaluationError f Variable) a) (ProverState f)
runProver (ProverT m) s = un Identity $ runStateT (runExceptT m) s

instance (Monad m, PrimeField f, R1CSSystem (CVar f Variable) c) => CircuitM f c (ProverT f) m where
  addConstraint _ = pure unit
  exists :: forall a var. CircuitType f a var => AsProverT f m a -> ProverT f m var
  exists m = ProverT do
    { assignments } <- get
    a <- ExceptT $ lift $ runAsProverT m assignments
    vars <- do
      { nextVar } <- get
      let n = sizeInFields (Proxy @f) (Proxy @a)
      let vars = Variable <$> (nextVar .. (nextVar + n - 1))
      modify_
        _
          { nextVar = nextVar + n
          , assignments =
              let
                aFieldElems = valueToFields a
              in
                foldl
                  ( \acc (Tuple v f) ->
                      Map.insert v f acc
                  )
                  assignments
                  (zip vars aFieldElems)
          }
      pure vars
    pure $ fieldsToVar @f @a (map Var vars)

instance Monad m => MonadFresh (ProverT f m) where
  fresh = ProverT do
    { nextVar } <- get
    modify_ _ { nextVar = nextVar + 1 }
    pure $ Variable nextVar

throwProverError :: forall f m a. Monad m => (EvaluationError f Variable) -> ProverT f m a
throwProverError = ProverT <<< throwError

setAssignments :: forall f m. Monad m => Array (Tuple Variable f) -> ProverT f m Unit
setAssignments vs = ProverT $
  modify_ \s ->
    s { assignments = foldl (\acc (Tuple v f) -> Map.insert v f acc) s.assignments vs }

getAssignments :: forall f m. Monad m => ProverT f m (Map Variable f)
getAssignments = ProverT $ gets _.assignments