module Snarky.Circuit.Prover
  ( ProverM
  , ProverError(..)
  , ProverState
  , emptyProverState
  , runProverM
  , assignPublicInputs
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.State (class MonadState, State, get, modify_, runState)
import Data.Array (foldl, zip)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (replicateA)
import Snarky.Circuit.CVar (CVar(Var), EvaluationError)
import Snarky.Circuit.DSL (class CircuitM, class MonadFresh, AsProver, fresh, runAsProver)
import Snarky.Circuit.Types (class ConstrainedType, Variable(..), fieldsToVar, sizeInFields, valueToFields)
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
  , publicInputs :: Array Variable
  }

emptyProverState :: forall f. ProverState f
emptyProverState =
  { nextVar: 0
  , assignments: Map.empty
  , publicInputs: mempty
  }

newtype ProverM f a = ProverM (ExceptT ProverError (State (ProverState f)) a)

derive newtype instance Functor (ProverM f)
derive newtype instance Apply (ProverM f)
derive newtype instance Bind (ProverM f)
derive newtype instance Applicative (ProverM f)
derive newtype instance Monad (ProverM f)
derive newtype instance MonadState (ProverState f) (ProverM f)
derive newtype instance MonadThrow ProverError (ProverM f)

runProverM :: forall f a. ProverM f a -> ProverState f -> Tuple (Either ProverError a) (ProverState f)
runProverM (ProverM m) = runState (runExceptT m)

instance CircuitM f (ProverM f) where
  addConstraint _ = pure unit
  exists :: forall a var. ConstrainedType f var a => AsProver f a -> ProverM f var
  exists m = do
    let n = sizeInFields @f (Proxy @a)
    { assignments } <- get
    a <- case runAsProver m assignments of
      Left e -> throwError (EvalError e)
      Right a -> pure a
    vars <- replicateA n fresh
    do
      let aFieldElems = valueToFields a
      modify_ _ { assignments = foldl (\acc (Tuple v f) -> Map.insert v f acc) assignments (zip vars aFieldElems) }
    pure $ fieldsToVar @f @var @a (map Var vars)
  publicInputs :: forall a var. ConstrainedType f var a => Proxy a -> ProverM f var
  publicInputs proxy = do
    let n = sizeInFields @f proxy
    vars <- replicateA n fresh
    modify_ \s -> s { publicInputs = s.publicInputs }
    pure $ fieldsToVar @f @var @a (map Var vars)

instance MonadFresh (ProverM f) where
  fresh = do
    { nextVar } <- get
    modify_ _ { nextVar = nextVar + 1 }
    pure $ Variable nextVar

assignPublicInputs :: forall f var a. ConstrainedType f var a => a -> ProverM f Unit
assignPublicInputs a = do
  let fs = valueToFields a
  { publicInputs } <- get
  if Array.length fs /= Array.length publicInputs then throwError $ PublicInputsMismatch
    { expected: Array.length publicInputs
    , found: Array.length fs
    }
  else do
    let as = zip publicInputs fs
    modify_ \s ->
      s { assignments = foldl (\acc (Tuple v f) -> Map.insert v f acc) s.assignments as }
