-- | Circuit compilation backend.
-- |
-- | `CircuitBuilderT` is a `CircuitM` instance that collects constraints without
-- | computing witness values. Used during compilation to extract the constraint
-- | system structure. The `exists` implementation allocates fresh variables and
-- | adds type-specific checks, but ignores the prover computation.
module Snarky.Backend.Builder
  ( CircuitBuilderT
  , initialState
  , runCircuitBuilderT
  , execCircuitBuilderT
  , CircuitBuilderState
  , CircuitBuilder
  , runCircuitBuilder
  , setPublicInputVars
  , appendConstraint
  , putState
  , getState
  , class Finalizer
  , finalize
  , class CompileCircuit
  ) where

import Prelude

import Control.Monad.State (StateT, execStateT, get, modify_, put, runStateT)
import Control.Monad.Trans.Class (class MonadTrans)
import Data.Array (snoc)
import Data.Array as Array
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Newtype (un)
import Data.Tuple (Tuple)
import Data.Unfoldable (replicateA)
import Snarky.Circuit.CVar (CVar(Var), Variable, incrementVariable, v0)
import Snarky.Circuit.DSL.Monad (class CheckedType, class CircuitM, class ConstraintM, class MonadFresh, class WithLabel, AsProverT, Snarky, check, fresh)
import Snarky.Circuit.Types (class CircuitType, fieldsToVar, sizeInFields)
import Snarky.Constraint.Basic (class BasicSystem, Basic)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

type CircuitBuilderState c r =
  { nextVar :: Variable
  , constraints :: Array c
  , publicInputs :: Array Variable
  , aux :: r
  , labelStack :: Array String
  , varMetadata :: Map Variable (Array String)
  }

newtype CircuitBuilderT c r m a = CircuitBuilderT (StateT (CircuitBuilderState c r) m a)

derive newtype instance Functor m => Functor (CircuitBuilderT c r m)
derive newtype instance Monad m => Apply (CircuitBuilderT c r m)
derive newtype instance Monad m => Bind (CircuitBuilderT c r m)
derive newtype instance Monad m => Applicative (CircuitBuilderT c r m)
derive newtype instance Monad m => Monad (CircuitBuilderT c r m)
derive newtype instance MonadTrans (CircuitBuilderT c r)

class Finalizer c r where
  finalize :: CircuitBuilderState c r -> CircuitBuilderState c r

instance Finalizer (Basic f) r where
  finalize = identity

runCircuitBuilderT
  :: forall c r m a
   . Monad m
  => CircuitBuilderT c r m a
  -> CircuitBuilderState c r
  -> m (Tuple a (CircuitBuilderState c r))
runCircuitBuilderT (CircuitBuilderT m) s = runStateT m s

execCircuitBuilderT
  :: forall c r m a
   . Monad m
  => CircuitBuilderT c r m a
  -> CircuitBuilderState c r
  -> m (CircuitBuilderState c r)
execCircuitBuilderT (CircuitBuilderT m) s = execStateT m s

type CircuitBuilder c r = CircuitBuilderT c r Identity

runCircuitBuilder
  :: forall c r a
   . CircuitBuilder c r a
  -> CircuitBuilderState c r
  -> Tuple a (CircuitBuilderState c r)
runCircuitBuilder (CircuitBuilderT m) s = un Identity $ runStateT m s

instance Monad m => MonadFresh (CircuitBuilderT c r m) where
  fresh = CircuitBuilderT do
    s <- get
    let v = s.nextVar
    put $ s
      { nextVar = incrementVariable v
      , varMetadata = Map.insert v s.labelStack s.varMetadata
      }
    pure v

class
  ( BasicSystem f c'
  , ConstraintM (CircuitBuilderT c r) c'
  , Finalizer c r
  ) <=
  CompileCircuit f c c' r
  | f c -> c'

instance ConstraintM (CircuitBuilderT (Basic f) r) (Basic f) where
  addConstraint' = appendConstraint

instance PrimeField f => CompileCircuit f (Basic f) (Basic f) r

initialState :: forall c. CircuitBuilderState c Unit
initialState =
  { nextVar: v0
  , constraints: mempty
  , publicInputs: mempty
  , aux: unit
  , labelStack: []
  , varMetadata: Map.empty
  }

instance
  ( Monad m
  , PrimeField f
  , BasicSystem f c'
  , ConstraintM (CircuitBuilderT c r) c'
  ) =>
  CircuitM f c' (CircuitBuilderT c r) m where
  exists
    :: forall a var
     . CircuitType f a var
    => CheckedType f c' var
    => ConstraintM (CircuitBuilderT c r) c'
    => AsProverT f m a
    -> Snarky c' (CircuitBuilderT c r) m var
  exists _ = do
    let n = sizeInFields (Proxy @f) (Proxy @a)
    vars <- replicateA n fresh
    let v = fieldsToVar @f @a (map Var vars)
    check v
    pure v

setPublicInputVars
  :: forall f r m
   . Monad m
  => Array Variable
  -> CircuitBuilderT f r m Unit
setPublicInputVars vars = CircuitBuilderT $ modify_ \s ->
  s { publicInputs = vars }

appendConstraint
  :: forall m c r
   . Monad m
  => c
  -> CircuitBuilderT c r m Unit
appendConstraint c = CircuitBuilderT $ modify_ \s ->
  s { constraints = s.constraints `snoc` c }

getState
  :: forall m c r
   . Monad m
  => CircuitBuilderT c r m (CircuitBuilderState c r)
getState = CircuitBuilderT $ get

putState
  :: forall m c r
   . Monad m
  => (CircuitBuilderState c r)
  -> CircuitBuilderT c r m Unit
putState = CircuitBuilderT <<< put

instance WithLabel (CircuitBuilderT c r) where
  withLabel l (CircuitBuilderT m) = CircuitBuilderT do
    modify_ \s -> s { labelStack = Array.snoc s.labelStack l }
    res <- m
    modify_ \s -> s { labelStack = Array.init s.labelStack # fromMaybe [] }
    pure res
