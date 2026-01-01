module Snarky.Constraint.Kimchi.Reduction
  ( GenericPlonkConstraint
  , Rows
  , getRows
  , class PlonkReductionM
  , createInternalVariable
  , addGenericPlonkConstraint
  , reduceAffineExpression
  , reduceToVariable
  , reduceAsBuilder
  , reduceAsProver
  , finalizeGateQueue
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.State (class MonadState, State, get, gets, modify_, runState)
import Data.Array as A
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.List.NonEmpty (fromFoldable)
import Data.List.Types (List(..), NonEmptyList(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, un)
import Data.NonEmpty (NonEmpty(..))
import Data.Tuple (Tuple(..))
import Record as Record
import Snarky.Circuit.CVar (AffineExpression(..), CVar, EvaluationError(..), Variable, evalAffineExpression, incrementVariable, reduceToAffineExpression)
import Snarky.Constraint.Kimchi.Wire (class ToKimchiRows, GateKind(..), KimchiRow, KimchiWireRow)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Vector (Vector, (:<))
import Snarky.Data.Vector as Vector
import Type.Proxy (Proxy(..))

type GenericPlonkConstraint f =
  { cl :: f -- Left coefficient
  , vl :: Maybe Variable -- Left variable
  , cr :: f -- Right coefficient  
  , vr :: Maybe Variable -- Right variable
  , co :: f -- Output coefficient
  , vo :: Maybe Variable -- Output variable
  , m :: f -- Multiplication coefficient  
  , c :: f -- Constant term
  }

class Monad m <= PlonkReductionM m f | m -> f where
  createInternalVariable
    :: AffineExpression f
    -> m Variable
  addGenericPlonkConstraint
    :: GenericPlonkConstraint f
    -> m Unit

-- return a * x where a \in f and x is a variable.
reduceAffineExpression
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => AffineExpression f
  -> m (Tuple (Maybe Variable) f)
reduceAffineExpression (AffineExpression { constant, terms }) = case fromFoldable terms of
  Nothing -> pure $ Tuple Nothing (fromMaybe zero constant)
  Just (NonEmptyList (NonEmpty head tail)) -> case tail of
    Nil -> case constant of
      Nothing -> pure $ lmap Just head
      Just c -> do
        vo <- createInternalVariable $ AffineExpression { constant, terms: [ head ] }
        let Tuple vl cl = head
        addGenericPlonkConstraint { vl: Just vl, cl, vr: Nothing, cr: zero, vo: Just vo, co: -one, m: zero, c }
        pure $ Tuple (Just vo) one
    Cons (Tuple vr cr) Nil -> do
      let Tuple vl cl = head
      vo <- createInternalVariable $ AffineExpression { constant, terms: [ Tuple vl cl, Tuple vr cr ] }
      addGenericPlonkConstraint { vl: Just vl, cl, vr: Just vr, cr, vo: Just vo, co: -one, m: zero, c: fromMaybe zero constant }
      pure $ Tuple (Just vo) one
    Cons head' tail' -> do
      Tuple vr cr <-
        foldM
          ( \(Tuple vr cr) (Tuple vl cl) -> do
              vo <- createInternalVariable $ AffineExpression { constant: Nothing, terms: [ Tuple vl cl, Tuple vr cr ] }
              addGenericPlonkConstraint { cl, vl: Just vl, cr, vr: Just vr, co: -one, vo: Just vo, m: zero, c: zero }
              pure $ Tuple vo one
          )
          head'
          tail'
      let Tuple vl cl = head
      vo <- createInternalVariable $ AffineExpression { constant, terms: [ Tuple vl cl, Tuple vr cr ] }
      addGenericPlonkConstraint { vl: Just vl, cl, vr: Just vr, cr, vo: Just vo, co: -one, m: zero, c: fromMaybe zero constant }
      pure $ Tuple (Just vo) one

reduceToVariable
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => CVar f Variable
  -> m Variable
reduceToVariable var = do
  Tuple mvar c <- reduceAffineExpression $ reduceToAffineExpression var
  case mvar of
    -- result is a constant
    Nothing -> do
      vl <- createInternalVariable $ AffineExpression { constant: Just c, terms: mempty }
      addGenericPlonkConstraint { cl: one, vl: Just vl, cr: zero, vr: Nothing, co: zero, vo: Nothing, m: zero, c: (-c) }
      pure vl
    -- result is c * v
    Just v ->
      if c == one then pure v
      else do
        c_times_v <- createInternalVariable $ AffineExpression { constant: zero, terms: [ Tuple v c ] }
        -- c * v - c_times_v = 0
        addGenericPlonkConstraint { cl: c, vl: Just v, cr: zero, vr: Nothing, co: -one, vo: Just c_times_v, m: zero, c: zero }
        pure c_times_v

newtype Rows f = Rows (KimchiRow f)

getRows :: forall f. Rows f -> KimchiRow f
getRows (Rows x) = x

instance ToKimchiRows f (Rows f) where
  toKimchiRows (Rows as) = Array.singleton as

reduceAsBuilder
  :: forall f a
   . PrimeField f
  => { nextVariable :: Variable
     , queuedGenericGate :: Maybe (GenericPlonkConstraint f)
     , wireState :: KimchiWireRow f
     }
  -> (forall m. PlonkReductionM m f => m a)
  -> Tuple
       a
       { nextVariable :: Variable
       , constraints :: Array (Rows f)
       , queuedGenericGate :: Maybe (GenericPlonkConstraint f)
       , wireState :: KimchiWireRow f
       }
reduceAsBuilder { nextVariable, wireState, queuedGenericGate } m =
  let
    initState = { nextVariable, constraints: mempty, wireState, queuedGenericGate }
    Tuple a s = runState (un PlonkBuilder m) initState
  in
    Tuple a (Record.set (Proxy @"constraints") (map Rows s.constraints) s)

reduceAsProver
  :: forall f a
   . PrimeField f
  => { nextVariable :: Variable
     , assignments :: Map Variable f
     }
  -> (forall m. PlonkReductionM m f => m a)
  -> Either
       EvaluationError
       ( Tuple
           a
           { nextVariable :: Variable
           , assignments :: Map Variable f
           }
       )
reduceAsProver s m =
  case runState (runExceptT $ un PlonkProver m) s of
    Tuple (Left e) _ -> Left e
    Tuple (Right a) s' -> Right $ Tuple a s'

--------------------------------------------------------------------------------

type BuilderReductionState f =
  { constraints :: Array (KimchiRow f)
  , nextVariable :: Variable
  , queuedGenericGate :: Maybe (GenericPlonkConstraint f)
  , wireState :: KimchiWireRow f
  }

newtype PlonkBuilder f a = PlonkBuilder (State (BuilderReductionState f) a)

derive newtype instance Functor (PlonkBuilder f)
derive newtype instance Apply (PlonkBuilder f)
derive newtype instance Applicative (PlonkBuilder f)
derive newtype instance Bind (PlonkBuilder f)
derive newtype instance Monad (PlonkBuilder f)
derive newtype instance MonadState (BuilderReductionState f) (PlonkBuilder f)

derive instance Newtype (PlonkBuilder f a) _

constraintToCoeffs
  :: forall f
   . PrimeField f
  => GenericPlonkConstraint f
  -> Vector 5 f
constraintToCoeffs gate =
  gate.cl :< gate.cr :< gate.co :< gate.m :< gate.c :< Vector.nil

finalizeGateQueue
  :: forall f r
   . PrimeField f
  => { queuedGenericGate :: Maybe (GenericPlonkConstraint f)
     | r
     }
  -> Maybe (Rows f)
finalizeGateQueue { queuedGenericGate } =
  map
    ( \gate ->
        let
          gateCoeffs = constraintToCoeffs gate
          zeros = Vector.generate $ const zero :: Vector 10 f
          coeffRow = gateCoeffs `Vector.append` zeros
          variables = gate.vl :< gate.vr :< gate.vo :< Vector.generate (const Nothing)
        in
          Rows { kind: GenericPlonkGate, coeffs: coeffRow, variables }

    )
    queuedGenericGate

-- Handle gate batching and wire placement for GenericPlonk gates
handleGateBatching
  :: forall f
   . PrimeField f
  => GenericPlonkConstraint f
  -> PlonkBuilder f (Maybe (KimchiRow f))
handleGateBatching newGate = do
  mqueued <- gets _.queuedGenericGate
  case mqueued of
    Nothing -> do
      -- No queued gate, store this one for batching
      modify_ _ { queuedGenericGate = Just newGate }
      pure Nothing
    Just queuedGate -> do
      -- clear the queue
      modify_ _ { queuedGenericGate = Nothing }
      pure $ Just $ emitDoubleGateRow queuedGate newGate
  where
  emitDoubleGateRow gate1 gate2 =
    let
      vars = gate1.vl :< gate1.vr :< gate1.vo :< gate2.vl :< gate2.vr :< gate2.vo :< Vector.generate (const Nothing)
      coeffs = constraintToCoeffs gate1
        `Vector.append` constraintToCoeffs gate2
        `Vector.append` Vector.generate (const zero)
    in
      { kind: GenericPlonkGate, coeffs, variables: vars }

instance PrimeField f => PlonkReductionM (PlonkBuilder f) f where
  addGenericPlonkConstraint c = do
    mconstraint <- handleGateBatching c
    case mconstraint of
      Nothing -> pure unit
      Just c' -> modify_ \s ->
        s { constraints = s.constraints `A.snoc` c' }
  createInternalVariable _ = do
    nextVariable <- gets _.nextVariable
    modify_ _ { nextVariable = incrementVariable nextVariable }
    pure nextVariable

type ProverReductionState f =
  { nextVariable :: Variable
  , assignments :: Map Variable f
  }

newtype PlonkProver f a = PlonkProver (ExceptT EvaluationError (State (ProverReductionState f)) a)

derive newtype instance Functor (PlonkProver f)
derive newtype instance Apply (PlonkProver f)
derive newtype instance Applicative (PlonkProver f)
derive newtype instance Bind (PlonkProver f)
derive newtype instance Monad (PlonkProver f)
derive newtype instance MonadState (ProverReductionState f) (PlonkProver f)
derive newtype instance MonadThrow EvaluationError (PlonkProver f)

derive instance Newtype (PlonkProver f a) _

instance (PrimeField f) => PlonkReductionM (PlonkProver f) f where
  addGenericPlonkConstraint _ = pure unit
  createInternalVariable e = do
    { nextVariable, assignments } <- get
    let
      _lookup v = case Map.lookup v assignments of
        Nothing -> throwError $ MissingVariable v
        Just a -> pure a
    a <- evalAffineExpression e _lookup
    modify_
      _
        { nextVariable = incrementVariable nextVariable
        , assignments = Map.insert nextVariable a assignments
        }
    pure nextVariable