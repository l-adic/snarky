module Snarky.Constraint.Kimchi.Reduction
  ( class PlonkReductionM
  , createInternalVariable
  , addInternalPlonkConstraint
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
import Control.Monad.State (class MonadState, State, get, modify_, runState)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Foldable (foldM, for_)
import Data.List.NonEmpty (fromFoldable)
import Data.List.Types (List(..), NonEmptyList(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, un)
import Data.NonEmpty (NonEmpty(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Snarky.Circuit.CVar (AffineExpression(..), CVar, EvaluationError(..), Variable, evalAffineExpression, incrementVariable, reduceToAffineExpression)
import Snarky.Constraint.Kimchi.Types (GenericPlonkConstraint)
import Snarky.Constraint.Kimchi.Wire (GateKind(..), KimchiWireRow, KimchiRow)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Vector (Vector, (:<))
import Snarky.Data.Vector as Vector

class Monad m <= PlonkReductionM m f | m -> f where
  createInternalVariable
    :: AffineExpression f
    -> m Variable
  addInternalPlonkConstraint
    :: GenericPlonkConstraint f
    -> m Unit
  -- WARNING: External use only. Doesn't add the constraint to the queue
  addGenericPlonkConstraint
    :: GenericPlonkConstraint f
    -> m (Maybe (KimchiRow f))

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
        addInternalPlonkConstraint { vl: Just vl, cl, vr: Nothing, cr: zero, vo: Just vo, co: -one, m: zero, c }
        pure $ Tuple (Just vo) one
    Cons (Tuple vr cr) Nil -> do
      let Tuple vl cl = head
      vo <- createInternalVariable $ AffineExpression { constant, terms: [ Tuple vl cl, Tuple vr cr ] }
      addInternalPlonkConstraint { vl: Just vl, cl, vr: Just vr, cr, vo: Just vo, co: -one, m: zero, c: fromMaybe zero constant }
      pure $ Tuple (Just vo) one
    Cons head' tail' -> do
      Tuple vr cr <-
        foldM
          ( \(Tuple vr cr) (Tuple vl cl) -> do
              vo <- createInternalVariable $ AffineExpression { constant: Nothing, terms: [ Tuple vl cl, Tuple vr cr ] }
              addInternalPlonkConstraint { cl, vl: Just vl, cr, vr: Just vr, co: -one, vo: Just vo, m: zero, c: zero }
              pure $ Tuple vo one
          )
          head'
          tail'
      let Tuple vl cl = head
      vo <- createInternalVariable $ AffineExpression { constant, terms: [ Tuple vl cl, Tuple vr cr ] }
      addInternalPlonkConstraint { vl: Just vl, cl, vr: Just vr, cr, vo: Just vo, co: -one, m: zero, c: fromMaybe zero constant }
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
      addInternalPlonkConstraint { cl: one, vl: Just vl, cr: zero, vr: Nothing, co: zero, vo: Nothing, m: zero, c: (-c) }
      pure vl
    -- result is c * v
    Just v ->
      if c == one then pure v
      else do
        c_times_v <- createInternalVariable $ AffineExpression { constant: zero, terms: [ Tuple v c ] }
        -- c * v - c_times_v = 0
        addInternalPlonkConstraint { cl: c, vl: Just v, cr: zero, vr: Nothing, co: -one, vo: Just c_times_v, m: zero, c: zero }
        pure c_times_v

reduceAsBuilder
  :: forall f a
   . PrimeField f
  => { nextVariable :: Variable
     , wireState :: KimchiWireRow f
     }
  -> (forall m. PlonkReductionM m f => m a)
  -> Tuple
       a
       { nextVariable :: Variable
       , constraints :: Array (KimchiRow f)
       , wireState :: KimchiWireRow f
       }
reduceAsBuilder { nextVariable, wireState } m =
  let
    initState = BuilderReductionState { nextVariable, constraints: mempty, wireState }
    Tuple a (BuilderReductionState s) = runState (un PlonkBuilder m) initState
  in
    Tuple a s

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
  case runState (runExceptT $ un PlonkProver m) (ProverReductionState s) of
    Tuple (Left e) _ -> Left e
    Tuple (Right a) (ProverReductionState s') -> Right $ Tuple a s'

--------------------------------------------------------------------------------

newtype BuilderReductionState f = BuilderReductionState
  { constraints :: Array (KimchiRow f)
  , nextVariable :: Variable
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

-- Convert GenericPlonkConstraint to coefficient vector (columns for one gate)
-- Note: This is a simplified version - actual Kimchi gate coefficients would be more complex
constraintToCoeffs
  :: forall f
   . PrimeField f
  => GenericPlonkConstraint f
  -> Vector 5 f
constraintToCoeffs gate =
  gate.cl :< gate.cr :< gate.co :< gate.m :< gate.c :< Vector.nil

finalizeGateQueue
  :: forall f
   . PrimeField f
  => KimchiWireRow f
  -> Tuple (Maybe (KimchiRow f)) (KimchiWireRow f)
finalizeGateQueue wireState =
  case wireState.queuedGenericGate of
    Nothing ->
      -- No leftover gate, nothing to do
      Tuple Nothing wireState
    Just leftoverGate ->
      -- Single leftover gate gets its own row
      let
        -- row = wireState.nextRow
        gateCoeffs = constraintToCoeffs leftoverGate
        zeros = Vector.generate $ const zero :: Vector 10 f
        coeffRow = gateCoeffs `Vector.append` zeros
        kimchiRow =
          { kind: GenericPlonkGate
          , coeffs: coeffRow
          , variables: leftoverGate.vl :< leftoverGate.vr :< leftoverGate.vo :< Vector.generate (const Nothing)
          }
      in
        Tuple
          (Just kimchiRow)
          wireState
            { queuedGenericGate = Nothing
            }

handleGateBatching :: forall f. PrimeField f => GenericPlonkConstraint f -> PlonkBuilder f (Maybe (KimchiRow f))
handleGateBatching newGate = do
  BuilderReductionState s <- get
  case s.wireState.queuedGenericGate of
    Nothing -> do
      modify_ \(BuilderReductionState s') -> BuilderReductionState $ s'
        { wireState = s'.wireState { queuedGenericGate = Just newGate } }
      pure Nothing
    Just queuedGate -> do
      modify_ \(BuilderReductionState s') -> BuilderReductionState $ s'
        { wireState = s'.wireState
            { queuedGenericGate = Nothing
            }
        }
      pure $ Just $ doubleGateRow queuedGate newGate
  where
  doubleGateRow gate1 gate2 =
    let
      vars = gate1.vl :< gate1.vr :< gate1.vo :< gate2.vl :< gate2.vr :< gate2.vo :< Vector.generate (const Nothing)
      coeffs = constraintToCoeffs gate1
        `Vector.append` constraintToCoeffs gate2
        `Vector.append` Vector.generate (const zero)
    in
      { kind: GenericPlonkGate, coeffs, variables: vars }

instance PrimeField f => PlonkReductionM (PlonkBuilder f) f where
  addInternalPlonkConstraint c = do
    mRow <- handleGateBatching c
    for_ mRow \row ->
      modify_ \(BuilderReductionState s) -> BuilderReductionState s { constraints = s.constraints `Array.snoc` row }
  addGenericPlonkConstraint c = handleGateBatching c
  createInternalVariable _ = do
    BuilderReductionState { nextVariable } <- get
    modify_ \(BuilderReductionState s) -> BuilderReductionState
      s
        { nextVariable = incrementVariable nextVariable
        , wireState = s.wireState { internalVariables = Set.insert nextVariable s.wireState.internalVariables }
        }
    pure nextVariable

newtype ProverReductionState f = ProverReductionState
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
  addInternalPlonkConstraint _ = pure unit
  addGenericPlonkConstraint _ = pure Nothing
  createInternalVariable e = do
    ProverReductionState { nextVariable, assignments } <- get
    let
      _lookup v = case Map.lookup v assignments of
        Nothing -> throwError $ MissingVariable v
        Just a -> pure a
    a <- evalAffineExpression e _lookup
    modify_ \(ProverReductionState s) -> ProverReductionState $
      s
        { nextVariable = incrementVariable nextVariable
        , assignments = Map.insert nextVariable a assignments
        }
    pure nextVariable