module Snarky.Constraint.Kimchi.GenericPlonk
  ( eval
  , class PlonkReductionM
  , createInternalVariable
  , addGenericPlonkConstraint
  , reduceBasic
  , reduceAsBuilder
  , reduceAsProver
  , finalizeGateQueue
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.State (class MonadState, State, execState, get, modify_, runState)
import Data.Array as A
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Foldable (foldM, traverse_)
import Data.List.NonEmpty (fromFoldable)
import Data.List.Types (List(..), NonEmptyList(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust, fromMaybe)
import Data.Newtype (class Newtype, un)
import Data.NonEmpty (NonEmpty(..))
import Data.Tuple (Tuple(..))
import Effect.Exception (error)
import Effect.Exception.Unsafe (unsafeThrowException)
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.CVar (AffineExpression(..), EvaluationError(..), Variable, evalAffineExpression, incrementVariable, reduceToAffineExpression)
import Snarky.Constraint.Basic (Basic(..))
import Snarky.Constraint.Kimchi.Types (GenericPlonkConstraint)
import Snarky.Constraint.Kimchi.Wire (GateKind(..), KimchiWireRow)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector
import Type.Proxy (Proxy(..))

eval
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> GenericPlonkConstraint f
  -> m Boolean
eval lookup x = ado
  vl <- if x.cl == zero && x.m == zero then pure zero else lookup x.vl
  vr <- if x.cr == zero && x.m == zero then pure zero else lookup x.vr
  vo <- if x.co == zero then pure zero else lookup x.vo
  in x.cl * vl + x.cr * vr + x.co * vo + x.m * vl * vr + x.c == zero

class Monad m <= PlonkReductionM m f | m -> f where
  createInternalVariable
    :: AffineExpression f
    -> m Variable
  addGenericPlonkConstraint
    :: GenericPlonkConstraint f
    -> m Unit

freshUnconstrainedVariable
  :: forall m f
   . PlonkReductionM m f
  => m Variable
freshUnconstrainedVariable =
  createInternalVariable $ AffineExpression { constant: Nothing, terms: mempty }

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
        vr <- freshUnconstrainedVariable
        let Tuple vl cl = head
        addGenericPlonkConstraint { vl, cl, vr, cr: zero, vo, co: -one, m: zero, c }
        pure $ Tuple (Just vo) one
    Cons (Tuple vr cr) Nil -> do
      let Tuple vl cl = head
      vo <- createInternalVariable $ AffineExpression { constant, terms: [ Tuple vl cl, Tuple vr cr ] }
      addGenericPlonkConstraint { vl, cl, vr, cr, vo, co: -one, m: zero, c: fromMaybe zero constant }
      pure $ Tuple (Just vo) one
    Cons head' tail' -> do
      Tuple vr cr <-
        foldM
          ( \(Tuple vr cr) (Tuple vl cl) -> do
              vo <- createInternalVariable $ AffineExpression { constant: Nothing, terms: [ Tuple vl cl, Tuple vr cr ] }
              addGenericPlonkConstraint { cl, vl, cr, vr, co: -one, vo, m: zero, c: zero }
              pure $ Tuple vo one
          )
          head'
          tail'
      let Tuple vl cl = head
      vo <- createInternalVariable $ AffineExpression { constant, terms: [ Tuple vl cl, Tuple vr cr ] }
      addGenericPlonkConstraint { vl, cl, vr, cr, vo, co: -one, m: zero, c: fromMaybe zero constant }
      pure $ Tuple (Just vo) one

reduceBasic
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => Basic f
  -> m Unit
reduceBasic g = case g of
  R1CS { left, right, output } -> do
    Tuple mvl cl <- reduceAffineExpression $ reduceToAffineExpression left
    Tuple mvr cr <- reduceAffineExpression $ reduceToAffineExpression right
    Tuple mvo co <- reduceAffineExpression $ reduceToAffineExpression output
    case mvl, mvr, mvo of
      -- (cl * vl) * (cr * vr) = (co * vo)
      Just vl, Just vr, Just vo -> do
        addGenericPlonkConstraint { cl: zero, vl, cr: zero, vr, co, vo, m: -(cl * cr), c: zero }
      -- (cl * vl) * (cr * vr) = co
      Just vl, Just vr, Nothing -> do
        vo <- freshUnconstrainedVariable
        addGenericPlonkConstraint { cl: zero, vl, cr: zero, vr, co: zero, vo, m: (cl * cr), c: -co }
      -- (cl * vl) * cr = (co * vo)
      Just vl, Nothing, Just vo -> do
        vr <- freshUnconstrainedVariable
        addGenericPlonkConstraint { vl, cl: cl * cr, vr, cr: zero, vo, co: -co, m: zero, c: zero }
      -- cl * (cr * vr) = (co * vo)
      Nothing, Just vr, Just vo -> do
        vl <- freshUnconstrainedVariable
        addGenericPlonkConstraint { vl, cl: zero, vr, cr: cl * cr, vo, co: -co, m: zero, c: zero }
      -- (cl * vl) cr = co
      Just vl, Nothing, Nothing -> do
        vr <- freshUnconstrainedVariable
        vo <- freshUnconstrainedVariable
        addGenericPlonkConstraint { vl, cl: cl * cr, vr, cr: zero, vo, co: zero, m: zero, c: -co }
      -- cl * (cr * vr) = co
      Nothing, Just vr, Nothing -> do
        vl <- freshUnconstrainedVariable
        vo <- freshUnconstrainedVariable
        addGenericPlonkConstraint { vl, cl: zero, vr, cr: cl * cr, vo, co: zero, m: zero, c: -co }
      -- cl * cr = (co * vo)
      Nothing, Nothing, Just vo -> do
        vl <- freshUnconstrainedVariable
        vr <- freshUnconstrainedVariable
        addGenericPlonkConstraint { vl, cl: zero, vr, cr: zero, co, vo, m: zero, c: -(cl * cr) }
      -- cl * cr = co
      Nothing, Nothing, Nothing -> do
        if ((cl * cr) /= co) then
          ( unsafeThrowException
              $ error
              $ "Contradiction while reducing r1cs to plonk gates: "
                  <> show (cl * cr)
                  <> " /= "
                  <> show co
          )
        else pure unit
  Equal a b -> do
    Tuple mvl cl <- reduceAffineExpression $ reduceToAffineExpression a
    Tuple mvr cr <- reduceAffineExpression $ reduceToAffineExpression b
    case mvl, mvr of
      -- cl * vl = cr * vr
      Just vl, Just vr -> do
        vo <- freshUnconstrainedVariable
        addGenericPlonkConstraint { vl, cl, vr, cr: -cr, co: zero, vo, m: zero, c: zero }
      -- cl * vl = cr
      Just vl, Nothing -> do
        vr <- freshUnconstrainedVariable
        vo <- freshUnconstrainedVariable
        addGenericPlonkConstraint { vl, cl, vr, cr: zero, co: zero, vo, m: zero, c: -cr }
      -- cl = cr * vr
      Nothing, Just vr -> do
        vl <- freshUnconstrainedVariable
        vo <- freshUnconstrainedVariable
        addGenericPlonkConstraint { vl, cl: zero, vr, cr: cr, co: zero, vo, m: zero, c: -cl }
      Nothing, Nothing ->
        if (cl /= cr) then
          ( unsafeThrowException
              $ error
              $ "Contradiction while reducing equal to plonk gates: "
                  <> show cl
                  <> " /= "
                  <> show cr
          )
        else pure unit
  Boolean b -> do
    Tuple mv c <- reduceAffineExpression $ reduceToAffineExpression b
    case mv of
      Nothing ->
        if (c * c /= c) then
          ( unsafeThrowException
              $ error
              $ "Contradiction while reducing bool to plonk gates: "
                  <> show c
                  <> " /= "
                  <> "{0,1}"
          )
        else pure unit
      -- v * v = v
      Just v -> do
        addGenericPlonkConstraint { vl: v, cl: -c, vr: v, cr: zero, co: zero, vo: v, m: c * c, c: zero }

reduceAsBuilder
  :: forall f
   . PrimeField f
  => { nextVariable :: Variable
     , constraints :: Array (Basic f)
     , wireState :: KimchiWireRow f
     }
  -> { nextVariable :: Variable
     , constraints :: Array (GenericPlonkConstraint f)
     , wireState :: KimchiWireRow f
     }
reduceAsBuilder { nextVariable, constraints: cs, wireState } =
  let
    initState = BuilderReductionState { nextVariable, constraints: mempty, wireState }
    BuilderReductionState s = execState (un PlonkBuilder (traverse_ reduceBasic cs)) initState
  in
    s

reduceAsProver
  :: forall f
   . PrimeField f
  => Array (Basic f)
  -> { nextVariable :: Variable
     , assignments :: Map Variable f
     }
  -> Either
       (EvaluationError f)
       { nextVariable :: Variable
       , assignments :: Map Variable f
       }
reduceAsProver cs s =
  case runState (runExceptT $ un PlonkProver (traverse_ (reduceBasic) cs)) (ProverReductionState s) of
    Tuple (Left e) _ -> Left e
    Tuple (Right _) (ProverReductionState s') -> Right s'

--------------------------------------------------------------------------------

newtype BuilderReductionState f = BuilderReductionState
  { constraints :: Array (GenericPlonkConstraint f)
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

-- Wire a variable at specific matrix position
wireVariableAt :: forall f. Variable -> Int -> Int -> PlonkBuilder f Unit
wireVariableAt var row col = do
  modify_ \(BuilderReductionState s) -> BuilderReductionState $ s
    { wireState = s.wireState
        { wireAssignments = Map.insert var (Tuple row col) s.wireState.wireAssignments }
    }

-- Convert GenericPlonkConstraint to coefficient vector (columns for one gate)
-- Note: This is a simplified version - actual Kimchi gate coefficients would be more complex
constraintToCoeffs :: forall f. PrimeField f => GenericPlonkConstraint f -> Vector 5 f
constraintToCoeffs gate = unsafePartial $ fromJust $
  Vector.toVector (Proxy @5) [ gate.cl, gate.cr, gate.co, gate.m, gate.c ]

-- Emit complete coefficient row for two GenericPlonk gates
emitDoubleGateRow :: forall f. PrimeField f => GenericPlonkConstraint f -> GenericPlonkConstraint f -> Int -> PlonkBuilder f Unit
emitDoubleGateRow gate1 gate2 row = do
  -- Wire variables to matrix positions
  wireVariableAt gate1.vl row 0
  wireVariableAt gate1.vr row 1
  wireVariableAt gate1.vo row 2
  wireVariableAt gate2.vl row 3
  wireVariableAt gate2.vr row 4
  wireVariableAt gate2.vo row 5

  let gate1Coeffs = constraintToCoeffs gate1
  let gate2Coeffs = constraintToCoeffs gate2
  let zeros = Vector.generate (const zero)
  let coeffRow = gate1Coeffs `Vector.append` gate2Coeffs `Vector.append` zeros

  -- Emit the complete row
  let kimchiRow = { kind: GenericPlonkGate, coeffs: coeffRow }
  modify_ \(BuilderReductionState s) -> BuilderReductionState $ s
    { wireState = s.wireState
        { emittedRows = s.wireState.emittedRows `A.snoc` kimchiRow }
    }

-- Handle gate batching and wire placement for GenericPlonk gates
handleGateBatching :: forall f. PrimeField f => GenericPlonkConstraint f -> PlonkBuilder f Unit
handleGateBatching newGate = do
  BuilderReductionState s <- get
  case s.wireState.queuedGenericGate of
    Nothing ->
      -- No queued gate, store this one for batching
      modify_ \(BuilderReductionState s') -> BuilderReductionState $ s'
        { wireState = s'.wireState { queuedGenericGate = Just newGate } }
    Just queuedGate -> do
      -- Have queued gate, emit row with both gates
      let row = s.wireState.nextRow
      emitDoubleGateRow queuedGate newGate row

      -- Advance to next row and clear queue
      modify_ \(BuilderReductionState s') -> BuilderReductionState $ s'
        { wireState = s'.wireState
            { nextRow = s'.wireState.nextRow + 1
            , queuedGenericGate = Nothing
            }
        }

-- Finalize gate queue - handle any leftover gate that didn't get paired
finalizeGateQueue :: forall f. PrimeField f => KimchiWireRow f -> KimchiWireRow f
finalizeGateQueue wireState =
  case wireState.queuedGenericGate of
    Nothing ->
      -- No leftover gate, nothing to do
      wireState
    Just leftoverGate ->
      -- Single leftover gate gets its own row
      let
        row = wireState.nextRow
        gateCoeffs = constraintToCoeffs leftoverGate
        zeros = Vector.generate $ const zero :: Vector 10 f
        coeffRow = gateCoeffs `Vector.append` zeros
        kimchiRow = { kind: GenericPlonkGate, coeffs: coeffRow }
      in
        wireState
          { nextRow = wireState.nextRow + 1
          , queuedGenericGate = Nothing
          , emittedRows = wireState.emittedRows `A.snoc` kimchiRow
          , wireAssignments = wireState.wireAssignments
              # Map.insert leftoverGate.vl (Tuple row 0)
              # Map.insert leftoverGate.vr (Tuple row 1)
              # Map.insert leftoverGate.vo (Tuple row 2)
          }

instance PrimeField f => PlonkReductionM (PlonkBuilder f) f where
  addGenericPlonkConstraint c = do
    modify_ \(BuilderReductionState s) -> BuilderReductionState $ s { constraints = s.constraints `A.snoc` c }
    handleGateBatching c
  createInternalVariable _ = do
    BuilderReductionState { nextVariable } <- get
    modify_ \(BuilderReductionState s) -> BuilderReductionState $ s { nextVariable = incrementVariable nextVariable }
    pure nextVariable

newtype ProverReductionState f = ProverReductionState
  { nextVariable :: Variable
  , assignments :: Map Variable f
  }

newtype PlonkProver f a = PlonkProver (ExceptT (EvaluationError f) (State (ProverReductionState f)) a)

derive newtype instance Functor (PlonkProver f)
derive newtype instance Apply (PlonkProver f)
derive newtype instance Applicative (PlonkProver f)
derive newtype instance Bind (PlonkProver f)
derive newtype instance Monad (PlonkProver f)
derive newtype instance MonadState (ProverReductionState f) (PlonkProver f)
derive newtype instance MonadThrow (EvaluationError f) (PlonkProver f)

derive instance Newtype (PlonkProver f a) _

instance (PrimeField f) => PlonkReductionM (PlonkProver f) f where
  addGenericPlonkConstraint _ = pure unit
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