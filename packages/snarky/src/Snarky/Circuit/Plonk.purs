module Snarky.Circuit.Plonk
  ( GenericPlonkConstraint
  , evalPlonkConstraint
  , reduceToPlonkGates
  , class PlonkReductionM
  , createInternalVariable
  , addGenericPlonkConstraint
  , reduceAsBuilder
  , reduceAsProver
  ) where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State (State, execState, get, modify_, runState)
import Data.Array as A
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Foldable (foldM, traverse_)
import Data.List.NonEmpty (fromFoldable)
import Data.List.Types (List(..), NonEmptyList(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.NonEmpty (NonEmpty(..))
import Data.Tuple (Tuple(..))
import Effect.Exception (error)
import Effect.Exception.Unsafe (unsafeThrowException)
import Snarky.Circuit.CVar (AffineExpression(..), EvaluationError(..), Variable, evalAffineExpression, incrementVariable, reduceToAffineExpression)
import Snarky.Circuit.Constraint (Basic(..))
import Snarky.Curves.Class (class PrimeField)

--------------------------------------------------------------------------------

type GenericPlonkConstraint f =
  { cl :: f
  , vl :: Variable
  , cr :: f
  , vr :: Variable
  , co :: f
  , vo :: Variable
  , m :: f
  , c :: f
  }

data PlonkConstraint f
  = PlonkGeneric (GenericPlonkConstraint f)

evalPlonkConstraint
  :: forall f m
   . PrimeField f
  => Monad m
  => (Variable -> m f)
  -> GenericPlonkConstraint f
  -> m Boolean
evalPlonkConstraint lookup x = do
  vl <- lookup x.vl
  vr <- lookup x.vr
  vo <- lookup x.vo
  pure $ x.cl * vl + x.cr * vr + x.co * vo + x.m * vl * vr + x.c == zero

class PlonkSystem f c | c -> f where
  plonk :: GenericPlonkConstraint f -> c

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

reduceToPlonkGates
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => Basic f
  -> m Unit
reduceToPlonkGates g = case g of
  R1CS { left, right, output } -> do
    Tuple mvl cl <- reduceAffineExpression $ reduceToAffineExpression left
    Tuple mvr cr <- reduceAffineExpression $ reduceToAffineExpression right
    Tuple mvo co <- reduceAffineExpression $ reduceToAffineExpression output
    case mvl, mvr, mvo of
      -- (cl * vl) * (cr * vr) = (co * vo)
      Just vl, Just vr, Just vo ->
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
      Nothing, Nothing, Nothing ->
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

newtype BuilderReductionState f = BuilderReductionState
  { constraints :: Array (GenericPlonkConstraint f)
  , nextVariable :: Variable
  }

instance PlonkReductionM (State (BuilderReductionState f)) f where
  addGenericPlonkConstraint c = modify_ \(BuilderReductionState s) -> BuilderReductionState $ s { constraints = s.constraints `A.snoc` c }
  createInternalVariable _ = do
    BuilderReductionState { nextVariable } <- get
    modify_ \(BuilderReductionState s) -> BuilderReductionState $ s { nextVariable = incrementVariable nextVariable }
    pure nextVariable

reduceAsBuilder
  :: forall f
   . PrimeField f
  => { nextVariable :: Variable
     , constraints :: Array (Basic f)
     }
  -> { nextVariable :: Variable
     , constraints :: Array (GenericPlonkConstraint f)
     }
reduceAsBuilder { nextVariable, constraints: cs } =
  let
    initState = BuilderReductionState { nextVariable, constraints: mempty }
    BuilderReductionState s = execState (traverse_ reduceToPlonkGates cs) initState
  in
    s

newtype ProverReductionState f = ProverReductionState
  { nextVariable :: Variable
  , assignments :: Map Variable f
  }

instance PrimeField f => PlonkReductionM (ExceptT (EvaluationError f) (State (ProverReductionState f))) f where
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
reduceAsProver cs s = case runState (runExceptT (traverse_ reduceToPlonkGates cs)) (ProverReductionState s) of
  Tuple (Left e) _ -> Left e
  Tuple (Right _) (ProverReductionState s') -> Right s'