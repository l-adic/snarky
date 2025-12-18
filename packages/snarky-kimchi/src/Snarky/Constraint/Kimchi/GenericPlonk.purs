module Snarky.Constraint.Kimchi.GenericPlonk
  ( GenericPlonkConstraint
  , eval
  , class PlonkReductionM
  , createInternalVariable
  , addGenericPlonkConstraint
  , reduceBasic
  ) where

import Prelude

import Data.Bifunctor (lmap)
import Data.Foldable (foldM)
import Data.List.NonEmpty (fromFoldable)
import Data.List.Types (List(..), NonEmptyList(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.NonEmpty (NonEmpty(..))
import Data.Tuple (Tuple(..))
import Effect.Exception (error)
import Effect.Exception.Unsafe (unsafeThrowException)
import Snarky.Circuit.CVar (AffineExpression(..), Variable, reduceToAffineExpression)
import Snarky.Constraint.Basic (Basic(..))
import Snarky.Curves.Class (class PrimeField)


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

eval
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> GenericPlonkConstraint f
  -> m Boolean
eval lookup x = ado
  vl <- lookup x.vl
  vr <- lookup x.vr
  vo <- lookup x.vo
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