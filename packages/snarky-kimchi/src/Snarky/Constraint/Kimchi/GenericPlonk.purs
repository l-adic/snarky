module Snarky.Constraint.Kimchi.GenericPlonk
  ( eval
  , reduce
  ) where

import Prelude

import Data.Foldable (all)
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Exception (error)
import Effect.Exception.Unsafe (unsafeThrowException)
import Snarky.Circuit.CVar (Variable, reduceToAffineExpression)
import Snarky.Constraint.Basic (Basic(..))
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, reduceAffineExpression)
import Snarky.Constraint.Kimchi.Types (GenericPlonkConstraint)
import Snarky.Constraint.Kimchi.Wire (KimchiRow)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Fin (unsafeFinite)
import Snarky.Data.Vector ((!!))
import Snarky.Data.Vector as Vector

eval
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> KimchiRow f
  -> m Boolean
eval lookup x = ado
  variables <- traverse lookup' x.variables
  let
    { before: vars } = Vector.splitAt @6 variables
    { before: row0Vars, after: row1Vars } = Vector.splitAt @3 vars
    { before: coeffs } = Vector.splitAt @10 x.coeffs
    { before: row0Coeffs, after: row1Coeffs } = Vector.splitAt @5 coeffs
    finite5 = unsafeFinite @5
    finite3 = unsafeFinite @3

    f { vars, coeffs } =
      let
        cl = coeffs !! finite5 0
        cr = coeffs !! finite5 1
        co = coeffs !! finite5 2
        m = coeffs !! finite5 3
        c = coeffs !! finite5 4
        vl = vars !! finite3 0
        vr = vars !! finite3 1
        vo = vars !! finite3 2
      in
        cl * vl + cr * vr + co * vo + m * vl * vr + c == zero
  in
    all f
      [ { vars: row0Vars, coeffs: row0Coeffs }
      , { vars: row1Vars, coeffs: row1Coeffs }
      ]
  where
  lookup' = maybe (pure zero) lookup

reduce
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => Basic f
  -> m (Maybe (GenericPlonkConstraint f))
reduce g = case g of
  R1CS { left, right, output } -> do
    Tuple mvl cl <- reduceAffineExpression $ reduceToAffineExpression left
    Tuple mvr cr <- reduceAffineExpression $ reduceToAffineExpression right
    Tuple mvo co <- reduceAffineExpression $ reduceToAffineExpression output
    pure case mvl, mvr, mvo of
      -- (cl * vl) * (cr * vr) = (co * vo)
      Just vl, Just vr, Just vo ->
        Just { cl: zero, vl: Just vl, cr: zero, vr: Just vr, co, vo: Just vo, m: -(cl * cr), c: zero }
      -- (cl * vl) * (cr * vr) = co
      Just vl, Just vr, Nothing ->
        Just { cl: zero, vl: Just vl, cr: zero, vr: Just vr, co: zero, vo: Nothing, m: (cl * cr), c: -co }
      -- (cl * vl) * cr = (co * vo)
      Just vl, Nothing, Just vo ->
        Just { vl: Just vl, cl: cl * cr, vr: Nothing, cr: zero, vo: Just vo, co: -co, m: zero, c: zero }
      -- cl * (cr * vr) = (co * vo)
      Nothing, Just vr, Just vo ->
        Just { vl: Nothing, cl: zero, vr: Just vr, cr: cl * cr, vo: Just vo, co: -co, m: zero, c: zero }
      -- (cl * vl) cr = co
      Just vl, Nothing, Nothing ->
        Just { vl: Just vl, cl: cl * cr, vr: Nothing, cr: zero, vo: Nothing, co: zero, m: zero, c: -co }
      -- cl * (cr * vr) = co
      Nothing, Just vr, Nothing ->
        Just { vl: Nothing, cl: zero, vr: Just vr, cr: cl * cr, vo: Nothing, co: zero, m: zero, c: -co }
      -- cl * cr = (co * vo)
      Nothing, Nothing, Just vo ->
        Just { vl: Nothing, cl: zero, vr: Nothing, cr: zero, co, vo: Just vo, m: zero, c: -(cl * cr) }
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
        else Nothing
  Equal a b -> do
    Tuple mvl cl <- reduceAffineExpression $ reduceToAffineExpression a
    Tuple mvr cr <- reduceAffineExpression $ reduceToAffineExpression b
    pure case mvl, mvr of
      -- cl * vl = cr * vr
      Just vl, Just vr ->
        Just { vl: Just vl, cl, vr: Just vr, cr: -cr, co: zero, vo: Nothing, m: zero, c: zero }
      -- cl * vl = cr
      Just vl, Nothing ->
        Just { vl: Just vl, cl, vr: Nothing, cr: zero, co: zero, vo: Nothing, m: zero, c: -cr }
      -- cl = cr * vr
      Nothing, Just vr ->
        Just { vl: Nothing, cl: zero, vr: Just vr, cr: cr, co: zero, vo: Nothing, m: zero, c: -cl }
      Nothing, Nothing ->
        if (cl /= cr) then
          ( unsafeThrowException
              $ error
              $ "Contradiction while reducing equal to plonk gates: "
                  <> show cl
                  <> " /= "
                  <> show cr
          )
        else Nothing
  Boolean b -> do
    Tuple mv c <- reduceAffineExpression $ reduceToAffineExpression b
    pure case mv of
      Nothing ->
        if (c * c /= c) then
          ( unsafeThrowException
              $ error
              $ "Contradiction while reducing bool to plonk gates: "
                  <> show c
                  <> " /= "
                  <> "{0,1}"
          )
        else Nothing
      -- v * v = v
      Just v ->
        Just { vl: Just v, cl: -c, vr: Just v, cr: zero, co: zero, vo: Just v, m: c * c, c: zero }