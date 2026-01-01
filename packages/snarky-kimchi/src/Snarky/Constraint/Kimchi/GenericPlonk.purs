module Snarky.Constraint.Kimchi.GenericPlonk
  ( class GenericPlonkVerifiable
  , verifyGenericPlonk
  , reduce
  , eval
  ) where

import Prelude

import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Exception (error)
import Effect.Exception.Unsafe (unsafeThrowException)
import Snarky.Circuit.CVar (Variable, reduceToAffineExpression)
import Snarky.Constraint.Basic (Basic(..))
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, addGenericPlonkConstraint, reduceAffineExpression, Rows, getRows)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Vector (Vector)

class GenericPlonkVerifiable f where
  verifyGenericPlonk :: { coeffs :: Vector 15 f, variables :: Vector 15 f } -> Boolean

eval
  :: forall f m
   . PrimeField f
  => Applicative m
  => GenericPlonkVerifiable f
  => (Variable -> m f)
  -> Rows f
  -> m Boolean
eval lookup rows = ado
  variables <- traverse lookup' x.variables
  in verifyGenericPlonk { variables, coeffs: x.coeffs }
  where
  x = getRows rows
  lookup' = maybe (pure zero) lookup

reduce
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => Basic f
  -> m Unit
reduce = case _ of
  R1CS { left, right, output } -> do
    Tuple mvl cl <- reduceAffineExpression $ reduceToAffineExpression left
    Tuple mvr cr <- reduceAffineExpression $ reduceToAffineExpression right
    Tuple mvo co <- reduceAffineExpression $ reduceToAffineExpression output
    case mvl, mvr, mvo of
      -- (cl * vl) * (cr * vr) = (co * vo)
      Just vl, Just vr, Just vo -> do
        addGenericPlonkConstraint { cl: zero, vl: Just vl, cr: zero, vr: Just vr, co, vo: Just vo, m: -(cl * cr), c: zero }
      -- (cl * vl) * (cr * vr) = co
      Just vl, Just vr, Nothing -> do
        addGenericPlonkConstraint { cl: zero, vl: Just vl, cr: zero, vr: Just vr, co: zero, vo: Nothing, m: (cl * cr), c: -co }
      -- (cl * vl) * cr = (co * vo)
      Just vl, Nothing, Just vo -> do
        addGenericPlonkConstraint { vl: Just vl, cl: cl * cr, vr: Nothing, cr: zero, vo: Just vo, co: -co, m: zero, c: zero }
      -- cl * (cr * vr) = (co * vo)
      Nothing, Just vr, Just vo -> do
        addGenericPlonkConstraint { vl: Nothing, cl: zero, vr: Just vr, cr: cl * cr, vo: Just vo, co: -co, m: zero, c: zero }
      -- (cl * vl) cr = co
      Just vl, Nothing, Nothing -> do
        addGenericPlonkConstraint { vl: Just vl, cl: cl * cr, vr: Nothing, cr: zero, vo: Nothing, co: zero, m: zero, c: -co }
      -- cl * (cr * vr) = co
      Nothing, Just vr, Nothing -> do
        addGenericPlonkConstraint { vl: Nothing, cl: zero, vr: Just vr, cr: cl * cr, vo: Nothing, co: zero, m: zero, c: -co }
      -- cl * cr = (co * vo)
      Nothing, Nothing, Just vo -> do
        addGenericPlonkConstraint { vl: Nothing, cl: zero, vr: Nothing, cr: zero, co, vo: Just vo, m: zero, c: -(cl * cr) }
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
        addGenericPlonkConstraint { vl: Just vl, cl, vr: Just vr, cr: -cr, co: zero, vo: Nothing, m: zero, c: zero }
      -- cl * vl = cr
      Just vl, Nothing -> do
        addGenericPlonkConstraint { vl: Just vl, cl, vr: Nothing, cr: zero, co: zero, vo: Nothing, m: zero, c: -cr }
      -- cl = cr * vr
      Nothing, Just vr -> do
        addGenericPlonkConstraint { vl: Nothing, cl: zero, vr: Just vr, cr: cr, co: zero, vo: Nothing, m: zero, c: -cl }
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
        addGenericPlonkConstraint { vl: Just v, cl: -c, vr: Just v, cr: zero, co: zero, vo: Just v, m: c * c, c: zero }

foreign import verifyPallasGeneric :: Vector 15 Pallas.ScalarField -> Vector 15 Pallas.ScalarField -> Boolean

foreign import verifyVestaGeneric :: Vector 15 Vesta.ScalarField -> Vector 15 Vesta.ScalarField -> Boolean

instance GenericPlonkVerifiable Pallas.ScalarField where
  verifyGenericPlonk { coeffs, variables } = verifyPallasGeneric coeffs variables

instance GenericPlonkVerifiable Vesta.ScalarField where
  verifyGenericPlonk { coeffs, variables } = verifyVestaGeneric coeffs variables
