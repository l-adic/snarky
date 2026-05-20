module Snarky.Constraint.Kimchi.AddComplete
  ( AddComplete
  , Rows
  , reduce
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Snarky.Circuit.DSL (FVar, Variable)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, reduceToVariable)
import Snarky.Constraint.Kimchi.Types (class ToKimchiRows, GateKind(..), KimchiRow)

type AddComplete f =
  { p1 :: { x :: FVar f, y :: FVar f }
  , p2 :: { x :: FVar f, y :: FVar f }
  , p3 :: { x :: FVar f, y :: FVar f }
  , inf :: FVar f
  , sameX :: FVar f
  , s :: FVar f
  , infZ :: FVar f
  , x21Inv :: FVar f
  }

newtype Rows f = Rows (KimchiRow f)

instance ToKimchiRows f (Rows f) where
  toKimchiRows (Rows as) = Array.singleton as

reduce
  :: forall f m
   . PlonkReductionM m f
  => AddComplete f
  -> m (Rows f)
reduce c = Rows <$> do
  p1 <- reduceAffinePoint c.p1
  p2 <- reduceAffinePoint c.p2
  p3 <- reduceAffinePoint c.p3
  -- OCaml evaluates the vars array literal right-to-left:
  -- x21_inv, inf_z, slope, same_x, inf
  x21Inv <- reduceToVariable c.x21Inv
  infZ <- reduceToVariable c.infZ
  s <- reduceToVariable c.s
  sameX <- reduceToVariable c.sameX
  inf <- reduceToVariable c.inf
  let
    variables :: Vector 15 (Maybe Variable)
    variables =
      Just p1.x :< Just p1.y :< Just p2.x :< Just p2.y :< Just p3.x
        :< Just p3.y
        :< Just inf
        :< Just sameX
        :< Just s
        :< Just infZ
        :< Just x21Inv
        :< Vector.generate (const Nothing)
  pure { kind: AddCompleteGate, coeffs: mempty, variables }

  where
  -- OCaml's reduce_curve_point (x, y) = (reduce_to_v x, reduce_to_v y)
  -- evaluates right-to-left: y first, then x. Combined with generic gate
  -- batching (new gate → first half, pending → second half), this produces
  -- [x | y] in the gate layout.
  reduceAffinePoint p = do
    y <- reduceToVariable p.y
    x <- reduceToVariable p.x
    pure { x, y }

