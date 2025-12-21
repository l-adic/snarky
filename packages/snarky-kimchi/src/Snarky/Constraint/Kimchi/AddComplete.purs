module Snarky.Constraint.Kimchi.AddComplete
  ( AddComplete
  , eval
  , reduceAddComplete
  ) where

import Prelude

import Data.Foldable (and)
import Data.Maybe (Maybe(..))
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, addRow, reduceToVariable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..))
import Snarky.Curves.Class (class PrimeField, fromInt)
import Snarky.Data.Vector (Vector, (:<))
import Snarky.Data.Vector as Vector

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

eval
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> AddComplete f
  -> m Boolean
eval lookup c = ado
  x1 <- CVar.eval lookup c.p1.x
  y1 <- CVar.eval lookup c.p1.y
  x2 <- CVar.eval lookup c.p2.x
  y2 <- CVar.eval lookup c.p2.y
  x3 <- CVar.eval lookup c.p3.x
  y3 <- CVar.eval lookup c.p3.y
  inf <- CVar.eval lookup c.inf
  sameX <- CVar.eval lookup c.sameX
  s <- CVar.eval lookup c.s
  infZ <- CVar.eval lookup c.infZ
  x21Inv <- CVar.eval lookup c.x21Inv
  let
    c1 =
      if x1 == x2 then sameX == one
      else sameX == zero
    c2 =
      if sameX == one then fromInt 2 * s * y1 == fromInt 3 * x1 * x1
      else (x2 - x1) * s == y2 - y1
    c3 = s * s == x1 + x2 + x3
    c4 = y3 == s * (x1 - x3) - y1
    c5 =
      let
        notSameY = if y1 /= y2 then one else zero
      in
        inf == sameX * notSameY
    c6 =
      if y1 == y2 then infZ == zero
      else
        let
          a =
            if sameX == one then recip $ y2 - y1
            else zero
        in
          infZ == a
    c7 =
      if x1 == x2 then x21Inv == zero
      else x21Inv == recip (x2 - x1)
  in and [ c1, c2, c3, c4, c5, c6, c7 ]

reduceAddComplete
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => AddComplete f
  -> m Unit
reduceAddComplete c = do
  p1 <- reduceAffinePoint c.p1
  p2 <- reduceAffinePoint c.p2
  p3 <- reduceAffinePoint c.p3
  inf <- reduceToVariable c.inf
  sameX <- reduceToVariable c.sameX
  s <- reduceToVariable c.s
  infZ <- reduceToVariable c.infZ
  x21Inv <- reduceToVariable c.x21Inv
  let
    vars :: Vector 15 (Maybe Variable)
    vars =
      Just p1.x :< Just p1.y :< Just p2.x :< Just p2.y :< Just p3.x
        :< Just p3.y
        :< Just inf
        :< Just sameX
        :< Just s
        :< Just infZ
        :< Just x21Inv
        :< Vector.generate (const Nothing)
  addRow vars { kind: AddCompleteGate, coeffs: Vector.generate zero }

  where
  reduceAffinePoint p = do
    x <- reduceToVariable p.x
    y <- reduceToVariable p.y
    pure { x, y }
