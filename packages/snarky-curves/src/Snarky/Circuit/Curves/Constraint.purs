module Snarky.Circuit.Curves.Constraint where

import Prelude

import Data.Foldable (and)
import Snarky.Circuit.CVar (CVar, Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Curves.Types (AffinePoint)
import Snarky.Curves.Class (class PrimeField, fromInt)

type AddComplete f =
  { p1 :: AffinePoint (CVar f Variable)
  , p2 :: AffinePoint (CVar f Variable)
  , p3 :: AffinePoint (CVar f Variable)
  , inf :: (CVar f Variable)
  , sameX :: (CVar f Variable)
  , s :: (CVar f Variable)
  , infZ :: (CVar f Variable)
  , x21Inv :: (CVar f Variable)
  }

data ECConstraint f = ECAddComplete (AddComplete f)

class ECSystem f c | c -> f where
  ecAddComplete :: AddComplete f -> c

instance ECSystem f (ECConstraint f) where
  ecAddComplete = ECAddComplete

evalECConstraint
  :: forall f m
   . PrimeField f
  => Monad m
  => (Variable -> m f)
  -> ECConstraint f
  -> m Boolean
evalECConstraint lookup gate = do
  case gate of
    ECAddComplete c -> do
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
      pure $ and [ c1, c2, c3, c4, c5, c6, c7 ]