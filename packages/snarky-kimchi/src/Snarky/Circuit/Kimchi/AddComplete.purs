module Snarky.Circuit.Kimchi.AddComplete where

import Prelude

import Control.Apply (lift2)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, addConstraint, exists, read, readCVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (fromInt)
import Snarky.Data.EllipticCurve (AffinePoint)

addComplete
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky (KimchiConstraint f) t m
       { p :: AffinePoint (FVar f)
       , isInfinity :: BoolVar f
       }
addComplete p1 p2 = do
  sameX <- exists $
    lift2 eq (readCVar p1.x) (readCVar p2.x)
  inf <- exists
    let
      sameY = lift2 eq (readCVar p1.y) (readCVar p2.y)
    in
      read sameX && not sameY
  infZ <- exists $
    lift2 eq (readCVar p1.y) (readCVar p2.y) >>=
      if _ then zero
      else
        read sameX >>=
          if _ then recip (readCVar p2.y - readCVar p1.y)
          else zero
  x21Inv <- exists $
    read sameX >>=
      if _ then zero
      else recip (readCVar p2.x - readCVar p1.x)
  s <- exists $
    read sameX >>=
      if _ then do
        x1 <- readCVar p1.x
        y1 <- readCVar p1.y
        pure $ (fromInt 3 * x1 * x1) / (fromInt 2 * y1)
      else
        (readCVar p2.y - readCVar p1.y) / (readCVar p2.x - readCVar p1.x)
  x3 <- exists
    let
      sVal = readCVar s
    in
      sVal * sVal - (readCVar p1.x + readCVar p2.x)
  y3 <- exists $
    readCVar s * (readCVar p1.x - readCVar x3) - readCVar p1.y
  addConstraint $ KimchiAddComplete
    { p1, p2, sameX: coerce sameX, inf: coerce inf, infZ, x21Inv, s, p3: { x: x3, y: y3 } }
  pure
    { p: { x: x3, y: y3 }
    , isInfinity: inf
    }