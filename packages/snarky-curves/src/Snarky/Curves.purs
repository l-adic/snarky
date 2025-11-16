module Snarky.Circuit.Curves
  ( assertOnCurve
  , assertEqual
  , negate
  , lookupSingleBit
  ) where

import Prelude

import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, CVar, Variable, Bool)
import Snarky.Circuit.DSL as Snarky
import Snarky.Circuit.Curves.Types (AffinePoint(..), CurveParams(..))
import Snarky.Curves.Class (class PrimeField)

assertOnCurve
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => CurveParams (CVar f Variable)
  -> AffinePoint (CVar f Variable)
  -> t m Unit
assertOnCurve (CurveParams { a, b }) (AffinePoint { x, y }) = do
  x2 <- Snarky.square_ x
  x3 <- Snarky.mul_ x2 x
  ax <- Snarky.mul_ a x
  y2 <- Snarky.square_ y
  let x3_plus_ax = Snarky.add_ x3 ax
  let rhs = Snarky.add_ x3_plus_ax b
  Snarky.assertEqual y2 rhs

assertEqual
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => AffinePoint (CVar f Variable)
  -> AffinePoint (CVar f Variable)
  -> t m Unit
assertEqual (AffinePoint { x: x1, y: y1 }) (AffinePoint { x: x2, y: y2 }) = do
  Snarky.assertEqual x1 x2
  Snarky.assertEqual y1 y2

negate
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => AffinePoint (CVar f Variable)
  -> t m (AffinePoint (CVar f Variable))
negate (AffinePoint { x, y }) = do
  pure $ AffinePoint { x, y: Snarky.negate_ y }

lookupSingleBit
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => CVar f (Bool Variable)
  -> AffinePoint (CVar f Variable)
  -> AffinePoint (CVar f Variable)
  -> t m (AffinePoint (CVar f Variable))
lookupSingleBit b (AffinePoint { x: x1, y: y1 }) (AffinePoint { x: x2, y: y2 }) = do
  -- x = x1 + b * (x2 - x1)
  xTerm <- Snarky.mul_ (coerce b) (Snarky.sub_ x2 x1)
  let x = Snarky.add_ x1 xTerm
  -- y = y1 + b * (y2 - y1)  
  yTerm <- Snarky.mul_ (coerce b) (Snarky.sub_ y2 y1)
  let y = Snarky.add_ y1 yTerm
  pure $ AffinePoint { x, y }
