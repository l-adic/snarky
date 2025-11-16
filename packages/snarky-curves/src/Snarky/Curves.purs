module Snarky.Circuit.Curves
  ( assertOnCurve
  ) where

import Prelude

import Snarky.Circuit.CVar (CVar, add_)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.DSL.Assert (assertEqual)
import Snarky.Circuit.DSL.Field (mul_, square_)
import Snarky.Circuit.Types (Variable)
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
  x2 <- square_ x
  x3 <- mul_ x2 x
  ax <- mul_ a x
  y2 <- square_ y
  let x3_plus_ax = add_ x3 ax
  let rhs = add_ x3_plus_ax b
  assertEqual y2 rhs