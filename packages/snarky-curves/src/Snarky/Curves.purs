module Snarky.Circuit.Curves
  ( assertOnCurve
  , assertEqual
  , negate
  , if_
  , unsafeAdd
  ) where

import Prelude

import Snarky.Circuit.Constraint.Class (r1cs)
import Snarky.Circuit.Curves.Types (AffinePoint(..), CurveParams(..))
import Snarky.Circuit.DSL (class CircuitM, Bool, CVar, FieldElem(..), UnChecked(..), Variable, assertSquare, exists, readCVar)
import Snarky.Circuit.DSL as Snarky
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
  => AffinePoint (CVar f Variable)
  -> AffinePoint (CVar f Variable)
  -> t m Unit
assertEqual (AffinePoint { x: x1, y: y1 }) (AffinePoint { x: x2, y: y2 }) = do
  Snarky.assertEqual x1 x2
  Snarky.assertEqual y1 y2

negate
  :: forall f c t m
   . CircuitM f c t m
  => AffinePoint (CVar f Variable)
  -> t m (AffinePoint (CVar f Variable))
negate (AffinePoint { x, y }) = do
  pure $ AffinePoint { x, y: Snarky.negate_ y }

if_
  :: forall f c t m
   . CircuitM f c t m
  => CVar f (Bool Variable)
  -> AffinePoint (CVar f Variable)
  -> AffinePoint (CVar f Variable)
  -> t m (AffinePoint (CVar f Variable))
if_ b (AffinePoint { x: x1, y: y1 }) (AffinePoint { x: x2, y: y2 }) = do
  x <- Snarky.if_ b x1 x2
  y <- Snarky.if_ b y1 y2
  pure $ AffinePoint { x, y }

-- N.B. This function is unsafe, the following scenerios will trigger bad behavior:
--   1. If the points are equal 
--   2. If the points are mutual inverses
unsafeAdd
  :: forall f c t m
   . Partial
  => CircuitM f c t m
  => AffinePoint (CVar f Variable)
  -> AffinePoint (CVar f Variable)
  -> t m (AffinePoint (CVar f Variable))
unsafeAdd (AffinePoint { x: ax, y: ay }) (AffinePoint { x: bx, y: by }) = do
  lambda <- Snarky.div_ (Snarky.sub_ by ay) (Snarky.sub_ bx ax)

  UnChecked cx <- exists do
    axVal <- readCVar ax
    bxVal <- readCVar bx
    lambdaVal <- readCVar lambda
    pure $ UnChecked $ FieldElem $ (lambdaVal * lambdaVal) - (axVal + bxVal)

  assertSquare lambda (Snarky.add_ (Snarky.add_ cx ax) bx)

  UnChecked cy <- exists do
    axVal <- readCVar ax
    ayVal <- readCVar ay
    cxVal <- readCVar cx
    lambdaVal <- readCVar lambda
    pure $ UnChecked $ FieldElem $ (lambdaVal * (axVal - cxVal)) - ayVal

  Snarky.addConstraint $ r1cs
    { left: lambda
    , right: Snarky.sub_ ax cx
    , output: Snarky.add_ cy ay
    }

  pure $ AffinePoint { x: cx, y: cy }