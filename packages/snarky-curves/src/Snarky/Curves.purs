module Snarky.Circuit.Curves
  ( assertOnCurve
  , assertEqual
  , negate
  , if_
  , unsafeAdd
  , double
  ) where

import Prelude

import Snarky.Circuit.Constraint.Class (r1cs)
import Snarky.Circuit.Curves.Types (AffinePoint, CurveParams)
import Snarky.Circuit.DSL (class CircuitM, Bool, CVar, F(..), UnChecked(..), Variable, assertSquare, exists, readCVar, addConstraint)
import Snarky.Circuit.DSL as Snarky
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve, curveParams)
import Type.Proxy (Proxy)

assertOnCurve
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => CurveParams (CVar f Variable)
  -> AffinePoint (CVar f Variable)
  -> t m Unit
assertOnCurve { a, b } { x, y } = do
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
assertEqual { x: x1, y: y1 } { x: x2, y: y2 } = do
  Snarky.assertEqual x1 x2
  Snarky.assertEqual y1 y2

negate
  :: forall f c t m
   . CircuitM f c t m
  => AffinePoint (CVar f Variable)
  -> t m (AffinePoint (CVar f Variable))
negate { x, y } = do
  pure { x, y: Snarky.negate_ y }

if_
  :: forall f c t m
   . CircuitM f c t m
  => CVar f (Bool Variable)
  -> AffinePoint (CVar f Variable)
  -> AffinePoint (CVar f Variable)
  -> t m (AffinePoint (CVar f Variable))
if_ b { x: x1, y: y1 } { x: x2, y: y2 } = do
  x <- Snarky.if_ b x1 x2
  y <- Snarky.if_ b y1 y2
  pure { x, y }

-- N.B. This function is unsafe, if the x value is the same for both points
-- bad things can happen, i.e.
--   1. If the points are equal 
--   2. If the points are mutual inverses
unsafeAdd
  :: forall f c t m
   . Partial
  => CircuitM f c t m
  => AffinePoint (CVar f Variable)
  -> AffinePoint (CVar f Variable)
  -> t m (AffinePoint (CVar f Variable))
unsafeAdd { x: ax, y: ay } { x: bx, y: by } = do
  lambda <- Snarky.div_ (Snarky.sub_ by ay) (Snarky.sub_ bx ax)

  UnChecked cx <- exists do
    axVal <- readCVar ax
    bxVal <- readCVar bx
    lambdaVal <- readCVar lambda
    pure $ UnChecked $ F $ (lambdaVal * lambdaVal) - (axVal + bxVal)

  assertSquare lambda (Snarky.add_ (Snarky.add_ cx ax) bx)

  UnChecked cy <- exists do
    axVal <- readCVar ax
    ayVal <- readCVar ay
    cxVal <- readCVar cx
    lambdaVal <- readCVar lambda
    pure $ UnChecked $ F $ (lambdaVal * (axVal - cxVal)) - ayVal

  Snarky.addConstraint $ r1cs
    { left: lambda
    , right: Snarky.sub_ ax cx
    , output: Snarky.add_ cy ay
    }

  pure { x: cx, y: cy }

double
  :: forall f g c t m
   . CircuitM f c t m
  => PrimeField f
  => WeierstrassCurve f g
  => Proxy g
  -> AffinePoint (CVar f Variable)
  -> t m (AffinePoint (CVar f Variable))
double pg { x: ax, y: ay } = do
  xSquared <- Snarky.square_ ax

  lambda <- exists do
    xSquaredVal <- readCVar xSquared
    ayVal <- readCVar ay
    let { a } = curveParams pg
    pure $ F $ (xSquaredVal + xSquaredVal + xSquaredVal + a) / (ayVal + ayVal)

  UnChecked bx <- exists do
    lambdaVal <- readCVar lambda
    axVal <- readCVar ax
    pure $ UnChecked $ F $ (lambdaVal * lambdaVal) - (axVal + axVal)

  UnChecked by <- exists do
    lambdaVal <- readCVar lambda
    axVal <- readCVar ax
    ayVal <- readCVar ay
    bxVal <- readCVar bx
    pure $ UnChecked $ F $ (lambdaVal * (axVal - bxVal)) - ayVal

  let { a } = curveParams pg
  let aConst = Snarky.const_ a

  addConstraint $ r1cs
    { left: Snarky.scale_ (one + one :: f) lambda -- lambda * 2
    , right: ay
    , output: Snarky.add_ (Snarky.scale_ (one + one + one :: f) xSquared) aConst -- 3*x² + a
    }

  assertSquare lambda (Snarky.add_ bx (Snarky.scale_ (one + one :: f) ax))

  addConstraint $ r1cs
    { left: lambda
    , right: Snarky.sub_ ax bx
    , output: Snarky.add_ by ay
    }

  pure { x: bx, y: by }