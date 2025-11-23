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
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, UnChecked(..), addConstraint, add_, assertEqual_, assertSquare_, const_, div_, exists, mul_, negate_, pow_, readCVar, scale_, sub_)
import Snarky.Circuit.DSL as Snarky
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve, curveParams)
import Type.Proxy (Proxy)

assertOnCurve
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => CurveParams (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky t m Unit
assertOnCurve { a, b } { x, y } = do
  rhs <- (x `pow_` 3) + (a `mul_` x) + (pure b)
  y2 <- mul_ y y
  assertEqual_ y2 rhs

assertEqual
  :: forall f c t m
   . CircuitM f c t m
  => AffinePoint (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky t m Unit
assertEqual { x: x1, y: y1 } { x: x2, y: y2 } = do
  assertEqual_ x1 x2
  assertEqual_ y1 y2

negate
  :: forall f c t m
   . CircuitM f c t m
  => AffinePoint (FVar f)
  -> Snarky t m (AffinePoint (FVar f))
negate { x, y } = do
  pure { x, y: negate_ y }

if_
  :: forall f c t m
   . CircuitM f c t m
  => BoolVar f
  -> AffinePoint (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky t m (AffinePoint (FVar f))
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
  => AffinePoint (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky t m (AffinePoint (FVar f))
unsafeAdd { x: ax, y: ay } { x: bx, y: by } = do
  lambda <- div_ (sub_ by ay) (sub_ bx ax)

  UnChecked cx <- exists do
    axVal <- readCVar ax
    bxVal <- readCVar bx
    lambdaVal <- readCVar lambda
    pure $ UnChecked $ F $ (lambdaVal * lambdaVal) - (axVal + bxVal)

  assertSquare_ lambda (add_ (add_ cx ax) bx)

  UnChecked cy <- exists do
    axVal <- readCVar ax
    ayVal <- readCVar ay
    cxVal <- readCVar cx
    lambdaVal <- readCVar lambda
    pure $ UnChecked $ F $ (lambdaVal * (axVal - cxVal)) - ayVal

  addConstraint $ r1cs
    { left: lambda
    , right: sub_ ax cx
    , output: add_ cy ay
    }

  pure { x: cx, y: cy }

double
  :: forall f g c t m
   . CircuitM f c t m
  => PrimeField f
  => WeierstrassCurve f g
  => Proxy g
  -> AffinePoint (FVar f)
  -> Snarky t m (AffinePoint (FVar f))
double pg { x: ax, y: ay } = do
  xSquared <- mul_ ax ax

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
  let aConst = const_ a

  addConstraint $ r1cs
    { left: scale_ (one + one :: f) lambda
    , right: ay
    , output: add_ (scale_ (one + one + one :: f) xSquared) aConst -- 3*x² + a
    }

  assertSquare_ lambda (add_ bx (scale_ (one + one :: f) ax))

  addConstraint $ r1cs
    { left: lambda
    , right: sub_ ax bx
    , output: add_ by ay
    }

  pure { x: bx, y: by }