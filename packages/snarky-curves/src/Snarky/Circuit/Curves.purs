module Snarky.Circuit.Curves
  ( add_
  , assertOnCurve
  , double
  , negate
  ) where

import Prelude

import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, UnChecked(..), addConstraint, assertEqual_, assertSquare_, const_, div_, exists, mul_, negate_, pow_, r1cs, readCVar, scale_, sub_)
import Snarky.Circuit.DSL as Snarky
import Snarky.Curves.Class (class PrimeField, fromInt)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)

assertOnCurve
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => CurveParams (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky c t m Unit
assertOnCurve { a, b } { x, y } = do
  rhs <- (x `pow_` 3) + (a `mul_` x) + (pure b)
  y2 <- mul_ y y
  assertEqual_ y2 rhs

negate
  :: forall f c t m
   . CircuitM f c t m
  => AffinePoint (FVar f)
  -> Snarky c t m (AffinePoint (FVar f))
negate { x, y } = do
  pure { x, y: negate_ y }

-- N.B. This function is unsafe, if the x value is the same for both points
-- bad things can happen, i.e.
--   1. If the points are equal 
--   2. If the points are mutual inverses
add_
  :: forall f c t m
   . Partial
  => CircuitM f c t m
  => AffinePoint (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky c t m (AffinePoint (FVar f))
add_ { x: ax, y: ay } { x: bx, y: by } = do
  lambda <- div_ (sub_ by ay) (sub_ bx ax)

  UnChecked cx <- exists do
    axVal <- readCVar ax
    bxVal <- readCVar bx
    lambdaVal <- readCVar lambda
    pure $ UnChecked $ (lambdaVal * lambdaVal) - (axVal + bxVal)

  assertSquare_ lambda (Snarky.add_ (Snarky.add_ cx ax) bx)

  UnChecked cy <- exists do
    axVal <- readCVar ax
    ayVal <- readCVar ay
    cxVal <- readCVar cx
    lambdaVal <- readCVar lambda
    pure $ UnChecked $ (lambdaVal * (axVal - cxVal)) - ayVal

  addConstraint $ r1cs
    { left: lambda
    , right: sub_ ax cx
    , output: Snarky.add_ cy ay
    }

  pure { x: cx, y: cy }

double
  :: forall f c t m
   . CircuitM f c t m
  => PrimeField f
  => CurveParams f
  -> AffinePoint (FVar f)
  -> Snarky c t m (AffinePoint (FVar f))
double { a } { x: ax, y: ay } = do
  xSquared <- mul_ ax ax

  lambda <- exists do
    xSquaredVal <- readCVar xSquared
    ayVal <- readCVar ay
    pure $ (xSquaredVal + xSquaredVal + xSquaredVal + F a) / (ayVal + ayVal)

  UnChecked bx <- exists do
    lambdaVal <- readCVar lambda
    axVal <- readCVar ax
    pure $ UnChecked $ (lambdaVal * lambdaVal) - (axVal + axVal)

  assertSquare_ lambda (Snarky.add_ bx (scale_ (fromInt 2) ax))

  UnChecked by <- exists do
    lambdaVal <- readCVar lambda
    axVal <- readCVar ax
    ayVal <- readCVar ay
    bxVal <- readCVar bx
    pure $ UnChecked $ (lambdaVal * (axVal - bxVal)) - ayVal

  let aConst = const_ a

  addConstraint $ r1cs
    { left: scale_ (fromInt 2) lambda
    , right: ay
    , output: Snarky.add_ (scale_ (fromInt 3) xSquared) aConst
    }

  addConstraint $ r1cs
    { left: lambda
    , right: sub_ ax bx
    , output: Snarky.add_ by ay
    }

  pure { x: bx, y: by }