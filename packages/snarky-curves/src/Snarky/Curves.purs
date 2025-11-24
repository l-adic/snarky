module Snarky.Circuit.Curves
  ( assertOnCurve
  , assertEqual
  , negate
  , if_
  , add_
  , double
  , addComplete
  ) where

import Prelude

import Control.Apply (lift2)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar)
import Snarky.Circuit.Constraint.Class (r1cs)
import Snarky.Circuit.Curves.Constraint (class ECSystem, ecAddComplete)
import Snarky.Circuit.Curves.Types (AffinePoint, CurveParams, Point)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, UnChecked(..), addConstraint, assertEqual_, assertSquare_, const_, div_, exists, mul_, negate_, not_, pow_, read, readCVar, scale_, sub_)
import Snarky.Circuit.DSL as Snarky
import Snarky.Circuit.Types (Variable(..))
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve, curveParams, fromInt)
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
add_
  :: forall f c t m
   . Partial
  => CircuitM f c t m
  => AffinePoint (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky t m (AffinePoint (FVar f))
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
    pure $ (xSquaredVal + xSquaredVal + xSquaredVal + F a) / (ayVal + ayVal)

  UnChecked bx <- exists do
    lambdaVal <- readCVar lambda
    axVal <- readCVar ax
    pure $ UnChecked $ (lambdaVal * lambdaVal) - (axVal + axVal)

  UnChecked by <- exists do
    lambdaVal <- readCVar lambda
    axVal <- readCVar ax
    ayVal <- readCVar ay
    bxVal <- readCVar bx
    pure $ UnChecked $ (lambdaVal * (axVal - bxVal)) - ayVal

  let { a } = curveParams pg
  let aConst = const_ a

  addConstraint $ r1cs
    { left: scale_ (fromInt 2) lambda
    , right: ay
    , output: Snarky.add_ (scale_ (fromInt 3) xSquared) aConst
    }

  assertSquare_ lambda (Snarky.add_ bx (scale_ (fromInt 2) ax))

  addConstraint $ r1cs
    { left: lambda
    , right: sub_ ax bx
    , output: Snarky.add_ by ay
    }

  pure { x: bx, y: by }

seal
  :: forall f c t m
   . CircuitM f c t m
  => AffinePoint (FVar f)
  -> Snarky t m (AffinePoint (FVar f))
seal { x, y } = do
  x' <- Snarky.seal x
  y' <- Snarky.seal y
  pure { x: x', y: y' }

addComplete
  :: forall f c t m
   . CircuitM f c t m
  => ECSystem (CVar f Variable) c
  => AffinePoint (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky t m (Point (FVar f))
addComplete _p1 _p2 = do
  p1 <- seal _p1
  p2 <- seal _p2
  sameX <- exists $
    lift2 eq (readCVar p1.x) (readCVar p2.x)
  inf <- exists do
    sameY <- lift2 eq (readCVar p1.y) (readCVar p2.y)
    read sameX && pure (not sameY)
  infZ <- exists do
    lift2 eq (readCVar p1.y) (readCVar p2.y) >>=
      if _ then zero
      else
        read sameX >>=
          if _ then recip (readCVar p2.y - readCVar p1.y)
          else zero
  x21Inv <- exists do
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
  x3 <- exists do
    sVal <- readCVar s
    pure (sVal * sVal) - (readCVar p1.x + readCVar p2.x)
  y3 <- exists do
    sVal <- readCVar s
    pure sVal * (readCVar p1.x - readCVar x3) - readCVar p1.y
  addConstraint $ ecAddComplete
    { p1, p2, sameX: coerce sameX, inf: coerce inf, infZ, x21Inv, s, p3: { x: x3, y: y3 } }
  pure { x: x3, y: y3, z: coerce (not_ inf) }