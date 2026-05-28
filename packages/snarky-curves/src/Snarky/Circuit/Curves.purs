module Snarky.Circuit.Curves
  ( add_
  , assertOnCurve
  , double
  , negate
  ) where

import Prelude

import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, UnChecked(..), addConstraint, assertEqual_, assertSquare_, const_, div_, exists, mul_, negate_, pow_, r1cs, readCVar, scale_, square_, sub_)
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
-- | Mirror of OCaml `Snarky_curves.Make_weierstrass_checked.double`
-- | (`snarky_curves.ml:277-313`). Uses `square_` for `x²` (Square
-- | gate) — NOT `mul_ ax ax` (R1CS gate). Constraint emission order
-- | matches OCaml byte-for-byte:
-- |   1. `square ax` (Square gate, x² alloc)
-- |   2. `assert_r1cs (2λ) ay (3x² + a)` (R1CS gate)
-- |   3. `assert_square λ (bx + 2ax)` (Square gate)
-- |   4. `assert_r1cs λ (ax - bx) (by + ay)` (R1CS gate)
double { a } { x: ax, y: ay } = do
  xSquared <- square_ ax

  lambda <- exists do
    xSquaredVal <- readCVar xSquared
    ayVal <- readCVar ay
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