module Snarky.Data.EllipticCurve
  ( AffinePoint
  , genAffinePoint
  , Point(..)
  , addAffine
  , fromAffine
  , genPoint
  , mkPoint
  , toAffine
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..), fromJust, isJust)
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.Types (class CheckedType, class CircuitType, F(..), FVar, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve)
import Snarky.Curves.Class as Snarky.Curves.Class
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Type.Proxy (Proxy(..))

type CurveParams f = { a :: f, b :: f }

type AffinePoint f = { x :: f, y :: f }

genAffinePoint
  :: forall g f
   . Arbitrary f
  => Arbitrary g
  => WeierstrassCurve f g
  => Proxy g
  -> Gen (AffinePoint (F f))
genAffinePoint _ = do
  mp <- (Snarky.Curves.Class.toAffine @f @g <$> arbitrary) `suchThat` isJust
  let { x, y } = unsafePartial $ fromJust mp
  pure { x: F x, y: F y }

newtype Point f = Point { x :: f, y :: f, z :: f }

derive instance Generic (Point f) _

instance (Show f, PrimeField f) => Show (Point f) where
  show p = case toAffine p of
    Nothing -> show $ { x: zero @f, y: one @f, z: one @f }
    Just { x, y } -> show { x, y, z: one @f }

instance CircuitType f (Point (F f)) (Point (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields (Proxy @(Point (F f)))
  fieldsToVar = genericFieldsToVar (Proxy @(Point (F f)))

instance CheckedType (Point (FVar f)) (KimchiConstraint f) where
  check = genericCheck

genPoint
  :: forall f g
   . WeierstrassCurve f g
  => Arbitrary g
  => Proxy g
  -> Gen (Point (F f))
genPoint _ =
  arbitrary @g <#> \g ->
    case Snarky.Curves.Class.toAffine g of
      Just { x, y } -> Point { x: F x, y: F y, z: one }
      Nothing -> mempty

mkPoint
  :: forall f
   . PrimeField f
  => CurveParams f
  -> { x :: f
     , y :: f
     , z :: f
     }
  -> Maybe (Point f)
mkPoint { a, b } p@{ x, y, z }
  | z == zero && x == zero && y == one = Just mempty
  | z /= zero && y * y == x * x * x + a * x + b = Just (Point p)
  | otherwise = Nothing

toAffine :: forall f. PrimeField f => Point f -> Maybe (AffinePoint f)
toAffine (Point { x, y, z })
  | z == zero = Nothing
  | otherwise = Just { x: x / z, y: y / z }

fromAffine :: forall f. PrimeField f => AffinePoint f -> Point f
fromAffine { x, y } = Point { x, y, z: one }

instance PrimeField f => Eq (Point f) where
  eq (Point p1) (Point p2)
    | p1.z == zero && p2.z == zero = true
    | p1.z == zero && p2.z /= zero = false
    | p1.z /= zero && p2.z == zero = false
    | otherwise = (p1.x / p1.z) == (p2.x / p2.z) &&
        (p2.x / p2.z) == (p2.y / p2.z)

instance PrimeField f => Semigroup (Point f) where
  append (Point p1) (Point p2)
    | p1.z == zero = Point p2
    | p2.z == zero = Point p1
    | otherwise =
        addAffine
          { x: p1.x, y: p1.y }
          { x: p2.x, y: p2.y }

instance PrimeField f => Monoid (Point f) where
  mempty = Point { x: zero, y: one, z: zero }

addAffine
  :: forall f
   . PrimeField f
  => AffinePoint f
  -> AffinePoint f
  -> Point f
addAffine p1 p2 =
  if p1.x == p2.x && p1.y == negate p2.y then mempty
  else
    let
      { x, y } = unsafeAdd p1 p2
    in
      Point { x, y, z: one }
  where
  unsafeAdd { x: x1, y: y1 } { x: x2, y: y2 } =
    let
      lambda = (y2 - y1) / (x2 - x1)
      x3 = (lambda * lambda) - x1 - x2
      y3 = lambda * (x1 - x3) - y1
    in
      { x: x3, y: y3 }