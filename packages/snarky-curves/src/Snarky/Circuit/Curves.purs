module Snarky.Circuit.Curves where

import Prelude

import Data.Maybe (fromJust, isJust)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.CVar (CVar, add_)
import Snarky.Circuit.DSL (class CircuitM)
import Snarky.Circuit.DSL.Assert (assertEqual)
import Snarky.Circuit.DSL.Field (mul_, square_)
import Snarky.Circuit.Types (Variable, FieldElem(..), class FieldEncoded, class ConstrainedType, valueToFields, fieldsToValue, sizeInFields, varToFields, fieldsToVar)
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve, toAffine)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Type.Proxy (Proxy(..))

newtype AffinePoint f = AffinePoint { x :: f, y :: f }

genAffinePoint :: forall g f. Arbitrary g => WeierstrassCurve f g => Proxy g -> Gen (AffinePoint f)
genAffinePoint _ = AffinePoint <$> do
  let g = (toAffine @f @g <$> arbitrary) `suchThat` isJust
  g <#> \p ->
    unsafePartial $ fromJust p

newtype CurveParams f = CurveParams { a :: f, b :: f }

instance PrimeField f => FieldEncoded f (AffinePoint f) where
  valueToFields (AffinePoint { x, y }) = valueToFields (Tuple (FieldElem x) (FieldElem (y)))
  fieldsToValue fs =
    let
      (Tuple (FieldElem x) (FieldElem y)) = fieldsToValue fs
    in
      AffinePoint { x, y }
  sizeInFields _ = sizeInFields @f (Proxy :: Proxy (Tuple (FieldElem f) (FieldElem f)))

instance PrimeField f => ConstrainedType f (AffinePoint f) c (AffinePoint (CVar f Variable)) where
  varToFields (AffinePoint { x, y }) =
    varToFields @f @(Tuple (FieldElem f) (FieldElem f)) (Tuple x y)
  fieldsToVar vs =
    let
      (Tuple x y) = fieldsToVar @f @(Tuple (FieldElem f) (FieldElem f)) vs
    in
      AffinePoint { x, y }
  check _ = mempty

instance PrimeField f => FieldEncoded f (CurveParams f) where
  valueToFields (CurveParams { a, b }) = valueToFields (Tuple (FieldElem a) (FieldElem b))
  fieldsToValue fs =
    let
      (Tuple (FieldElem a) (FieldElem b)) = fieldsToValue fs
    in
      CurveParams { a, b }
  sizeInFields _ = sizeInFields @f (Proxy :: Proxy (Tuple (FieldElem f) (FieldElem f)))

instance PrimeField f => ConstrainedType f (CurveParams f) c (CurveParams (CVar f Variable)) where
  varToFields (CurveParams { a, b }) =
    varToFields @f @(Tuple (FieldElem f) (FieldElem f)) (Tuple a b)
  fieldsToVar vs =
    let
      (Tuple a b) = fieldsToVar @f @(Tuple (FieldElem f) (FieldElem f)) vs
    in
      CurveParams { a, b }
  check _ = mempty

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