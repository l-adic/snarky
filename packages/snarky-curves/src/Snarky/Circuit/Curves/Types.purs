module Snarky.Circuit.Curves.Types where

import Prelude

import Data.Maybe (fromJust, isJust)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.CVar (CVar)
import Snarky.Circuit.Types (Variable, FieldElem(..), class FieldEncoded, class ConstrainedType, valueToFields, fieldsToValue, sizeInFields, varToFields, fieldsToVar)
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve, toAffine)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Type.Proxy (Proxy(..))

newtype AffinePoint f = AffinePoint { x :: f, y :: f }

derive instance Eq f => Eq (AffinePoint f)
derive newtype instance Show f => Show (AffinePoint f)

genAffinePoint :: forall g f. Arbitrary g => WeierstrassCurve f g => Proxy g -> Gen (AffinePoint f)
genAffinePoint _ = AffinePoint <$> do
  let g = (toAffine @f @g <$> arbitrary) `suchThat` isJust
  g <#> \p ->
    unsafePartial $ fromJust p

newtype CurveParams f = CurveParams { a :: f, b :: f }

derive instance Eq f => Eq (CurveParams f)

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
