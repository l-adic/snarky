module Snarky.Types.Shifted
  ( Type1(..)
  , Type2(..)
  , class Shifted
  , fromShifted
  , toShifted
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Reflectable (reflectType)
import Data.Show.Generic (genericShow)
import JS.BigInt (fromInt)
import Snarky.Circuit.Types (class CircuitType, F(..), FVar, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, pow)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Type.Proxy (Proxy(..))

newtype Type1 f = Type1 f

derive instance Functor Type1
derive instance Eq f => Eq (Type1 f)
derive instance Generic (Type1 f) _

instance Show f => Show (Type1 f) where
  show x = genericShow x

instance CircuitType f (Type1 (F f)) (Type1 (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(Type1 (F f))
  fieldsToVar = genericFieldsToVar @(Type1 (F f))

shift1 :: forall f. PrimeField f => Int -> { c :: f, scale :: f }
shift1 fieldSizeInBits =
  { c: fromBigInt (fromInt 2) `pow` (fromInt fieldSizeInBits) + one
  , scale: recip (fromBigInt $ fromInt 2)
  }

newtype Type2 f = Type2 f

derive instance Functor Type2
derive instance Eq f => Eq (Type2 f)
derive instance Generic (Type2 f) _

instance Show f => Show (Type2 f) where
  show x = genericShow x

instance CircuitType f (Type2 (F f)) (Type2 (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(Type2 (F f))
  fieldsToVar = genericFieldsToVar @(Type2 (F f))

shift2 :: forall f. PrimeField f => Int -> { shift :: f }
shift2 fieldSizeInBits =
  { shift: (fromBigInt $ fromInt 2) `pow` (fromInt fieldSizeInBits) }

class Shifted (t :: Type -> Type) f where
  toShifted :: F f -> t (F f)
  fromShifted :: t (F f) -> F f

instance FieldSizeInBits Vesta.ScalarField n => Shifted Type1 Vesta.ScalarField where
  toShifted (F s) =
    let
      shift = shift1 (reflectType $ Proxy @n)
    in
      Type1 $ F $ (s - shift.c) * shift.scale

  fromShifted (Type1 (F t)) =
    let
      shift = shift1 (reflectType $ Proxy @n)
    in
      F $ recip shift.scale * t + shift.c

instance FieldSizeInBits Pallas.ScalarField n => Shifted Type2 Pallas.ScalarField where
  toShifted (F s) =
    let
      { shift } = shift2 (reflectType $ Proxy @n)
    in
      Type2 $ F $ (s - shift)

  fromShifted (Type2 (F t)) =
    let
      { shift } = shift2 (reflectType $ Proxy @n)
    in
      F $ t + shift