module Snarky.Types.Shifted
  ( Type1(..)
  , Type2(..)
  , class Shifted
  , fromShifted
  , toShifted
  , splitField
  , joinField
  , fieldSizeBits
  ) where

import Prelude

import Data.Bifunctor (class Bifunctor)
import Data.Generic.Rep (class Generic)
import Data.Reflectable (reflectType)
import Data.Show.Generic (genericShow)
import JS.BigInt (fromInt)
import JS.BigInt as BigInt
import Snarky.Circuit.Types (class CheckedType, class CircuitType, BoolVar, F(..), FVar, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, pow, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Type1: Single field element with shift 2^n + 1 (n = field size in bits)
-- Used when scalar field < circuit field
--------------------------------------------------------------------------------

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

fieldSizeBits :: forall f n. FieldSizeInBits f n => Proxy f -> Int
fieldSizeBits _ = reflectType (Proxy :: Proxy n)

shift1 :: forall f n. FieldSizeInBits f n => Proxy f -> { c :: f, scale :: f }
shift1 _ =
  let
    n = reflectType (Proxy :: Proxy n)
  in
    { c: fromBigInt (fromInt 2) `pow` (fromInt n) + one
    , scale: recip (fromBigInt $ fromInt 2)
    }

toShifted1 :: forall f n. FieldSizeInBits f n => Proxy f -> F f -> Type1 (F f)
toShifted1 p (F s) =
  let
    { c, scale } = shift1 p
  in
    Type1 $ F $ (s - c) * scale

fromShifted1 :: forall f n. FieldSizeInBits f n => Proxy f -> Type1 (F f) -> F f
fromShifted1 p (Type1 (F t)) =
  let
    { c, scale } = shift1 p
  in
    F $ recip scale * t + c

toShifted2 :: forall f n. FieldSizeInBits f n => Proxy f -> F f -> Type2 (F f) Boolean
toShifted2 _ (F s) =
  let
    sBigInt = toBigInt s
    sOdd = BigInt.odd sBigInt
    sDiv2 = (if sOdd then s - one else s) / fromBigInt (fromInt 2)
  in
    Type2 { sDiv2: F sDiv2, sOdd }

fromShifted2 :: forall f n. FieldSizeInBits f n => Proxy f -> Type2 (F f) Boolean -> F f
fromShifted2 _ (Type2 { sDiv2: F d, sOdd }) =
  let
    n = fieldSizeBits (Proxy :: Proxy f)
    dBigInt = toBigInt d
    sBigInt = BigInt.fromInt 2 * dBigInt + (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)
    twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    effectiveScalar = sBigInt + twoToN
  in
    F $ fromBigInt effectiveScalar

--------------------------------------------------------------------------------
-- Type2: Split representation (sDiv2, sOdd) where s = 2 * sDiv2 + sOdd
-- Used when scalar field > circuit field
--------------------------------------------------------------------------------

newtype Type2 f b = Type2 { sDiv2 :: f, sOdd :: b }

derive instance (Eq f, Eq b) => Eq (Type2 f b)
derive instance Generic (Type2 f b) _

instance (Show f, Show b) => Show (Type2 f b) where
  show x = genericShow x

instance PrimeField f => CircuitType f (Type2 (F f) Boolean) (Type2 (FVar f) (BoolVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(Type2 (F f) Boolean)
  fieldsToVar = genericFieldsToVar @(Type2 (F f) Boolean)

instance BasicSystem f c => CheckedType (Type2 (FVar f) (BoolVar f)) c where
  check = genericCheck

instance Bifunctor Type2 where
  bimap f g (Type2 x) = Type2 { sDiv2: f x.sDiv2, sOdd: g x.sOdd }

--------------------------------------------------------------------------------
-- Shifted class
--
-- Type1: t = (s - 2^n - 1) / 2, so s = 2*t + 2^n + 1
-- Type2: s split into (sDiv2, sOdd) where s = 2*sDiv2 + sOdd + 2^n
--------------------------------------------------------------------------------

class Shifted f sf where
  toShifted :: f -> sf
  fromShifted :: sf -> f

-- Type1 instances

instance Shifted (F Vesta.ScalarField) (Type1 (F Vesta.ScalarField)) where
  toShifted = toShifted1 (Proxy :: Proxy Vesta.ScalarField)
  fromShifted = fromShifted1 (Proxy :: Proxy Vesta.ScalarField)

instance Shifted (F Vesta.BaseField) (Type1 (F Vesta.BaseField)) where
  toShifted = toShifted1 (Proxy :: Proxy Vesta.BaseField)
  fromShifted = fromShifted1 (Proxy :: Proxy Vesta.BaseField)

instance Shifted (F Vesta.ScalarField) (Type1 (F Vesta.BaseField)) where
  toShifted (F s) =
    let
      { c, scale } = shift1 (Proxy :: Proxy Vesta.ScalarField)

      t_scalar :: Vesta.ScalarField
      t_scalar = (s - c) * scale
    in
      Type1 $ F $ fromBigInt (toBigInt t_scalar)
  fromShifted (Type1 (F t)) =
    let
      n = fieldSizeBits (Proxy :: Proxy Vesta.BaseField)
      tBigInt = toBigInt t
      twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    in
      F $ fromBigInt (BigInt.fromInt 2 * tBigInt + twoToN + BigInt.fromInt 1)

-- Type2 instances

instance Shifted (F Vesta.ScalarField) (Type2 (F Vesta.ScalarField) Boolean) where
  toShifted = toShifted2 (Proxy :: Proxy Vesta.ScalarField)
  fromShifted = fromShifted2 (Proxy :: Proxy Vesta.ScalarField)

instance Shifted (F Vesta.BaseField) (Type2 (F Vesta.BaseField) Boolean) where
  toShifted = toShifted2 (Proxy :: Proxy Vesta.BaseField)
  fromShifted = fromShifted2 (Proxy :: Proxy Vesta.BaseField)

-- Cross-field Type2: scalar field → Type2 in circuit field (via BigInt)
instance Shifted (F Pallas.ScalarField) (Type2 (F Pallas.BaseField) Boolean) where
  toShifted (F s) =
    let
      sBigInt = toBigInt s
      sOdd = BigInt.odd sBigInt

      sDiv2 :: Pallas.BaseField
      sDiv2 = fromBigInt $ (sBigInt - (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)) / BigInt.fromInt 2
    in
      Type2 { sDiv2: F sDiv2, sOdd }
  fromShifted (Type2 { sDiv2: F d, sOdd }) =
    let
      n = fieldSizeBits (Proxy :: Proxy Pallas.BaseField)
      dBigInt = toBigInt d
      sBigInt = BigInt.fromInt 2 * dBigInt + (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)
      twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    in
      F $ fromBigInt (sBigInt + twoToN)

instance Shifted (F Vesta.ScalarField) (Type2 (F Vesta.BaseField) Boolean) where
  toShifted (F s) =
    let
      sBigInt = toBigInt s
      sOdd = BigInt.odd sBigInt

      sDiv2 :: Vesta.BaseField
      sDiv2 = fromBigInt $ (sBigInt - (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)) / BigInt.fromInt 2
    in
      Type2 { sDiv2: F sDiv2, sOdd }
  fromShifted (Type2 { sDiv2: F d, sOdd }) =
    let
      n = fieldSizeBits (Proxy :: Proxy Vesta.BaseField)
      dBigInt = toBigInt d
      sBigInt = BigInt.fromInt 2 * dBigInt + (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)
      twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    in
      F $ fromBigInt (sBigInt + twoToN)

--------------------------------------------------------------------------------
-- Utility functions
--------------------------------------------------------------------------------

splitField :: forall f. PrimeField f => F f -> Type2 (F f) Boolean
splitField (F s) =
  let
    sBigInt = toBigInt s
    sOdd = BigInt.odd sBigInt
    sDiv2 = (if sOdd then s - one else s) / fromBigInt (fromInt 2)
  in
    Type2 { sDiv2: F sDiv2, sOdd }

joinField :: forall f. PrimeField f => { sDiv2 :: f, sOdd :: Boolean } -> f
joinField { sDiv2, sOdd } =
  let
    two = fromBigInt (fromInt 2)
  in
    two * sDiv2 + (if sOdd then one else zero)
