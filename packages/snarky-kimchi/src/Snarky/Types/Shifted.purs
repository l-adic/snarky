module Snarky.Types.Shifted
  ( Type1(..)
  , Type2(..)
  , class Shifted
  , fromShifted
  , toShifted
  , splitField
  , joinField
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import JS.BigInt (fromInt)
import JS.BigInt as BigInt
import Snarky.Circuit.Types (class CheckedType, class CircuitType, BoolVar, F(..), FVar, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class PrimeField, fromBigInt, pow, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

--------------------------------------------------------------------------------
-- Type1: Single field element with shift 2^n + 1
-- Used when the scalar field is smaller than or equal to the circuit field
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

-- | Shift constants for Type1: c = 2^255 + 1, scale = 1/2
shift1 :: forall f. PrimeField f => { c :: f, scale :: f }
shift1 =
  { c: fromBigInt (fromInt 2) `pow` (fromInt 255) + one
  , scale: recip (fromBigInt $ fromInt 2)
  }

--------------------------------------------------------------------------------
-- Shifted class: Unified interface for Type1 and Type2 shifted representations
--
-- Maps between scalar field values and their shifted circuit representations.
-- The functional dependencies ensure:
--   f -> sf: Each scalar field has exactly one shifted representation type
--   sf -> f: Each shifted type corresponds to exactly one scalar field
--
-- For Pallas circuit (circuit field = Pallas.BaseField):
--   - Scalar field: Pallas.ScalarField (= Vesta.BaseField), smaller
--   - Uses Type1 with shift transformation
--
-- For Vesta circuit (circuit field = Vesta.BaseField):
--   - Scalar field: Vesta.ScalarField (= Pallas.BaseField), larger
--   - Uses Type2 with split representation
--------------------------------------------------------------------------------

class Shifted f sf | f -> sf, sf -> f where
  toShifted :: f -> sf
  fromShifted :: sf -> f

-- | Type1 instance for Pallas circuit
-- | Scalar field: Pallas.ScalarField (= Vesta.BaseField)
-- | Circuit field: Pallas.BaseField
-- | Shift: t = (s - c) * scale, effective scalar = 2*t + 2^255 + 1
instance Shifted (F Pallas.ScalarField) (Type1 (F Pallas.BaseField)) where
  toShifted (F s) =
    let
      { c, scale } = shift1 :: { c :: Pallas.BaseField, scale :: Pallas.BaseField }

      -- Coerce from smaller (ScalarField) to larger (BaseField)
      sLarge :: Pallas.BaseField
      sLarge = fromBigInt (toBigInt s)
    in
      Type1 $ F $ (sLarge - c) * scale

  fromShifted (Type1 (F t)) =
    let
      -- Coerce t to smaller field, then do arithmetic there
      tSmall :: Pallas.ScalarField
      tSmall = fromBigInt (toBigInt t)
      { c, scale } = shift1 :: { c :: Pallas.ScalarField, scale :: Pallas.ScalarField }
    in
      F $ recip scale * tSmall + c

-- | Type2 instance for Vesta circuit
-- | Scalar field: Vesta.ScalarField (= Pallas.BaseField)
-- | Circuit field: Vesta.BaseField
-- | Split: s = 2*sDiv2 + sOdd, effective scalar = s + 2^255
instance Shifted (F Vesta.ScalarField) (Type2 (F Vesta.BaseField) Boolean) where
  toShifted (F s) =
    let
      sBigInt = toBigInt s
      sOdd = BigInt.odd sBigInt
      sDiv2 = (if sOdd then s - one else s) / fromBigInt (fromInt 2)

      -- sDiv2 is 254 bits, safe to coerce to smaller field
      sDiv2Small :: Vesta.BaseField
      sDiv2Small = fromBigInt (toBigInt sDiv2)
    in
      Type2 { sDiv2: F sDiv2Small, sOdd }

  fromShifted (Type2 { sDiv2: F d, sOdd }) =
    let
      -- Coerce sDiv2 to larger field FIRST, then do arithmetic there
      dLarge :: Vesta.ScalarField
      dLarge = fromBigInt (toBigInt d)
      -- Reconstruct original value in larger field
      sLarge = joinField { sDiv2: dLarge, sOdd }

      -- Effective scalar includes the 2^255 shift (computed in larger field)
      twoToThe255 :: Vesta.ScalarField
      twoToThe255 = fromBigInt (fromInt 2) `pow` fromInt 255
      effectiveScalar = sLarge + twoToThe255
    in
      F effectiveScalar

--------------------------------------------------------------------------------
-- Type2: Split representation (sDiv2, sOdd) where s = 2 * sDiv2 + sOdd
-- Used when the scalar field is larger than the circuit field (foreign field)
--
-- When computing [s]*G where s is from the larger field:
--   1. Split s into (sDiv2, sOdd) where s = 2*sDiv2 + sOdd
--   2. sDiv2 fits in 254 bits (one less than field size)
--   3. sOdd is a single bit (0 or 1)
--   4. scaleFast2 computes [s]*G = sOdd ? h : (h - G) where h = [2*sDiv2 + 1 + 2^n]*G
--------------------------------------------------------------------------------

-- | Type2 represents a scalar split into (sDiv2, sOdd) where s = 2*sDiv2 + sOdd
-- | f = field element type, b = boolean type
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

-- | Split a field element into Type2 representation where s = 2*sDiv2 + sOdd
-- | This is used when you have a circuit field value (e.g., a hash output)
-- | and need to compute the effective scalar for scaleFast2.
splitField :: forall f. PrimeField f => F f -> Type2 (F f) Boolean
splitField (F s) =
  let
    sBigInt = toBigInt s
    sOdd = BigInt.odd sBigInt
    sDiv2 = (if sOdd then s - one else s) / fromBigInt (fromInt 2)
  in
    Type2 { sDiv2: F sDiv2, sOdd }

-- | Join (sDiv2, sOdd) back into a field element: s = 2*sDiv2 + sOdd
joinField :: forall f. PrimeField f => { sDiv2 :: f, sOdd :: Boolean } -> f
joinField { sDiv2, sOdd } =
  let
    two = fromBigInt (fromInt 2)
  in
    two * sDiv2 + (if sOdd then one else zero)