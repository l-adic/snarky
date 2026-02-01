module Snarky.Types.Shifted
  ( Type1(..)
  , Type2(..)
  , class Shifted
  , fromShifted
  , toShifted
  , splitField
  , joinField
  , fieldSizeBits
  , forbiddenShiftedValues
  , forbiddenType1Values
  , forbiddenType2Values
  ) where

import Prelude

import Data.Array as Array
import Data.Bifunctor (class Bifunctor)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Reflectable (reflectType)
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (unfoldr)
import JS.BigInt (BigInt, fromInt)
import JS.BigInt as BigInt
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, BoolVar, F(..), FVar, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, modulus, pow, toBigInt)
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

instance BasicSystem f c => CheckedType f c t m (Type2 (FVar f) (BoolVar f)) where
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

--------------------------------------------------------------------------------
-- Forbidden shifted values
--
-- When representing a scalar s from field F_r in a circuit over field F_p,
-- certain values are "forbidden" because they cause the shifted reconstruction
-- to produce 0 (or other edge cases).
--
-- For Type1: s = 2*t + 2^n + 1, forbidden when t ≡ -2^n - 1 (mod r) (gives s ≡ 0)
-- For Type2: s = 2*sDiv2 + sOdd + 2^n, forbidden when 2*sDiv2 + sOdd ≡ -2^n (mod r)
--
-- The function finds all n-bit values congruent to -2^n or -2^n - 1 modulo r.
--------------------------------------------------------------------------------

-- | Find all values that fit in `sizeInBits` bits and are congruent to
-- | `-2^sizeInBits` or `-2^sizeInBits - 1` modulo `r`.
-- |
-- | These are the "raw" forbidden values before converting to field representation.
forbiddenShiftedValues
  :: { modulus :: BigInt, sizeInBits :: Int }
  -> Array BigInt
forbiddenShiftedValues { modulus: r, sizeInBits } =
  let
    twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt sizeInBits)

    -- All n-bit values equivalent to x mod r
    representatives :: BigInt -> Array BigInt
    representatives x =
      let
        -- x mod r, but handle negative x (mod is from EuclideanRing)
        xModR = ((x `mod` r) + r) `mod` r
        -- Generate sequence: xModR, xModR + r, xModR + 2r, ... while < 2^n
        step cur =
          if cur < twoToN then Just (Tuple cur (cur + r))
          else Nothing
      in
        unfoldr step xModR

    -- -2^n and -2^n - 1
    negTwoToN = negate twoToN
    negTwoToNMinus1 = negTwoToN - BigInt.fromInt 1
  in
    Array.nub $ Array.sort $
      representatives negTwoToN <> representatives negTwoToNMinus1

-- | Forbidden values for Type1 representation.
-- | Returns field elements t where 2*t + 2^n + 1 ≡ 0 (mod scalarModulus).
-- |
-- | For the Vesta.ScalarField → Type1 (Vesta.BaseField) instance.
forbiddenType1Values :: Array (F Vesta.BaseField)
forbiddenType1Values =
  let
    scalarMod = modulus @Vesta.ScalarField
    sizeInBits = fieldSizeBits (Proxy @Vesta.ScalarField)
    circuitMod = modulus @Vesta.BaseField

    rawValues = forbiddenShiftedValues { modulus: scalarMod, sizeInBits }

    -- Filter to values that fit in the circuit field
    toCircuitField :: BigInt -> Maybe (F Vesta.BaseField)
    toCircuitField x =
      if x < circuitMod then Just (F (fromBigInt x))
      else Nothing
  in
    Array.mapMaybe toCircuitField rawValues

-- | Forbidden values for Type2 representation.
-- | Returns (sDiv2, sOdd) pairs where 2*sDiv2 + sOdd + 2^n ≡ 0 (mod scalarModulus).
-- |
-- | For the Pallas.ScalarField → Type2 (Pallas.BaseField) Boolean instance.
forbiddenType2Values :: Array { sDiv2 :: F Pallas.BaseField, sOdd :: Boolean }
forbiddenType2Values =
  let
    scalarMod = modulus @Pallas.ScalarField
    sizeInBits = fieldSizeBits (Proxy @Pallas.ScalarField)
    circuitMod = modulus @Pallas.BaseField

    rawValues = forbiddenShiftedValues { modulus: scalarMod, sizeInBits }

    -- Convert raw x to (sDiv2, sOdd) where x = 2*sDiv2 + sOdd
    toType2 :: BigInt -> Maybe { sDiv2 :: F Pallas.BaseField, sOdd :: Boolean }
    toType2 x =
      let
        sOdd = BigInt.odd x
        sDiv2BigInt = (x - (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)) / BigInt.fromInt 2
      in
        -- sDiv2 must fit in the circuit field
        if sDiv2BigInt < circuitMod then Just { sDiv2: F (fromBigInt sDiv2BigInt), sOdd }
        else Nothing
  in
    Array.mapMaybe toType2 rawValues
