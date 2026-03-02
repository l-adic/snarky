module Snarky.Types.Shifted
  ( Type1(..)
  , Type2(..)
  , class Shifted
  , fromShifted
  , toShifted
  , fieldSizeBits
  , forbiddenShiftedValues
  , forbiddenType1Values
  , forbiddenType2Values
  , forbiddenType2SameFieldValues
  , fromShiftedType1Circuit
  , ofFieldType1Circuit
  , shiftedEqualType1
  , fromShiftedType2Circuit
  , shiftedEqualType2
  ) where

import Prelude

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Reflectable (reflectType)
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (unfoldr)
import JS.BigInt (BigInt, fromInt)
import JS.BigInt as BigInt
import Snarky.Circuit.DSL (class CheckedType, class CircuitM, class CircuitType, BoolVar, F(..), FVar, Snarky, add_, any_, assert_, const_, equals_, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, not_, scale_, sub_)
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

-- | Check that a Type1 value is not one of the forbidden shifted values.
-- | This is specialized for the Vesta cross-field case (Wrap circuit).
instance CheckedType Vesta.BaseField c (Type1 (FVar Vesta.BaseField)) where
  check (Type1 t) = do
    -- For each forbidden value, check if t equals it
    -- Then assert that NONE of them match
    let forbiddenConstants = map (\(F f) -> const_ f) forbiddenType1Values
    matchesForbidden <- traverse (equals_ t) forbiddenConstants
    anyMatch <- any_ matchesForbidden
    assert_ (not_ anyMatch)

-- | CheckedType instance for Step circuit (runs on Vesta.ScalarField = Pallas.BaseField).
-- | Type1 values here represent Pallas.ScalarField values shifted into the larger field.
-- | Since Pallas.ScalarField < Vesta.ScalarField, all values are valid (no forbidden values).
-- |
-- | Note: This also covers Pallas.ScalarField (= Vesta.BaseField) for the Wrap circuit,
-- | since Vesta.ScalarField < Pallas.ScalarField means no forbidden values either.
instance CheckedType Vesta.ScalarField c (Type1 (FVar Vesta.ScalarField)) where
  check _ = pure unit

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
-- Type2: Single field element with shift 2^n (n = field size in bits)
-- Used when scalar field > circuit field
-- Matches OCaml's Shifted_value.Type2.t = Shifted_value of 'f
--------------------------------------------------------------------------------

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

-- | Check that a Type2 value is not one of the forbidden shifted values.
-- | This is specialized for the Pallas cross-field case.
instance CheckedType Pallas.BaseField c (Type2 (FVar Pallas.BaseField)) where
  check (Type2 t) = do
    let forbiddenConstants = map (\(F f) -> const_ f) forbiddenType2Values
    matchesForbidden <- traverse (equals_ t) forbiddenConstants
    anyMatch <- any_ matchesForbidden
    assert_ (not_ anyMatch)

-- | Same-field CheckedType for Pallas.ScalarField (Fq circuit).
-- | When shifting a field element within its own field, forbidden values still exist
-- | (where t + 2^n ≡ 0 mod field modulus).
instance CheckedType Pallas.ScalarField c (Type2 (FVar Pallas.ScalarField)) where
  check (Type2 t) = do
    let forbiddenConstants = map (\(F f) -> const_ f) forbiddenType2SameFieldValues
    matchesForbidden <- traverse (equals_ t) forbiddenConstants
    anyMatch <- any_ matchesForbidden
    assert_ (not_ anyMatch)

--------------------------------------------------------------------------------
-- SplitField: Parity decomposition s = 2 * sDiv2 + sOdd (NO shift)
--
-- Structurally identical to Type2, but semantically different:
-- Type2 represents a *shifted* value: fromShifted (Type2 {sDiv2, sOdd}) = 2*sDiv2 + sOdd + 2^n
-- SplitField is just a parity split: joinField {sDiv2, sOdd} = 2*sDiv2 + sOdd
--
-- Used by scaleFast2' which takes a raw field element, splits it, then delegates
-- to scaleFast2 (which internally adds the 2^n shift via varBaseMul).
--------------------------------------------------------------------------------

newtype SplitField f b = SplitField { sDiv2 :: f, sOdd :: b }

derive instance (Eq f, Eq b) => Eq (SplitField f b)
derive instance Generic (SplitField f b) _

instance (Show f, Show b) => Show (SplitField f b) where
  show x = genericShow x

instance PrimeField f => CircuitType f (SplitField (F f) Boolean) (SplitField (FVar f) (BoolVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(SplitField (F f) Boolean)
  fieldsToVar = genericFieldsToVar @(SplitField (F f) Boolean)

-- | CheckedType for SplitField: just verify sOdd is boolean (no forbidden value checks needed).
-- | Since SplitField represents s = 2*sDiv2 + sOdd (no shift), there are no forbidden values.
-- | Note: Pallas.BaseField = Vesta.ScalarField and Pallas.ScalarField = Vesta.BaseField,
-- | so two instances cover all four Pasta fields.
instance CheckedType Pallas.BaseField c (SplitField (FVar Pallas.BaseField) (BoolVar Pallas.BaseField)) where
  check = genericCheck

instance CheckedType Pallas.ScalarField c (SplitField (FVar Pallas.ScalarField) (BoolVar Pallas.ScalarField)) where
  check = genericCheck

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

-- Same-field Type1: Step circuit stores Wrap-field scalars shifted into its own field.
-- Since Pallas.ScalarField < Vesta.ScalarField, all values fit and there are no forbidden values.
instance Shifted (F Vesta.ScalarField) (Type1 (F Vesta.ScalarField)) where
  toShifted (F s) =
    let
      { c, scale } = shift1 (Proxy :: Proxy Vesta.ScalarField)
      t = (s - c) * scale
    in
      Type1 (F t)
  fromShifted (Type1 (F t)) =
    let
      { c } = shift1 (Proxy :: Proxy Vesta.ScalarField)
      two = fromBigInt (BigInt.fromInt 2)
    in
      F (two * t + c)

-- Same-field Type1: Wrap circuit stores Step-field scalars shifted into its own field.
-- Since Vesta.ScalarField < Pallas.ScalarField, all values fit and there are no forbidden values.
instance Shifted (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField)) where
  toShifted (F s) =
    let
      { c, scale } = shift1 (Proxy :: Proxy Pallas.ScalarField)
      t = (s - c) * scale
    in
      Type1 (F t)
  fromShifted (Type1 (F t)) =
    let
      { c } = shift1 (Proxy :: Proxy Pallas.ScalarField)
      two = fromBigInt (BigInt.fromInt 2)
    in
      F (two * t + c)

-- Type2 instances
-- Type2 shift formula: s = t + 2^n, so t = s - 2^n

-- Cross-field Type2: scalar field → Type2 in circuit field (via BigInt)
instance Shifted (F Pallas.ScalarField) (Type2 (F Pallas.BaseField)) where
  toShifted (F s) =
    let
      n = fieldSizeBits (Proxy :: Proxy Pallas.BaseField)
      twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
      -- t = s - 2^n, computed in scalar field then coerced to circuit field via BigInt
      tBigInt = toBigInt (s - fromBigInt twoToN)
    in
      Type2 (F (fromBigInt tBigInt :: Pallas.BaseField))
  fromShifted (Type2 (F t)) =
    let
      n = fieldSizeBits (Proxy :: Proxy Pallas.BaseField)
      tBigInt = toBigInt t
      twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    in
      F $ fromBigInt (tBigInt + twoToN)

-- Same-field Type2: shift a field element within its own field
instance Shifted (F Pallas.ScalarField) (Type2 (F Pallas.ScalarField)) where
  toShifted (F s) =
    let
      n = fieldSizeBits (Proxy :: Proxy Pallas.ScalarField)

      twoToN :: Pallas.ScalarField
      twoToN = fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    in
      Type2 (F (s - twoToN))
  fromShifted (Type2 (F t)) =
    let
      n = fieldSizeBits (Proxy :: Proxy Pallas.ScalarField)

      twoToN :: Pallas.ScalarField
      twoToN = fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    in
      F (t + twoToN)

instance Shifted (F Vesta.ScalarField) (Type2 (F Vesta.ScalarField)) where
  toShifted (F s) =
    let
      n = fieldSizeBits (Proxy :: Proxy Vesta.ScalarField)

      twoToN :: Vesta.ScalarField
      twoToN = fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    in
      Type2 (F (s - twoToN))
  fromShifted (Type2 (F t)) =
    let
      n = fieldSizeBits (Proxy :: Proxy Vesta.ScalarField)

      twoToN :: Vesta.ScalarField
      twoToN = fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    in
      F (t + twoToN)

--------------------------------------------------------------------------------
-- Circuit-level unshifting
--
-- These convert shifted circuit variables back to raw field elements.
-- Used in verification to compare claimed (shifted) values against computed values.
-- Only fromShifted is provided since toShifted for Type2 requires monadic unpacking.
--------------------------------------------------------------------------------

-- | Unshift a Type1 circuit variable: s = 2*t + 2^n + 1
-- | This is OCaml's `to_field`: s = t + t + c
fromShiftedType1Circuit
  :: forall f n
   . PrimeField f
  => FieldSizeInBits f n
  => Type1 (FVar f)
  -> FVar f
fromShiftedType1Circuit (Type1 t) =
  let
    { c } = shift1 (Proxy @f)
    two = fromBigInt (fromInt 2)
  in
    add_ (scale_ two t) (const_ c)

-- | Apply Type1 of_field to a raw circuit variable: t = (s - c) * scale
-- | This is OCaml's `Shifted_value.Type1.of_field`.
-- | Used for comparison matching OCaml's `Shifted_value.equal`:
-- |   equals_ claimedInner (ofFieldType1Circuit rawComputed)
ofFieldType1Circuit
  :: forall f n
   . PrimeField f
  => FieldSizeInBits f n
  => FVar f
  -> FVar f
ofFieldType1Circuit raw =
  let
    { c, scale } = shift1 (Proxy @f)
  in
    scale_ scale (sub_ raw (const_ c))

-- | Compare a claimed Type1 shifted value against a raw computed value.
-- | Matches OCaml's `Shifted_value.Type1.equal Field.equal`:
-- |   equal claimed_inner (of_field raw_computed)
shiftedEqualType1
  :: forall f n c t m
   . PrimeField f
  => FieldSizeInBits f n
  => CircuitM f c t m
  => Type1 (FVar f)
  -> FVar f
  -> Snarky c t m (BoolVar f)
shiftedEqualType1 (Type1 claimedInner) rawComputed =
  equals_ claimedInner (ofFieldType1Circuit rawComputed)

-- | Unshift a Type2 circuit variable: s = t + 2^n
fromShiftedType2Circuit
  :: forall f n
   . PrimeField f
  => FieldSizeInBits f n
  => Type2 (FVar f)
  -> FVar f
fromShiftedType2Circuit (Type2 t) =
  let
    n = fieldSizeBits (Proxy @f)
    twoToN = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n))
  in
    add_ t (const_ twoToN)

-- | Compare a claimed Type2 shifted value against a raw computed value.
-- | Matches OCaml's `Shifted_value.Type2.equal Field.equal`:
-- |   equal claimed_inner (of_field raw_computed)
-- | where of_field raw = raw - 2^n
shiftedEqualType2
  :: forall f n c t m
   . PrimeField f
  => FieldSizeInBits f n
  => CircuitM f c t m
  => Type2 (FVar f)
  -> FVar f
  -> Snarky c t m (BoolVar f)
shiftedEqualType2 (Type2 claimedInner) rawComputed =
  let
    n = fieldSizeBits (Proxy @f)
    twoToN = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n))
  in
    equals_ claimedInner (sub_ rawComputed (const_ twoToN))

--------------------------------------------------------------------------------
-- Utility functions
--------------------------------------------------------------------------------

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
-- | Returns field elements t where t + 2^n ≡ 0 (mod scalarModulus).
-- | These are the raw values in the Type2 wrapper that would produce 0 when unshifted.
-- |
-- | For the Pallas.ScalarField → Type2 (Pallas.BaseField) instance.
forbiddenType2Values :: Array (F Pallas.BaseField)
forbiddenType2Values =
  let
    scalarMod = modulus @Pallas.ScalarField
    sizeInBits = fieldSizeBits (Proxy @Pallas.ScalarField)
    circuitMod = modulus @Pallas.BaseField

    rawValues = forbiddenShiftedValues { modulus: scalarMod, sizeInBits }

    toCircuitField :: BigInt -> Maybe (F Pallas.BaseField)
    toCircuitField x =
      if x < circuitMod then Just (F (fromBigInt x))
      else Nothing
  in
    Array.mapMaybe toCircuitField rawValues

-- | Forbidden values for same-field Type2 representation.
-- | Returns field elements t where t + 2^n ≡ 0 (mod fieldModulus).
-- |
-- | For the Pallas.ScalarField → Type2 (Pallas.ScalarField) instance.
forbiddenType2SameFieldValues :: Array (F Pallas.ScalarField)
forbiddenType2SameFieldValues =
  let
    fMod = modulus @Pallas.ScalarField
    sizeInBits = fieldSizeBits (Proxy @Pallas.ScalarField)

    rawValues = forbiddenShiftedValues { modulus: fMod, sizeInBits }

    toField :: BigInt -> Maybe (F Pallas.ScalarField)
    toField x =
      if x < fMod then Just (F (fromBigInt x))
      else Nothing
  in
    Array.mapMaybe toField rawValues