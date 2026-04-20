module Snarky.Types.Shifted
  ( Type1(..)
  , Type2(..)
  , SplitField(..)
  , class Shifted
  , fromShifted
  , toShifted
  , fieldSizeBits
  , forbiddenShiftedValues
  , forbiddenType1Values
  , forbiddenSplitFieldValues
  , fromShiftedType1Circuit
  , ofFieldType1Circuit
  , shiftedEqualType1
  , fromShiftedType2Circuit
  , shiftedEqualType2
  , fromShiftedSplitFieldCircuit
  , splitFieldCircuit
  ) where

import Prelude

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Reflectable (reflectType)
import Data.Show.Generic (genericShow)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (unfoldr)
import JS.BigInt (BigInt, fromInt)
import JS.BigInt as BigInt
import Safe.Coerce (coerce)
import Data.TraversableWithIndex (forWithIndex)
import Snarky.Circuit.DSL (class CheckedType, class CircuitM, class CircuitType, Bool(..), BoolVar, F(..), FVar, Snarky, add_, and_, any_, assertEqual_, assert_, const_, equals_, exists, fieldsToValue, fieldsToVar, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, label, not_, readCVar, scale_, sizeInFields, sub_, valueToFields, varToFields)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, modulus, pow, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Type1: Single field element with shift 2^n + 1 (n = field size in bits)
-- Used when scalar field < circuit field
--------------------------------------------------------------------------------

newtype Type1 f = Type1 f

derive instance Newtype (Type1 f) _
derive instance Functor Type1
derive instance Eq f => Eq (Type1 f)
derive instance Generic (Type1 f) _

instance Show f => Show (Type1 f) where
  show x = genericShow x

instance PrimeField f => CircuitType f (Type1 (F f)) (Type1 (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(Type1 (F f))
  fieldsToVar = genericFieldsToVar @(Type1 (F f))

-- | Check that a Type1 value is not one of the forbidden shifted values.
-- | This is specialized for the Pallas.ScalarField cross-field case (Wrap circuit).
-- | Vesta.ScalarField (= Pallas.BaseField) values stored as Type1 in Fq
-- | can produce forbidden values where 2*t + 2^n + 1 ≡ 0 (mod scalarModulus).
instance CheckedType Pallas.ScalarField c (Type1 (FVar Pallas.ScalarField)) where
  check (Type1 t) = do
    let forbiddenConstants = map (\(F f) -> const_ f) forbiddenType1Values
    matchesForbidden <- for forbiddenConstants (equals_ t)
    anyMatch <- any_ matchesForbidden
    assert_ (not_ anyMatch)

-- | Same-field Type1: Step circuit (Vesta.ScalarField). No forbidden values needed.
instance CheckedType Vesta.ScalarField c (Type1 (FVar Vesta.ScalarField)) where
  check = genericCheck

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

newtype Type2 f = Type2 f

derive instance (Eq f) => Eq (Type2 f)
derive instance Generic (Type2 f) _

instance (Show f) => Show (Type2 f) where
  show x = genericShow x

instance CircuitType f val var => CircuitType f (Type2 val) (Type2 var) where
  valueToFields (Type2 v) = valueToFields @f @val v
  fieldsToValue fs = Type2 (fieldsToValue @f @val fs)
  sizeInFields _ _ = sizeInFields (Proxy @f) (Proxy @val)
  varToFields (Type2 v) = varToFields @f @val v
  fieldsToVar fs = Type2 (fieldsToVar @f @val fs)

instance CheckedType f c (Type2 (FVar f)) where
  check = genericCheck

-- | Check that a Type2 (SplitField) value is not one of the forbidden shifted values.
-- | This is specialized for the Vesta.ScalarField cross-field case (Step circuit).
-- | Pallas.ScalarField values stored as Type2 (SplitField ...) in Fp can produce
-- | forbidden values where 2*sDiv2 + sOdd + 2^n ≡ 0 (mod scalarModulus).
-- | Cross-field Type2 (SplitField) for Step circuit (Vesta.ScalarField = Fp).
-- | Pallas.ScalarField values stored as Type2 (SplitField ...) in Fp need forbidden value checks.
instance CheckedType Vesta.ScalarField c (Type2 (SplitField (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField))) where
  check (Type2 sf@(SplitField { sDiv2, sOdd })) = do
    -- First run the generic check on the inner SplitField (verifies sOdd is a boolean)
    genericCheck sf
    -- For each forbidden (sDiv2, sOdd) pair, check if current matches
    -- Then assert that NONE of them match
    matchesForbidden <- forWithIndex (forbiddenSplitFieldValues @Pallas.ScalarField @Vesta.ScalarField) \idx { sDiv2: F forbiddenDiv2, sOdd: forbiddenOdd } ->
      label ("forbidden_eq_" <> show idx) do
        sDiv2Matches <- equals_ sDiv2 (const_ forbiddenDiv2)
        let sOddMatches = if forbiddenOdd then sOdd else not_ sOdd
        sDiv2Matches `and_` sOddMatches
    anyMatch <- label "forbidden_any" (any_ matchesForbidden)
    label "forbidden_assert_not" (assert_ (not_ anyMatch))

-- | Type2 (SplitField) in Wrap circuit (Pallas.ScalarField = Fq).
-- | Used when the Wrap circuit reads Step public inputs containing Type2 (SplitField ...).
-- | No forbidden value check needed — the Step circuit already validated these.
instance CheckedType Pallas.ScalarField c (Type2 (SplitField (FVar Pallas.ScalarField) (BoolVar Pallas.ScalarField))) where
  check (Type2 sf) = genericCheck sf

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
-- | Two concrete instances avoid overlap with the Type2 (SplitField ...) instance above.
instance CheckedType Vesta.ScalarField c (SplitField (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField)) where
  check = genericCheck

instance CheckedType Pallas.ScalarField c (SplitField (FVar Pallas.ScalarField) (BoolVar Pallas.ScalarField)) where
  check = genericCheck

-- | Split a field element into high bits and low bit.
-- |
-- | Witnesses (sDiv2, sOdd) such that x = 2*sDiv2 + sOdd.
-- | Does NOT check that sDiv2 fits in (n-1) bits — that check is deferred
-- | to scale_fast2 which performs it during the scalar multiplication.
-- |
-- | Reference: wrap_main.ml:57-69
splitFieldCircuit
  :: forall f c t m
   . PrimeField f
  => CircuitM f c t m
  => FVar f
  -> Snarky c t m (SplitField (FVar f) (BoolVar f))
splitFieldCircuit x = do
  let
    two = one + one
    readIsOdd = do
      F xVal <- readCVar x
      pure $ toBigInt xVal `BigInt.and` fromInt 1 == fromInt 1
    readSDiv2 = do
      F xVal <- readCVar x
      let isOdd = toBigInt xVal `BigInt.and` fromInt 1 == fromInt 1
      pure $ F $ (if isOdd then xVal - one else xVal) * recip two
  sDiv2 <- exists readSDiv2
  sOdd <- exists readIsOdd
  -- Assert: 2 * sDiv2 + sOdd == x
  assertEqual_ x (add_ (scale_ two sDiv2) (coerce sOdd))
  pure $ SplitField { sDiv2, sOdd }

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

-- SplitField instance (cross-field, shifted by 2^n)

-- Cross-field SplitField: Fq → SplitField (F Fp) Boolean
-- Used by Step circuit for Wrap scalars (Fq > Fp, needs split representation).
-- The shift is computed in the source field (Fq), then components are converted
-- to the circuit field (Fp) via BigInt.
instance Shifted (F Pallas.ScalarField) (SplitField (F Vesta.ScalarField) Boolean) where
  toShifted (F s) =
    let
      n = fieldSizeBits (Proxy :: Proxy Pallas.ScalarField)

      shift :: Pallas.ScalarField
      shift = fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
      -- s' = s - 2^n in Fq
      sBigInt = toBigInt (s - shift)
      sOdd = BigInt.odd sBigInt
      sDiv2BigInt = (sBigInt - (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)) / BigInt.fromInt 2

      -- Convert to circuit field (Fp) via BigInt
      sDiv2 :: Vesta.ScalarField
      sDiv2 = fromBigInt sDiv2BigInt
    in
      SplitField { sDiv2: F sDiv2, sOdd }
  fromShifted (SplitField { sDiv2: F d, sOdd }) =
    let
      dBigInt = toBigInt d
      sBigInt = BigInt.fromInt 2 * dBigInt + (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)
      twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 255)

      -- Convert back to source field (Fq)
      result :: Pallas.ScalarField
      result = fromBigInt (sBigInt + twoToN)
    in
      F result

-- Same-field SplitField: Fp → SplitField (F Fp) Boolean
-- Used for generating dummy/random shifted values in tests.
-- s = 2*sDiv2 + sOdd + 2^n (where n = field size bits)
instance Shifted (F Vesta.ScalarField) (SplitField (F Vesta.ScalarField) Boolean) where
  toShifted (F s) =
    let
      n = fieldSizeBits (Proxy :: Proxy Vesta.ScalarField)

      shift :: Vesta.ScalarField
      shift = fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
      sBigInt = toBigInt (s - shift)
      sOdd = BigInt.odd sBigInt

      sDiv2 :: Vesta.ScalarField
      sDiv2 = fromBigInt $ (sBigInt - (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)) / BigInt.fromInt 2
    in
      SplitField { sDiv2: F sDiv2, sOdd }
  fromShifted (SplitField { sDiv2: F d, sOdd }) =
    let
      n = fieldSizeBits (Proxy :: Proxy Vesta.ScalarField)
      dBigInt = toBigInt d
      sBigInt = BigInt.fromInt 2 * dBigInt + (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)
      twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    in
      F $ fromBigInt (sBigInt + twoToN)

-- Same-field SplitField: Fq → SplitField (F Fq) Boolean
-- Used for converting between shifted representations in tests.
instance Shifted (F Pallas.ScalarField) (SplitField (F Pallas.ScalarField) Boolean) where
  toShifted (F s) =
    let
      n = fieldSizeBits (Proxy :: Proxy Pallas.ScalarField)

      shift :: Pallas.ScalarField
      shift = fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
      sBigInt = toBigInt (s - shift)
      sOdd = BigInt.odd sBigInt

      sDiv2 :: Pallas.ScalarField
      sDiv2 = fromBigInt $ (sBigInt - (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)) / BigInt.fromInt 2
    in
      SplitField { sDiv2: F sDiv2, sOdd }
  fromShifted (SplitField { sDiv2: F d, sOdd }) =
    let
      n = fieldSizeBits (Proxy :: Proxy Pallas.ScalarField)
      dBigInt = toBigInt d
      sBigInt = BigInt.fromInt 2 * dBigInt + (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)
      twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    in
      F $ fromBigInt (sBigInt + twoToN)

-- Type2 (SplitField) instances: delegate to bare SplitField instances

-- Cross-field Type2 (SplitField): Fq → Type2 (SplitField (F Fp) Boolean)
instance Shifted (F Pallas.ScalarField) (Type2 (SplitField (F Vesta.ScalarField) Boolean)) where
  toShifted s = Type2 (toShifted s)
  fromShifted (Type2 sf) = fromShifted sf

-- Same-field Type2 (SplitField): Fp → Type2 (SplitField (F Fp) Boolean)
instance Shifted (F Vesta.ScalarField) (Type2 (SplitField (F Vesta.ScalarField) Boolean)) where
  toShifted s = Type2 (toShifted s)
  fromShifted (Type2 sf) = fromShifted sf

-- Same-field Type2 (SplitField): Fq → Type2 (SplitField (F Fq) Boolean)
instance Shifted (F Pallas.ScalarField) (Type2 (SplitField (F Pallas.ScalarField) Boolean)) where
  toShifted s = Type2 (toShifted s)
  fromShifted (Type2 sf) = fromShifted sf

-- Type2 (single field) instances

-- Cross-field Type2: scalar field → Type2 in circuit field (via BigInt)
instance FieldSizeInBits f n => Shifted (F f) (Type2 (F f)) where
  toShifted (F s) =
    let
      n = fieldSizeBits (Proxy :: Proxy f)

      shift :: f
      shift = fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)

    in
      Type2 (F $ s - shift)
  fromShifted (Type2 (F sf)) =
    let
      n = fieldSizeBits (Proxy :: Proxy f)
      twoToN = fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    in
      F $ sf + twoToN

{-
-- Same-field Type2: shift a field element within its own field
instance Shifted (F Pallas.ScalarField) (Type2 (F Pallas.ScalarField)) where
  toShifted (F s) =
    let
      n = fieldSizeBits (Proxy :: Proxy Pallas.ScalarField)

      shift :: Pallas.ScalarField
      shift = fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)

      -- s' = s - 2^n (field subtraction, auto mod p)
      sBigInt = toBigInt (s - shift)
      sOdd = BigInt.odd sBigInt

      sDiv2 :: Pallas.ScalarField
      sDiv2 = fromBigInt $ (sBigInt - (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)) / BigInt.fromInt 2
    in
      Type2 { sDiv2: F sDiv2, sOdd }
  fromShifted (Type2 { sDiv2: F d, sOdd }) =
    let
      n = fieldSizeBits (Proxy :: Proxy Pallas.ScalarField)
      dBigInt = toBigInt d
      sBigInt = BigInt.fromInt 2 * dBigInt + (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)
      twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    in
      F $ fromBigInt (sBigInt + twoToN)

instance Shifted (F Vesta.ScalarField) (Type2 (F Vesta.ScalarField)) where
  toShifted (F s) =
    let
      n = fieldSizeBits (Proxy :: Proxy Vesta.ScalarField)

      shift :: Vesta.ScalarField
      shift = fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)

      -- s' = s - 2^n (field subtraction, auto mod p)
      sBigInt = toBigInt (s - shift)
      sOdd = BigInt.odd sBigInt

      sDiv2 :: Vesta.ScalarField
      sDiv2 = fromBigInt $ (sBigInt - (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)) / BigInt.fromInt 2
    in
      Type2 { sDiv2: F sDiv2, sOdd }
  fromShifted (Type2 { sDiv2: F d, sOdd }) =
    let
      n = fieldSizeBits (Proxy :: Proxy Vesta.ScalarField)
      dBigInt = toBigInt d
      sBigInt = BigInt.fromInt 2 * dBigInt + (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)
      twoToN = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)
    in
      F $ fromBigInt (sBigInt + twoToN)
-}
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

-- | Unshift a Type2 circuit variable: s = sf + 2^n
fromShiftedType2Circuit
  :: forall f n
   . PrimeField f
  => FieldSizeInBits f n
  => Type2 (FVar f)
  -> FVar f
fromShiftedType2Circuit (Type2 sf) =
  let
    n = fieldSizeBits (Proxy @f)
    twoToN = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n))
  in
    add_ sf (const_ twoToN)

-- | Compare a claimed Type2 shifted value against a raw computed value.
-- | Matches OCaml's `Shifted_value.Type2.equal`:
-- |   equal (claimed + 2^n) raw_computed
shiftedEqualType2
  :: forall f n c t m
   . PrimeField f
  => FieldSizeInBits f n
  => CircuitM f c t m
  => Type2 (FVar f)
  -> FVar f
  -> Snarky c t m (BoolVar f)
shiftedEqualType2 shifted rawComputed =
  equals_ (fromShiftedType2Circuit shifted) rawComputed

-- | Unshift a SplitField circuit variable: s = 2*sDiv2 + sOdd + 2^n
-- | This is the cross-field shifted representation used by the Step circuit.
fromShiftedSplitFieldCircuit
  :: forall f n
   . PrimeField f
  => FieldSizeInBits f n
  => SplitField (FVar f) (BoolVar f)
  -> FVar f
fromShiftedSplitFieldCircuit (SplitField { sDiv2, sOdd }) =
  let
    n = fieldSizeBits (Proxy @f)
    twoToN = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n))
    two = fromBigInt (fromInt 2)
  in
    add_ (add_ (scale_ two sDiv2) (coerce sOdd)) (const_ twoToN)

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
-- | For the Wrap circuit: Vesta.ScalarField values stored as Type1 in Pallas.ScalarField.
-- | Vesta.BaseField = Pallas.ScalarField, so these are F Pallas.ScalarField values.
forbiddenType1Values :: Array (F Pallas.ScalarField)
forbiddenType1Values =
  let
    scalarMod = modulus @Vesta.ScalarField
    sizeInBits = fieldSizeBits (Proxy @Vesta.ScalarField)
    circuitMod = modulus @Pallas.ScalarField

    rawValues = forbiddenShiftedValues { modulus: scalarMod, sizeInBits }

    -- Filter to values that fit in the circuit field
    toCircuitField :: BigInt -> Maybe (F Pallas.ScalarField)
    toCircuitField x =
      if x < circuitMod then Just (F (fromBigInt x))
      else Nothing
  in
    Array.mapMaybe toCircuitField rawValues

-- | Forbidden values for Type2 (SplitField) representation.
-- | Returns (sDiv2, sOdd) pairs where 2*sDiv2 + sOdd + 2^n ≡ 0 (mod scalarModulus).
-- |
-- | Parameterized by the source field (scalar field being shifted) and the
-- | circuit field (where the split representation lives).
forbiddenSplitFieldValues
  :: forall @scalarField @circuitField
   . PrimeField scalarField
  => PrimeField circuitField
  => FieldSizeInBits scalarField 255
  => FieldSizeInBits circuitField 255
  => Array { sDiv2 :: F circuitField, sOdd :: Boolean }
forbiddenSplitFieldValues =
  let
    scalarMod = modulus @scalarField
    sizeInBits = fieldSizeBits (Proxy @scalarField)
    circuitMod = modulus @circuitField

    rawValues = forbiddenShiftedValues { modulus: scalarMod, sizeInBits }

    -- Convert raw x to (lo, hi) matching OCaml's Other_field decomposition:
    --   hi = test_bit x (Field.size_in_bits - 1)  -- high bit of circuit field
    --   lo = x >> 1                                -- remaining bits
    -- Reference: impls.ml:66-74
    circuitSizeInBits = fieldSizeBits (Proxy @circuitField)

    toSplitField :: BigInt -> Maybe { sDiv2 :: F circuitField, sOdd :: Boolean }
    toSplitField x =
      let
        sOdd = BigInt.and (BigInt.shr x (BigInt.fromInt (circuitSizeInBits - 1))) (BigInt.fromInt 1) == BigInt.fromInt 1
        sDiv2BigInt = BigInt.shr x (BigInt.fromInt 1)
      in
        -- sDiv2 must fit in the circuit field
        if sDiv2BigInt < circuitMod then Just { sDiv2: F (fromBigInt sDiv2BigInt), sOdd }
        else Nothing
  in
    Array.mapMaybe toSplitField rawValues