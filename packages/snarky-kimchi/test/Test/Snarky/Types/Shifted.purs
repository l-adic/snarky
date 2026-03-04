module Test.Snarky.Types.Shifted where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import JS.BigInt as BigInt
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, modulus)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Types.Shifted (class Shifted, Type1(..), Type2(..), fieldSizeBits, fromShifted, fromShiftedType1Circuit, fromShiftedType2Circuit, toShifted)
import Test.QuickCheck (Result, (===))
import Test.QuickCheck.Gen (Gen, chooseInt, oneOf)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Type1 roundtrip: fromShifted (toShifted s) == s
--------------------------------------------------------------------------------

type1ShiftRoundtrip
  :: forall @f @f'
   . PrimeField f
  => Shifted (F f) (Type1 (F f'))
  => F f
  -> Result
type1ShiftRoundtrip s =
  let
    shifted :: Type1 (F f')
    shifted = toShifted s
  in
    fromShifted shifted === s

--------------------------------------------------------------------------------
-- Type2 roundtrip: fromShifted (toShifted s) == s
--------------------------------------------------------------------------------

type2ShiftRoundtrip
  :: forall @f n
   . FieldSizeInBits f n
  => Shifted (F f) (Type2 (F f))
  => F f
  -> Result
type2ShiftRoundtrip s =
  let
    shifted :: Type2 (F f)
    shifted = toShifted s
  in
    fromShifted shifted === s

--------------------------------------------------------------------------------
-- Danger zone generators
--------------------------------------------------------------------------------

genDangerZone :: forall @f. PrimeField f => Gen (F f)
genDangerZone =
  let
    m = modulus @f
    two = BigInt.fromInt 2

    genNearZero = do
      small <- chooseInt 0 1000
      pure $ F (fromBigInt (BigInt.fromInt small))

    genNearMax = do
      offset <- chooseInt 1 1000
      pure $ F (fromBigInt (m - BigInt.fromInt offset))

    genNearHalf = do
      offset <- chooseInt 0 1000
      pure $ F (fromBigInt (m / two + BigInt.fromInt offset))

    genEven = do
      k <- chooseInt 1 10000
      pure $ F (fromBigInt (two * BigInt.fromInt k))
  in
    oneOf $ NEA.cons' genNearZero [ genNearMax, genNearHalf, genEven ]

--------------------------------------------------------------------------------
-- Circuit-level tests for fromShiftedType1Circuit and fromShiftedType2Circuit
--------------------------------------------------------------------------------

-- | Circuit that computes fromShiftedType1Circuit (cross-field: Vesta.BaseField).
type1Circuit
  :: forall t
   . CircuitM Vesta.BaseField (KimchiConstraint Vesta.BaseField) t Identity
  => Type1 (FVar Vesta.BaseField)
  -> Snarky (KimchiConstraint Vesta.BaseField) t Identity (FVar Vesta.BaseField)
type1Circuit shifted = pure $ fromShiftedType1Circuit shifted

-- | Circuit that computes fromShiftedType1Circuit (same-field: Vesta.ScalarField).
type1SameFieldCircuit
  :: forall t
   . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t Identity
  => Type1 (FVar Vesta.ScalarField)
  -> Snarky (KimchiConstraint Vesta.ScalarField) t Identity (FVar Vesta.ScalarField)
type1SameFieldCircuit shifted = pure $ fromShiftedType1Circuit shifted

-- | Circuit that computes fromShiftedType2Circuit.
type2Circuit
  :: forall @f t n
   . CircuitM f (KimchiConstraint f) t Identity
  => PrimeField f
  => FieldSizeInBits f n
  => Type2 (FVar f)
  -> Snarky (KimchiConstraint f) t Identity (FVar f)
type2Circuit shifted = pure $ fromShiftedType2Circuit shifted

-- | Pure computation for Type1 (cross-field): s = 2*t + 2^n + 1
type1Expected :: Type1 (F Vesta.BaseField) -> F Vesta.BaseField
type1Expected (Type1 (F t)) =
  let
    n = fieldSizeBits (Proxy :: Proxy Vesta.BaseField)
    two = fromBigInt (BigInt.fromInt 2)
    twoToN = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n))
  in
    F (two * t + twoToN + one)

-- | Pure computation for Type1 (same-field): s = 2*t + 2^n + 1
type1SameFieldExpected :: Type1 (F Vesta.ScalarField) -> F Vesta.ScalarField
type1SameFieldExpected (Type1 (F t)) =
  let
    n = fieldSizeBits (Proxy :: Proxy Vesta.ScalarField)
    two = fromBigInt (BigInt.fromInt 2)
    twoToN = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n))
  in
    F (two * t + twoToN + one)

-- | Pure computation for Type2: s = t + 2^n
type2Expected :: forall @f n. FieldSizeInBits f n => Type2 (F f) -> F f
type2Expected (Type2 (F t)) =
  let
    n = fieldSizeBits (Proxy :: Proxy f)
    twoToN = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n))
  in
    F (t + twoToN)

--------------------------------------------------------------------------------
-- Spec
--------------------------------------------------------------------------------

spec :: (forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)) -> Spec Unit
spec cfg = do
  describe "Snarky.Types.Shifted" do
    describe "Type1 Shifted (crossField)" do
      it "fromShifted (toShifted s) == s" $
        quickCheck (type1ShiftRoundtrip @Vesta.ScalarField @Vesta.BaseField)
      it "fromShifted (toShifted s) == s (danger zone)" $
        quickCheck (type1ShiftRoundtrip @Vesta.ScalarField @Vesta.BaseField <$> genDangerZone)

    describe "Type1 Shifted (sameField)" do
      it "fromShifted (toShifted s) == s" $
        quickCheck (type1ShiftRoundtrip @Vesta.ScalarField @Vesta.ScalarField)
      it "fromShifted (toShifted s) == s (danger zone)" $
        quickCheck (type1ShiftRoundtrip @Vesta.ScalarField @Vesta.ScalarField <$> genDangerZone)

    describe "Type2 Shifted (Pallas.ScalarField)" do
      it "fromShifted (toShifted s) == s" $
        quickCheck (type2ShiftRoundtrip @Pallas.ScalarField)
      it "fromShifted (toShifted s) == s (danger zone)" $
        quickCheck (type2ShiftRoundtrip @Pallas.ScalarField <$> genDangerZone)

    describe "Type2 Shifted (Vesta.ScalarField)" do
      it "fromShifted (toShifted s) == s" $
        quickCheck (type2ShiftRoundtrip @Vesta.ScalarField)
      it "fromShifted (toShifted s) == s (danger zone)" $
        quickCheck (type2ShiftRoundtrip @Vesta.ScalarField <$> genDangerZone)

    describe "fromShiftedType1Circuit" do
      it "circuit matches pure implementation" do
        let
          gen = toShifted <$> genDangerZone @Vesta.ScalarField
        void $ circuitTest' @Vesta.BaseField
          cfg
          (NEA.singleton { testFunction: satisfied type1Expected, input: QuickCheck 100 gen })
          type1Circuit

    describe "fromShiftedType1Circuit (sameField)" do
      it "circuit matches pure implementation" do
        let
          gen = toShifted <$> genDangerZone @Vesta.ScalarField
        void $ circuitTest' @Vesta.ScalarField
          cfg
          (NEA.singleton { testFunction: satisfied type1SameFieldExpected, input: QuickCheck 100 gen })
          type1SameFieldCircuit

    describe "fromShiftedType2Circuit" do
      it "circuit matches pure implementation" do
        let
          gen = toShifted <$> genDangerZone @Pallas.ScalarField
        void $ circuitTest' @Pallas.ScalarField
          cfg
          (NEA.singleton { testFunction: satisfied (type2Expected @Pallas.ScalarField), input: QuickCheck 100 gen })
          (type2Circuit @Pallas.ScalarField)