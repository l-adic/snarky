module Test.Snarky.Types.Shifted where

import Prelude

import Data.Array.NonEmpty as NEA
import JS.BigInt as BigInt
import Snarky.Circuit.Types (F(..))
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromBigInt, modulus)
import Snarky.Curves.Vesta as Vesta
import Snarky.Types.Shifted (class Shifted, Type1, Type2(..), fieldSizeBits, fromShifted, joinField, splitField, toShifted)
import Test.QuickCheck (Result, (===))
import Test.QuickCheck.Gen (Gen, chooseInt, oneOf)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- splitField / joinField roundtrip (within same field)
--------------------------------------------------------------------------------

splitJoinRoundtrip :: forall @f. PrimeField f => F f -> Result
splitJoinRoundtrip x =
  let
    Type2 { sDiv2: F d, sOdd } = splitField x
    reconstructed = F (joinField { sDiv2: d, sOdd })
  in
    reconstructed === x

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
-- Type2: fromShifted (toShifted s) == s + 2^n (mod field)
--------------------------------------------------------------------------------

type2ShiftRoundtrip
  :: forall @f @f' n
   . FieldSizeInBits f n
  => Shifted (F f) (Type2 (F f') Boolean)
  => F f
  -> Result
type2ShiftRoundtrip s =
  let
    shifted :: Type2 (F f') Boolean
    shifted = toShifted s
    unshifted = fromShifted shifted
    n = fieldSizeBits (Proxy :: Proxy f)
    twoToN = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n))
    expected = case s of F x -> F (x + twoToN)
  in
    unshifted === expected

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
-- Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Snarky.Types.Shifted" do
    describe "splitField / joinField" do
      it "roundtrips in Vesta.BaseField" $
        quickCheck (splitJoinRoundtrip @Vesta.BaseField)
      it "roundtrips in Vesta.ScalarField" $
        quickCheck (splitJoinRoundtrip @Vesta.ScalarField)

    describe "Type1 Shifted (same-field roundtrip)" do
      it "fromShifted (toShifted s) == s (Vesta.BaseField)" $
        quickCheck (type1ShiftRoundtrip @Vesta.BaseField @Vesta.BaseField)
      it "fromShifted (toShifted s) == s (Vesta.ScalarField)" $
        quickCheck (type1ShiftRoundtrip @Vesta.ScalarField @Vesta.ScalarField)
      it "fromShifted (toShifted s) == s (danger zone, Vesta.BaseField)" $
        quickCheck (type1ShiftRoundtrip @Vesta.BaseField @Vesta.BaseField <$> genDangerZone)
      it "fromShifted (toShifted s) == s (danger zone, Vesta.ScalarField)" $
        quickCheck (type1ShiftRoundtrip @Vesta.ScalarField @Vesta.ScalarField <$> genDangerZone)

    describe "Type1 Shifted (crossField)" do
      it "fromShifted (toShifted s) == s" $
        quickCheck (type1ShiftRoundtrip @Vesta.ScalarField @Vesta.BaseField)
      it "fromShifted (toShifted s) == s (danger zone)" $
        quickCheck (type1ShiftRoundtrip @Vesta.ScalarField @Vesta.BaseField <$> genDangerZone)

    describe "Type2 Shifted (same-field, adds 2^n)" do
      it "fromShifted (toShifted s) == s + 2^n (Vesta.BaseField)" $
        quickCheck (type2ShiftRoundtrip @Vesta.BaseField @Vesta.BaseField)
      it "fromShifted (toShifted s) == s + 2^n (Vesta.ScalarField)" $
        quickCheck (type2ShiftRoundtrip @Vesta.ScalarField @Vesta.ScalarField)
      it "fromShifted (toShifted s) == s + 2^n (danger zone, Vesta.BaseField)" $
        quickCheck (type2ShiftRoundtrip @Vesta.BaseField @Vesta.BaseField <$> genDangerZone)
      it "fromShifted (toShifted s) == s + 2^n (danger zone, Vesta.ScalarField)" $
        quickCheck (type2ShiftRoundtrip @Vesta.ScalarField @Vesta.ScalarField <$> genDangerZone)

    describe "Type2 Shifted (crossField)" do
      it "fromShifted (toShifted s) == s" $
        quickCheck (type2ShiftRoundtrip @Vesta.BaseField @Vesta.ScalarField)
      it "fromShifted (toShifted s) == s + 2^n (danger zone)" $
        quickCheck (type2ShiftRoundtrip @Vesta.BaseField @Vesta.ScalarField <$> genDangerZone)