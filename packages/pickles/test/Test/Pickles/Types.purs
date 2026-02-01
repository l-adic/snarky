module Test.Pickles.Types where

import Prelude

import Data.Array.NonEmpty as NEA
import JS.BigInt as BigInt
import Pickles.Types (OtherField, SplitField, fromOtherField, toOtherField)
import Snarky.Curves.Class (fromBigInt, modulus)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (Result, arbitrary, (===))
import Test.QuickCheck.Gen (Gen, chooseInt, oneOf)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)

--------------------------------------------------------------------------------
-- Retraction properties: fromOtherField . toOtherField = id
--------------------------------------------------------------------------------

-- | Pallas.ScalarField -> SplitField -> Pallas.ScalarField is a retraction
retractionPallasToSplit :: Pallas.ScalarField -> Result
retractionPallasToSplit x =
  let
    converted :: SplitField Vesta.ScalarField Boolean
    converted = toOtherField x
  in
    fromOtherField converted === x

-- | Vesta.ScalarField -> OtherField Pallas.ScalarField -> Vesta.ScalarField is a retraction
retractionVestaToPallas :: Vesta.ScalarField -> Result
retractionVestaToPallas x =
  let
    converted :: OtherField Pallas.ScalarField
    converted = toOtherField x
  in
    fromOtherField converted === x

--------------------------------------------------------------------------------
-- Danger zone generators (boundary testing)
--------------------------------------------------------------------------------

genDangerZonePallasScalar :: Gen Pallas.ScalarField
genDangerZonePallasScalar =
  let
    m = modulus @Pallas.ScalarField
    two = BigInt.fromInt 2

    genNearZero = do
      small <- chooseInt 0 1000
      pure $ fromBigInt (BigInt.fromInt small)

    genNearMax = do
      offset <- chooseInt 1 1000
      pure $ fromBigInt (m - BigInt.fromInt offset)

    genNearHalf = do
      offset <- chooseInt 0 1000
      pure $ fromBigInt (m / two + BigInt.fromInt offset)

    genEven = do
      k <- chooseInt 1 10000
      pure $ fromBigInt (two * BigInt.fromInt k)

    genOdd = do
      k <- chooseInt 0 10000
      pure $ fromBigInt (two * BigInt.fromInt k + BigInt.fromInt 1)
  in
    oneOf $ NEA.cons' genNearZero [ genNearMax, genNearHalf, genEven, genOdd ]

genDangerZoneVestaScalar :: Gen Vesta.ScalarField
genDangerZoneVestaScalar =
  let
    m = modulus @Vesta.ScalarField
    two = BigInt.fromInt 2

    genNearZero = do
      small <- chooseInt 0 1000
      pure $ fromBigInt (BigInt.fromInt small)

    genNearMax = do
      offset <- chooseInt 1 1000
      pure $ fromBigInt (m - BigInt.fromInt offset)

    genNearHalf = do
      offset <- chooseInt 0 1000
      pure $ fromBigInt (m / two + BigInt.fromInt offset)

    genEven = do
      k <- chooseInt 1 10000
      pure $ fromBigInt (two * BigInt.fromInt k)

    genOdd = do
      k <- chooseInt 0 10000
      pure $ fromBigInt (two * BigInt.fromInt k + BigInt.fromInt 1)
  in
    oneOf $ NEA.cons' genNearZero [ genNearMax, genNearHalf, genEven, genOdd ]

--------------------------------------------------------------------------------
-- Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Pickles.Types" do
    describe "HasOtherField Pallas.ScalarField (SplitField Vesta.ScalarField Boolean)" do
      it "fromOtherField . toOtherField = id" $
        quickCheck (retractionPallasToSplit <$> genPallasScalar)

      it "fromOtherField . toOtherField = id (danger zone)" $
        quickCheck (retractionPallasToSplit <$> genDangerZonePallasScalar)

    describe "HasOtherField Vesta.ScalarField (OtherField Pallas.ScalarField)" do
      it "fromOtherField . toOtherField = id" $
        quickCheck (retractionVestaToPallas <$> genVestaScalar)

      it "fromOtherField . toOtherField = id (danger zone)" $
        quickCheck (retractionVestaToPallas <$> genDangerZoneVestaScalar)

  where
  genPallasScalar :: Gen Pallas.ScalarField
  genPallasScalar = arbitrary

  genVestaScalar :: Gen Vesta.ScalarField
  genVestaScalar = arbitrary
