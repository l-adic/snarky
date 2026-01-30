module Test.Snarky.Data.SizedF (spec) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..), isNothing)
import Data.Vector (Vector)
import Data.Vector as Vector
import Snarky.Circuit.DSL.Bits (packPure)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.SizedF (SizedF, fromBits, fromField, toBits, toField)
import Test.QuickCheck (Result(..), arbitrary, (===))
import Test.QuickCheck.Gen (Gen)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck, quickCheck')
import Type.Proxy (Proxy(..))

type F = Vesta.ScalarField

genSizedF :: Gen (SizedF 128 F)
genSizedF = do
  bits <- Vector.generator (Proxy @128) arbitrary
  pure $ fromBits bits

genLargeField :: Gen F
genLargeField = do
  bits <- Vector.generator (Proxy @255) arbitrary
  let bits' = Vector.updateAt (unsafeFinite 200) true bits
  pure $ packPure bits'

spec :: Spec Unit
spec = describe "SizedF" do
  it "fromBits >>> toBits is identity" $
    quickCheck prop_fromBitsToBits

  it "toBits >>> fromBits is identity" $
    quickCheck prop_toBitsFromBits

  it "toField >>> fromField is Just" $
    quickCheck prop_toFieldFromField

  it "fromField rejects large values" $
    quickCheck prop_fromFieldRejectsLarge

  it "handles maximum 128-bit value (2^128 - 1)" $
    quickCheck' 1 prop_max128BitValue

prop_fromBitsToBits :: Gen Result
prop_fromBitsToBits = do
  bits <- Vector.generator (Proxy @128) arbitrary
  let result = toBits (fromBits bits :: SizedF 128 F)
  pure $ bits === result

prop_toBitsFromBits :: Gen Result
prop_toBitsFromBits = do
  x <- genSizedF
  pure $ x === fromBits (toBits x)

prop_toFieldFromField :: Gen Result
prop_toFieldFromField = do
  x <- genSizedF
  pure $ fromField (toField x) === Just x

prop_fromFieldRejectsLarge :: Gen Result
prop_fromFieldRejectsLarge = do
  large <- genLargeField
  let result = fromField large :: Maybe (SizedF 128 F)
  pure $ isNothing result === true

-- | Test that the maximum 128-bit value (2^128 - 1) works correctly
prop_max128BitValue :: Result
prop_max128BitValue =
  let
    -- Create a SizedF with all 128 bits set to true
    allOnes = Vector.generate (const true) :: Vector 128 Boolean
    maxVal = fromBits allOnes :: SizedF 128 F

    -- Round-trip through field and back
    asField = toField maxVal
    backToSized = fromField asField :: Maybe (SizedF 128 F)

    -- Round-trip through bits
    asBits = toBits maxVal
  in
    -- All checks should pass
    if backToSized == Just maxVal && asBits == allOnes then Success
    else Failed "max 128-bit value round-trip failed"
