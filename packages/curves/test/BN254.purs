module Test.BN254 where

import Prelude

import Effect.Class (liftEffect)
import Test.Spec (Spec, describe, it)
import Test.QuickCheck (class Arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt)
import Test.QuickCheck.Laws.Data as Laws
import Type.Proxy (Proxy(..))
import Data.Array ((..))
import Data.Foldable (foldr)

import Snarky.Curves.BN254 (ScalarField)

-- Newtype wrapper for ScalarField to create Arbitrary instance
newtype TestBN254 = TestBN254 ScalarField

-- Generate small field elements for testing
smallBN254 :: Gen ScalarField
smallBN254 = do
  n <- chooseInt 0 100
  pure $ foldr (\_ acc -> acc + one) zero (1..n)

instance Arbitrary TestBN254 where
  arbitrary = TestBN254 <$> smallBN254

-- Unwrap for type class instances
derive newtype instance Eq TestBN254
derive newtype instance Semiring TestBN254  
derive newtype instance Ring TestBN254
derive newtype instance CommutativeRing TestBN254
derive newtype instance EuclideanRing TestBN254
derive newtype instance DivisionRing TestBN254
derive newtype instance Show TestBN254

spec :: Spec Unit
spec = describe "BN254 Field Laws" do
  it "satisfies Eq laws" $ liftEffect $
    Laws.checkEq prxTestBN254
  
  it "satisfies Semiring laws" $ liftEffect $
    Laws.checkSemiring prxTestBN254
  
  it "satisfies Ring laws" $ liftEffect $
    Laws.checkRing prxTestBN254
  
  it "satisfies CommutativeRing laws" $ liftEffect $
    Laws.checkCommutativeRing prxTestBN254
  
  it "satisfies EuclideanRing laws" $ liftEffect $
    Laws.checkEuclideanRing prxTestBN254
  
  it "satisfies DivisionRing laws" $ liftEffect $
    Laws.checkDivisionRing prxTestBN254
  where
    prxTestBN254 = Proxy :: Proxy TestBN254