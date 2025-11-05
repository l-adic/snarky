module Test.Vesta where

import Prelude

import Effect.Class (liftEffect)
import Test.Spec (Spec, describe, it)
import Test.QuickCheck (class Arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt)
import Test.QuickCheck.Laws.Data as Laws
import Type.Proxy (Proxy(..))
import Data.Array ((..))
import Data.Foldable (foldr)

import Snarky.Curves.Vesta (ScalarField)

-- Newtype wrapper for ScalarField to create Arbitrary instance
newtype TestVesta = TestVesta ScalarField

-- Generate small field elements for testing
smallVesta :: Gen ScalarField
smallVesta = do
  n <- chooseInt 0 100
  pure $ foldr (\_ acc -> acc + one) zero (1..n)

instance Arbitrary TestVesta where
  arbitrary = TestVesta <$> smallVesta

-- Unwrap for type class instances
derive newtype instance Eq TestVesta
derive newtype instance Semiring TestVesta  
derive newtype instance Ring TestVesta
derive newtype instance CommutativeRing TestVesta
derive newtype instance EuclideanRing TestVesta
derive newtype instance DivisionRing TestVesta
derive newtype instance Show TestVesta

spec :: Spec Unit
spec = describe "Vesta Field Laws" do
  it "satisfies Eq laws" $ liftEffect $
    Laws.checkEq prxTestVesta
  
  it "satisfies Semiring laws" $ liftEffect $
    Laws.checkSemiring prxTestVesta
  
  it "satisfies Ring laws" $ liftEffect $
    Laws.checkRing prxTestVesta
  
  it "satisfies CommutativeRing laws" $ liftEffect $
    Laws.checkCommutativeRing prxTestVesta
  
  it "satisfies EuclideanRing laws" $ liftEffect $
    Laws.checkEuclideanRing prxTestVesta
  
  it "satisfies DivisionRing laws" $ liftEffect $
    Laws.checkDivisionRing prxTestVesta
  where
    prxTestVesta = Proxy :: Proxy TestVesta