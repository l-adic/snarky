module Test.Pallas where

import Prelude

import Effect.Class (liftEffect)
import Test.Spec (Spec, describe, it)
import Test.QuickCheck (class Arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt)
import Test.QuickCheck.Laws.Data as Laws
import Type.Proxy (Proxy(..))
import Data.Array ((..))
import Data.Foldable (foldr)

import Snarky.Curves.Pallas (ScalarField)

-- Newtype wrapper for ScalarField to create Arbitrary instance
newtype TestPallas = TestPallas ScalarField

-- Generate small field elements for testing
smallPallas :: Gen ScalarField
smallPallas = do
  n <- chooseInt 0 100
  pure $ foldr (\_ acc -> acc + one) zero (1..n)

instance Arbitrary TestPallas where
  arbitrary = TestPallas <$> smallPallas

-- Unwrap for type class instances
derive newtype instance Eq TestPallas
derive newtype instance Semiring TestPallas  
derive newtype instance Ring TestPallas
derive newtype instance CommutativeRing TestPallas
derive newtype instance EuclideanRing TestPallas
derive newtype instance DivisionRing TestPallas
derive newtype instance Show TestPallas

spec :: Spec Unit
spec = describe "Pallas Field Laws" do
  it "satisfies Eq laws" $ liftEffect $
    Laws.checkEq prxTestPallas
  
  it "satisfies Semiring laws" $ liftEffect $
    Laws.checkSemiring prxTestPallas
  
  it "satisfies Ring laws" $ liftEffect $
    Laws.checkRing prxTestPallas
  
  it "satisfies CommutativeRing laws" $ liftEffect $
    Laws.checkCommutativeRing prxTestPallas
  
  it "satisfies EuclideanRing laws" $ liftEffect $
    Laws.checkEuclideanRing prxTestPallas
  
  it "satisfies DivisionRing laws" $ liftEffect $
    Laws.checkDivisionRing prxTestPallas
  where
    prxTestPallas = Proxy :: Proxy TestPallas