module Test.BigInt where

import Prelude

import Effect.Class (liftEffect)
import JS.BigInt (BigInt)
import JS.BigInt as BigInt
import Test.QuickCheck (Result, quickCheck, (===))
import Test.QuickCheck.Arbitrary (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Spec (Spec, describe, it)

-- Newtype wrapper for BigInt to provide Arbitrary instance without orphan instances
newtype TestBigInt = TestBigInt BigInt

derive newtype instance Eq TestBigInt
derive newtype instance Show TestBigInt

-- Arbitrary instance for TestBigInt - includes both positive and negative integers
instance Arbitrary TestBigInt where
  arbitrary = do
    n <- arbitrary :: Gen Int
    pure $ TestBigInt $ BigInt.fromInt n

-- Generic ring homomorphism test functions
-- Test that fromBigInt preserves addition: f(a) + f(b) = f(a + b)
testAdditionHomomorphism :: forall f. Eq f => Show f => Semiring f => (BigInt -> f) -> TestBigInt -> TestBigInt -> Result
testAdditionHomomorphism fromBigInt (TestBigInt a) (TestBigInt b) =
  (fromBigInt a + fromBigInt b) === fromBigInt (a + b)

-- Test that fromBigInt preserves multiplication: f(a) * f(b) = f(a * b)
testMultiplicationHomomorphism :: forall f. Eq f => Show f => Semiring f => (BigInt -> f) -> TestBigInt -> TestBigInt -> Result
testMultiplicationHomomorphism fromBigInt (TestBigInt a) (TestBigInt b) =
  (fromBigInt a * fromBigInt b) === fromBigInt (a * b)

-- Test that fromBigInt maps zero correctly: f(0) = 0
testZeroHomomorphism :: forall f. Eq f => Show f => (BigInt -> f) -> f -> Result
testZeroHomomorphism fromBigInt zero =
  fromBigInt (BigInt.fromInt 0) === zero

-- Test that fromBigInt maps one correctly: f(1) = 1
testOneHomomorphism :: forall f. Eq f => Show f => (BigInt -> f) -> f -> Result
testOneHomomorphism fromBigInt one =
  fromBigInt (BigInt.fromInt 1) === one

-- Reusable spec for testing ring homomorphism properties
bigIntHomomorphismSpec :: forall f. Eq f => Show f => Semiring f => String -> (BigInt -> f) -> f -> f -> Spec Unit
bigIntHomomorphismSpec name fromBigInt zero one = describe (name <> " fromBigInt ring homomorphism") do
  it "preserves addition: fromBigInt a + fromBigInt b == fromBigInt (a + b)" $ liftEffect $
    quickCheck (testAdditionHomomorphism fromBigInt)

  it "preserves multiplication: fromBigInt a * fromBigInt b == fromBigInt (a * b)" $ liftEffect $
    quickCheck (testMultiplicationHomomorphism fromBigInt)

  it "maps zero correctly: fromBigInt zero == zero" $ liftEffect $
    quickCheck (testZeroHomomorphism fromBigInt zero)

  it "maps one correctly: fromBigInt one == one" $ liftEffect $
    quickCheck (testOneHomomorphism fromBigInt one)