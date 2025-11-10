module Test.Snarky.Curves.BigInt where

import Prelude

import Effect.Class (liftEffect)
import JS.BigInt (BigInt)
import JS.BigInt as BigInt
import Snarky.Curves.Types (class PrimeField, fromBigInt)
import Test.QuickCheck (Result, quickCheck, (===))
import Test.QuickCheck.Arbitrary (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy)

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
testAdditionHomomorphism :: forall f. PrimeField f => Proxy f -> TestBigInt -> TestBigInt -> Result
testAdditionHomomorphism _ (TestBigInt a) (TestBigInt b) =
  (fromBigInt a + fromBigInt b) === fromBigInt @f (a + b)

-- Test that fromBigInt preserves multiplication: f(a) * f(b) = f(a * b)
testMultiplicationHomomorphism :: forall f. PrimeField f => Proxy f -> TestBigInt -> TestBigInt -> Result
testMultiplicationHomomorphism _ (TestBigInt a) (TestBigInt b) =
  (fromBigInt a * fromBigInt b) === fromBigInt @f (a * b)

-- Test that fromBigInt maps zero correctly: f(0) = 0
testZeroHomomorphism :: forall f. PrimeField f => Proxy f -> Result
testZeroHomomorphism _ =
  fromBigInt (BigInt.fromInt 0) === zero @f

-- Test that fromBigInt maps one correctly: f(1) = 1
testOneHomomorphism :: forall f. PrimeField f => Proxy f -> Result
testOneHomomorphism _ =
  fromBigInt (BigInt.fromInt 1) === one @f

-- Reusable spec for testing ring homomorphism properties
bigIntHomomorphismSpec :: forall f. PrimeField f => Proxy f -> Spec Unit
bigIntHomomorphismSpec proxy = describe "BigInt algebra" do
  it "preserves addition: fromBigInt a + fromBigInt b == fromBigInt (a + b)" $ liftEffect $
    quickCheck (testAdditionHomomorphism proxy)

  it "preserves multiplication: fromBigInt a * fromBigInt b == fromBigInt (a * b)" $ liftEffect $
    quickCheck (testMultiplicationHomomorphism proxy)

  it "maps zero correctly: fromBigInt zero == zero" $ liftEffect $
    quickCheck (testZeroHomomorphism proxy)

  it "maps one correctly: fromBigInt one == one" $ liftEffect $
    quickCheck (testOneHomomorphism proxy)