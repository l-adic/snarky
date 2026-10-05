module Test.Snarky.Curves.Field where

import Prelude

import Data.Array (replicate)
import Data.Foldable (foldr)
import Data.Function.Uncurried (runFn2)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Snarky.Curves.Class (class PrimeField, addFn, eqFn, fromBigInt, mulFn, pow, subFn, toBigInt)
import Test.QuickCheck (arbitrary, quickCheckGen, (===))
import Test.QuickCheck.Gen (chooseInt)
import Test.QuickCheck.Laws.Data as Laws
import Test.Snarky.Curves.BigInt (bigIntHomomorphismSpec)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy)

spec :: forall f. PrimeField f => Proxy f -> Spec Unit
spec proxy = describe "Field Laws" do
  it "satisfies Eq laws" $ liftEffect $
    Laws.checkEq proxy

  it "satisfies Semiring laws" $ liftEffect $
    Laws.checkSemiring proxy

  it "satisfies Ring laws" $ liftEffect $
    Laws.checkRing proxy

  it "satisfies CommutativeRing laws" $ liftEffect $
    Laws.checkCommutativeRing proxy

  it "satisfies EuclideanRing laws" $ liftEffect $
    Laws.checkEuclideanRing proxy

  it "satisfies DivisionRing laws" $ liftEffect $
    Laws.checkDivisionRing proxy

  it "the two-argument operations are the operators" $ liftEffect $ quickCheckGen do
    a :: f <- arbitrary
    b :: f <- arbitrary
    -- half the time compare an element with itself, so `eqFn` sees `true`
    same <- arbitrary
    let c = if same then a else b
    pure $ runFn2 mulFn a b == a * b
      && runFn2 addFn a b == a + b
      && runFn2 subFn a b == a - b
      && runFn2 eqFn a c == (a == c)

  bigIntHomomorphismSpec proxy

  toBigIntPowSpec proxy

toBigIntPowSpec :: forall f. PrimeField f => Proxy f -> Spec Unit
toBigIntPowSpec _ = describe "toBigInt and pow tests" do
  it "toBigInt roundtrips with fromBigInt" $ liftEffect $ quickCheckGen do
    a :: f <- arbitrary
    pure $ fromBigInt (toBigInt a) === a

  it "pow works correctly for small exponents" $ liftEffect $ quickCheckGen do
    base :: f <- arbitrary
    exp <- chooseInt 0 10
    let
      expected = foldr (*) one (replicate exp base)
      actual = pow base (BigInt.fromInt exp)
    pure $ actual === expected

  it "pow(2, n) gives correct powers of two" $ liftEffect $ quickCheckGen do
    n <- chooseInt 0 20
    let
      two = fromBigInt (BigInt.fromInt 2) :: f
      powerOfTwo = pow two (BigInt.fromInt n)
      expected = fromBigInt (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n))
    pure $ powerOfTwo === expected