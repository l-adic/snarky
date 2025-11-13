module Test.Snarky.Curves.BaseField where

import Prelude

import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Snarky.Curves.Class (class PrimeField, fromBigInt, toBigInt, pow)
import Test.QuickCheck (class Arbitrary, arbitrary, (===), quickCheck, quickCheckGen)
import Test.QuickCheck.Gen (chooseInt)
import Test.QuickCheck.Laws (checkLaws)
import Test.QuickCheck.Laws.Data as Data
import Test.Spec (Spec, describe, it)
import Test.Snarky.Curves.BigInt (bigIntHomomorphismSpec)
import Type.Proxy (Proxy)

spec :: forall f. PrimeField f => Arbitrary f => Show f => Proxy f -> Spec Unit
spec proxy = describe "BaseField" do
  it "satisfies type class laws" $ liftEffect $ checkLaws "BaseField" do
    Data.checkEq proxy
    Data.checkSemiring proxy
    Data.checkRing proxy
    Data.checkCommutativeRing proxy
    Data.checkEuclideanRing proxy
    Data.checkDivisionRing proxy

  bigIntHomomorphismSpec proxy

  describe "fromBigInt/toBigInt" do
    it "is a left inverse" do
      liftEffect $ quickCheck \(f :: f) ->
        fromBigInt (toBigInt f) === f

  describe "pow" do
    it "pow a 0 = one" do
      liftEffect $ quickCheck \(a :: f) ->
        pow a (BigInt.fromInt 0) === one

    it "pow a 1 = a" do
      liftEffect $ quickCheck \(a :: f) ->
        pow a (BigInt.fromInt 1) === a

    it "pow a (n + m) = pow a n * pow a m" do
      liftEffect $ quickCheckGen do
        a :: f <- arbitrary
        n <- chooseInt 0 10
        m <- chooseInt 0 10
        let
          n' = BigInt.fromInt n
          m' = BigInt.fromInt m
        pure $ pow a (n' + m') === pow a n' * pow a m'

  describe "Special values" do
    it "zero is additive identity" do
      liftEffect $ quickCheck \(a :: f) ->
        (a + zero) === a

    it "one is multiplicative identity" do
      liftEffect $ quickCheck \(a :: f) ->
        (a * one) === a

    it "recip gives multiplicative inverse" do
      liftEffect $ quickCheck \(a :: f) ->
        if a == zero then (one :: f) === one -- Skip zero (trivial test that always passes)
        else (a * recip a) === one