module Test.Snarky.Circuit.Assert (spec) where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Snarky.Circuit.Compile (compile, makeSolver)
import Snarky.Circuit.DSL (FieldElem(..), assertEqual, assertNonZero)
import Snarky.Circuit.TestUtils (AssertionExpectation(..), ConstraintSystem, assertionSpec', expectDivideByZero)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (suchThat)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: forall f. PrimeField f => Arbitrary f => Proxy f -> Spec Unit
spec _ = describe "Assertion Circuit Specs" do

  it "assertNonZero Circuit is Valid" $
    let
      solver = makeSolver (Proxy @(ConstraintSystem f)) assertNonZero
      { constraints } = un Identity $
        compile
          (Proxy @(FieldElem f))
          (Proxy @Unit)
          assertNonZero
      gen = do
        a <- arbitrary `suchThat` (_ /= zero)
        pure $ FieldElem a
    in
      do
        assertionSpec' constraints solver (const Satisfied) gen
        assertionSpec' constraints solver expectDivideByZero (pure $ FieldElem zero)

  it "assertEqual Circuit is Valid" $
    let
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry assertEqual)
      { constraints } = un Identity $
        compile
          (Proxy @(Tuple (FieldElem f) (FieldElem f)))
          (Proxy @Unit)
          (uncurry assertEqual)
      same = arbitrary <#> \a -> Tuple a a
      distinct = do
        a <- arbitrary
        b <- arbitrary `suchThat` \x -> x /= a
        pure $ Tuple (FieldElem a) (FieldElem b)
    in
      do
        assertionSpec' constraints solver (const Unsatisfied) distinct
        assertionSpec' constraints solver (const Satisfied) same