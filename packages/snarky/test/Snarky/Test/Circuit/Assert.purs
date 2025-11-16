module Test.Snarky.Circuit.Assert (spec) where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Snarky.Circuit.Compile (compile, makeSolver)
import Snarky.Circuit.DSL (FieldElem(..), assertEqual, assertNonZero)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary)
import Snarky.Circuit.TestUtils (ConstraintSystem, assertionSpec)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: forall f. PrimeField f => Arbitrary f => Proxy f -> Spec Unit
spec _ = describe "Assertion Circuit Specs" do

  it "assertNonZero Circuit is Valid" $
    let
      isValid :: FieldElem f -> Boolean
      isValid (FieldElem a) = a /= zero
      solver = makeSolver (Proxy @(ConstraintSystem f)) assertNonZero
      { constraints } = un Identity $
        compile
          (Proxy @(FieldElem f))
          (Proxy @Unit)
          assertNonZero
    in
      assertionSpec constraints solver isValid

  it "assertEqual Circuit is Valid" $
    let
      isValid :: Tuple (FieldElem f) (FieldElem f) -> Boolean
      isValid (Tuple (FieldElem a) (FieldElem b)) = a == b
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry assertEqual)
      { constraints } = un Identity $
        compile
          (Proxy @(Tuple (FieldElem f) (FieldElem f)))
          (Proxy @Unit)
          (uncurry assertEqual)
    in
      assertionSpec constraints solver isValid