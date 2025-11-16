module Test.Snarky.Circuit.Field (spec) where

import Prelude

import Data.Foldable (sum)
import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Snarky.Circuit.Compile (compile, makeSolver)
import Snarky.Circuit.DSL (div_, eq_, inv_, mul_, square_, sum_, FieldElem(..))
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Vector (Vector, unVector)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (class Arbitrary, arbitrary)
import Snarky.Circuit.TestUtils (ConstraintSystem, circuitSpec, circuitSpec')
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: forall f. Arbitrary f => PrimeField f => Proxy f -> Spec Unit
spec _ = describe "Field Circuit Specs" do

  it "mul Circuit is Valid" $
    let
      f (Tuple (FieldElem a) (FieldElem b)) = FieldElem (a * b)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry mul_)
      { constraints } = un Identity $
        compile
          (Proxy @(Tuple (FieldElem f) (FieldElem f)))
          (Proxy @(FieldElem f))
          (uncurry mul_)
    in
      circuitSpec constraints solver f

  it "square Circuit is Valid" $
    let
      f (FieldElem a) = FieldElem (a * a)
      solver = makeSolver (Proxy @(ConstraintSystem f)) square_
      { constraints } = un Identity $
        compile
          (Proxy @(FieldElem f))
          (Proxy @(FieldElem f))
          square_
    in
      circuitSpec constraints solver f

  it "eq Circuit is Valid" $
    let
      f :: Tuple (FieldElem f) (FieldElem f) -> Boolean
      f = uncurry (==)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry eq_)
      { constraints } = un Identity $
        compile
          (Proxy @(Tuple (FieldElem f) (FieldElem f)))
          (Proxy @Boolean)
          (uncurry eq_)
    in
      circuitSpec constraints solver f

  it "inv Circuit is Valid" $
    let
      f (FieldElem a) =
        if a == zero then FieldElem zero
        else FieldElem @f (recip a)
      solver = makeSolver (Proxy @(ConstraintSystem f)) inv_
      { constraints } = un Identity $
        compile
          (Proxy @(FieldElem f))
          (Proxy @(FieldElem f))
          inv_
    in
      circuitSpec constraints solver f

  it "div Circuit is Valid" $
    let
      f (Tuple (FieldElem a) (FieldElem b)) =
        if b == zero then FieldElem zero
        else FieldElem @f (a / b)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry div_)
      { constraints } = un Identity $
        compile
          (Proxy @(Tuple (FieldElem f) (FieldElem f)))
          (Proxy @(FieldElem f))
          (uncurry div_)
    in
      circuitSpec constraints solver f

  it "sum Circuit is Valid" $
    let
      f :: Vector 10 (FieldElem f) -> FieldElem f
      f as = FieldElem $ sum (un FieldElem <$> as)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (pure <<< sum_ <<< unVector)
      { constraints } = un Identity $
        compile
          (Proxy @(Vector 10 (FieldElem f)))
          (Proxy @(FieldElem f))
          (pure <<< sum_ <<< unVector)
    in
      circuitSpec' constraints solver f (Vector.generator (Proxy @10) arbitrary)
