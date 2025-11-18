module Test.Snarky.Circuit.Field (spec) where

import Prelude

import Data.Foldable (sum)
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Snarky.Circuit.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL.Field (div_, eq_, inv_, mul_, negate_, square_, sum_)
import Snarky.Circuit.TestUtils (ConstraintSystem, circuitSpecPure, circuitSpecPure', satisfied)
import Snarky.Circuit.Types (FieldElem(..))
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Vector (Vector, unVector)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: forall f. Arbitrary f => PrimeField f => Proxy f -> Spec Unit
spec _ = describe "Field Circuit Specs" do

  it "mul Circuit is Valid" $
    let
      f (Tuple (FieldElem a) (FieldElem b)) = FieldElem (a * b)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry mul_)
      { constraints } =
        compilePure
          (Proxy @(Tuple (FieldElem f) (FieldElem f)))
          (Proxy @(FieldElem f))
          (uncurry mul_)
    in
      circuitSpecPure constraints solver (satisfied f)

  it "square Circuit is Valid" $
    let
      f (FieldElem a) = FieldElem (a * a)
      solver = makeSolver (Proxy @(ConstraintSystem f)) square_
      { constraints } =
        compilePure
          (Proxy @(FieldElem f))
          (Proxy @(FieldElem f))
          square_
    in
      circuitSpecPure constraints solver (satisfied f)

  it "eq Circuit is Valid" $
    let
      f :: Tuple (FieldElem f) (FieldElem f) -> Boolean
      f = uncurry (==)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry eq_)
      { constraints } =
        compilePure
          (Proxy @(Tuple (FieldElem f) (FieldElem f)))
          (Proxy @Boolean)
          (uncurry eq_)
      same = do
        a <- arbitrary
        pure $ Tuple (FieldElem a) (FieldElem a)
      distinct = do
        a <- arbitrary
        b <- arbitrary
        pure $ Tuple (FieldElem a) (FieldElem b)
    in
      do
        circuitSpecPure' constraints solver (satisfied f) same
        circuitSpecPure' constraints solver (satisfied f) distinct

  it "inv Circuit is Valid" $
    let
      f (FieldElem a) =
        if a == zero then FieldElem zero
        else FieldElem @f (recip a)
      solver = makeSolver (Proxy @(ConstraintSystem f)) inv_
      { constraints } =
        compilePure
          (Proxy @(FieldElem f))
          (Proxy @(FieldElem f))
          inv_
    in
      circuitSpecPure constraints solver (satisfied f)

  it "div Circuit is Valid" $
    let
      f (Tuple (FieldElem a) (FieldElem b)) =
        if b == zero then FieldElem zero
        else FieldElem @f (a / b)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry div_)
      { constraints } =
        compilePure
          (Proxy @(Tuple (FieldElem f) (FieldElem f)))
          (Proxy @(FieldElem f))
          (uncurry div_)
    in
      circuitSpecPure constraints solver (satisfied f)

  it "sum Circuit is Valid" $
    let
      f :: Vector 10 (FieldElem f) -> FieldElem f
      f as = FieldElem $ sum (un FieldElem <$> as)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (pure <<< sum_ <<< unVector)
      { constraints } =
        compilePure
          (Proxy @(Vector 10 (FieldElem f)))
          (Proxy @(FieldElem f))
          (pure <<< sum_ <<< unVector)
    in
      circuitSpecPure' constraints solver (satisfied f) (Vector.generator (Proxy @10) arbitrary)

  it "negate Circuit is Valid" $
    let
      f (FieldElem a) = FieldElem (negate a)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (pure <<< negate_)
      { constraints } =
        compilePure
          (Proxy @(FieldElem f))
          (Proxy @(FieldElem f))
          (pure <<< negate_)
    in
      circuitSpecPure constraints solver (satisfied f)
