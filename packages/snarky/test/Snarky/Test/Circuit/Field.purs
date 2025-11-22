module Test.Snarky.Circuit.Field (spec) where

import Prelude

import Data.Foldable (sum)
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Snarky.Circuit.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (div_, equals_, inv_, mul_, negate_, sum_)
import Snarky.Circuit.TestUtils (ConstraintSystem, circuitSpecPure, circuitSpecPure', satisfied)
import Snarky.Circuit.Types (F(..))
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
      f (Tuple (F a) (F b)) = F (a * b)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry mul_)
      { constraints } =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @(F f))
          (uncurry mul_)
    in
      circuitSpecPure constraints solver (satisfied f)

  it "eq Circuit is Valid" $
    let
      f :: Tuple (F f) (F f) -> Boolean
      f = uncurry (==)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry equals_)
      { constraints } =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Boolean)
          (uncurry equals_)
      same = do
        a <- arbitrary
        pure $ Tuple (F a) (F a)
      distinct = do
        a <- arbitrary
        b <- arbitrary
        pure $ Tuple (F a) (F b)
    in
      do
        circuitSpecPure' constraints solver (satisfied f) same
        circuitSpecPure' constraints solver (satisfied f) distinct

  it "inv Circuit is Valid" $
    let
      f (F a) =
        if a == zero then F zero
        else F @f (recip a)
      solver = makeSolver (Proxy @(ConstraintSystem f)) inv_
      { constraints } =
        compilePure
          (Proxy @(F f))
          (Proxy @(F f))
          inv_
    in
      circuitSpecPure constraints solver (satisfied f)

  it "div Circuit is Valid" $
    let
      f (Tuple (F a) (F b)) =
        if b == zero then F zero
        else F @f (a / b)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry div_)
      { constraints } =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @(F f))
          (uncurry div_)
    in
      circuitSpecPure constraints solver (satisfied f)

  it "sum Circuit is Valid" $
    let
      f :: Vector 10 (F f) -> F f
      f as = F $ sum (un F <$> as)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (pure <<< sum_ <<< unVector)
      { constraints } =
        compilePure
          (Proxy @(Vector 10 (F f)))
          (Proxy @(F f))
          (pure <<< sum_ <<< unVector)
    in
      circuitSpecPure' constraints solver (satisfied f) (Vector.generator (Proxy @10) arbitrary)

  it "negate Circuit is Valid" $
    let
      f (F a) = F (negate a)
      solver = makeSolver (Proxy @(ConstraintSystem f)) (pure <<< negate_)
      { constraints } =
        compilePure
          (Proxy @(F f))
          (Proxy @(F f))
          (pure <<< negate_)
    in
      circuitSpecPure constraints solver (satisfied f)