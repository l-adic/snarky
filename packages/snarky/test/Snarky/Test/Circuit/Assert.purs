module Test.Snarky.Circuit.Assert (spec) where

import Prelude

import Data.Tuple (Tuple(..), uncurry)
import Snarky.Circuit.Compile (compilePure, makeSolver)
import Snarky.Circuit.Constraint (R1CS, evalR1CSConstraint)
import Snarky.Circuit.DSL (F(..), assertEqual_, assertNonZero_, assertSquare_, assertNotEqual_)
import Snarky.Circuit.TestUtils (circuitSpecPure', expectDivideByZero, satisfied_, unsatisfied)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (suchThat)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: forall f. PrimeField f => Arbitrary f => Proxy f -> Spec Unit
spec _ = describe "Assertion Circuit Specs" do

  it "assertNonZero Circuit is Valid" $
    let
      solver = makeSolver (Proxy @(R1CS f)) assertNonZero_
      { constraints } =
        compilePure
          (Proxy @(F f))
          (Proxy @Unit)
          assertNonZero_
      gen = do
        a <- arbitrary `suchThat` (_ /= zero)
        pure $ F a
    in
      do
        circuitSpecPure' constraints evalR1CSConstraint solver satisfied_ gen
        circuitSpecPure' constraints evalR1CSConstraint solver expectDivideByZero (pure $ F zero)

  it "assertEqual Circuit is Valid" $
    let
      solver = makeSolver (Proxy @(R1CS f)) (uncurry assertEqual_)
      { constraints } =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Unit)
          (uncurry assertEqual_)
      same = arbitrary <#> \a -> Tuple a a
      distinct = do
        a <- arbitrary
        b <- arbitrary `suchThat` \x -> x /= a
        pure $ Tuple (F a) (F b)
    in
      do
        circuitSpecPure' constraints evalR1CSConstraint solver unsatisfied distinct
        circuitSpecPure' constraints evalR1CSConstraint solver satisfied_ same

  it "assertNotEqual Circuit is Valid" $
    let
      solver = makeSolver (Proxy @(R1CS f)) (uncurry assertNotEqual_)
      { constraints } =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Unit)
          (uncurry assertNotEqual_)
      same = arbitrary <#> \a -> Tuple a a
      distinct = do
        a <- arbitrary
        b <- arbitrary `suchThat` \x -> x /= a
        pure $ Tuple (F a) (F b)
    in
      do
        circuitSpecPure' constraints evalR1CSConstraint solver expectDivideByZero same
        circuitSpecPure' constraints evalR1CSConstraint solver satisfied_ distinct

  it "assertSquare Circuit is Valid" $
    let
      solver = makeSolver (Proxy @(R1CS f)) (uncurry assertSquare_)
      { constraints } =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Unit)
          (uncurry assertSquare_)
      squares = do
        x <- arbitrary
        pure $ Tuple (F x) (F (x * x))
      nonSquares = do
        x <- arbitrary
        y <- arbitrary `suchThat` \y -> y /= x * x
        pure $ Tuple (F x) (F y)
    in
      do
        circuitSpecPure' constraints evalR1CSConstraint solver satisfied_ squares
        circuitSpecPure' constraints evalR1CSConstraint solver unsatisfied nonSquares