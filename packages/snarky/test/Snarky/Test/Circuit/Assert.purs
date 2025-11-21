module Test.Snarky.Circuit.Assert (spec) where

import Prelude

import Data.Tuple (Tuple(..), uncurry)
import Snarky.Circuit.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (F(..), assertEqual, assertNonZero, assertSquare)
import Snarky.Circuit.DSL.Assert (assertNotEqual)
import Snarky.Circuit.TestUtils (ConstraintSystem, circuitSpecPure', expectDivideByZero, satisfied_, unsatisfied)
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
      { constraints } =
        compilePure
          (Proxy @(F f))
          (Proxy @Unit)
          assertNonZero
      gen = do
        a <- arbitrary `suchThat` (_ /= zero)
        pure $ F a
    in
      do
        circuitSpecPure' constraints solver satisfied_ gen
        circuitSpecPure' constraints solver expectDivideByZero (pure $ F zero)

  it "assertEqual Circuit is Valid" $
    let
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry assertEqual)
      { constraints } =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Unit)
          (uncurry assertEqual)
      same = arbitrary <#> \a -> Tuple a a
      distinct = do
        a <- arbitrary
        b <- arbitrary `suchThat` \x -> x /= a
        pure $ Tuple (F a) (F b)
    in
      do
        circuitSpecPure' constraints solver unsatisfied distinct
        circuitSpecPure' constraints solver satisfied_ same

  it "assertNotEqual Circuit is Valid" $
    let
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry assertNotEqual)
      { constraints } =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Unit)
          (uncurry assertNotEqual)
      same = arbitrary <#> \a -> Tuple a a
      distinct = do
        a <- arbitrary
        b <- arbitrary `suchThat` \x -> x /= a
        pure $ Tuple (F a) (F b)
    in
      do
        circuitSpecPure' constraints solver expectDivideByZero same
        circuitSpecPure' constraints solver satisfied_ distinct

  it "assertSquare Circuit is Valid" $
    let
      solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry assertSquare)
      { constraints } =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Unit)
          (uncurry assertSquare)
      squares = do
        x <- arbitrary
        pure $ Tuple (F x) (F (x * x))
      nonSquares = do
        x <- arbitrary
        y <- arbitrary `suchThat` \y -> y /= x * x
        pure $ Tuple (F x) (F y)
    in
      do
        circuitSpecPure' constraints solver satisfied_ squares
        circuitSpecPure' constraints solver unsatisfied nonSquares