module Test.Snarky.Circuit.Assert (spec) where

import Prelude

import Data.Tuple (Tuple(..), uncurry)
import Snarky.Circuit.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.Constraint.Basic (Basic, evalBasicConstraint)
import Snarky.Circuit.DSL (F(..), assertEqual_, assertNonZero_, assertSquare_, assertNotEqual_)
import Snarky.Circuit.Backend.TestUtils (circuitSpecPure', expectDivideByZero, satisfied_, unsatisfied)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (suchThat)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: forall f. PrimeField f => Arbitrary f => Proxy f -> Spec Unit
spec _ = describe "Assertion Circuit Specs" do

  it "assertNonZero Circuit is Valid" $
    let
      solver = makeSolver (Proxy @(Basic f)) assertNonZero_
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
        circuitSpecPure' constraints evalBasicConstraint solver satisfied_ gen
        circuitSpecPure' constraints evalBasicConstraint solver expectDivideByZero (pure $ F zero)

  it "assertEqual Circuit is Valid" $
    let
      solver = makeSolver (Proxy @(Basic f)) (uncurry assertEqual_)
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
        circuitSpecPure' constraints evalBasicConstraint solver unsatisfied distinct
        circuitSpecPure' constraints evalBasicConstraint solver satisfied_ same

  it "assertNotEqual Circuit is Valid" $
    let
      solver = makeSolver (Proxy @(Basic f)) (uncurry assertNotEqual_)
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
        circuitSpecPure' constraints evalBasicConstraint solver expectDivideByZero same
        circuitSpecPure' constraints evalBasicConstraint solver satisfied_ distinct

  it "assertSquare Circuit is Valid" $
    let
      solver = makeSolver (Proxy @(Basic f)) (uncurry assertSquare_)
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
        circuitSpecPure' constraints evalBasicConstraint solver satisfied_ squares
        circuitSpecPure' constraints evalBasicConstraint solver unsatisfied nonSquares