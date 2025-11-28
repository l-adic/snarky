module Test.Snarky.Circuit.Assert (spec) where

import Prelude

import Data.Tuple (Tuple(..), uncurry)
import Snarky.Circuit.Backend.Compile (compilePure, makeSolver)
import Test.Snarky.Circuit.Utils (circuitSpecPure', expectDivideByZero, satisfied_, unsatisfied)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Circuit.DSL (F(..), Variable, assertEqual_, assertNonZero_, assertNotEqual_, assertSquare_)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (suchThat)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall f c
   . PrimeField f
  => BasicSystem f c
  => Proxy f
  -> Proxy c
  -> ( forall m
        . Applicative m
       => (Variable -> m f)
       -> c
       -> m Boolean
     )
  -> Spec Unit
spec _ pc eval = describe "Assertion Circuit Specs" do

  it "assertNonZero Circuit is Valid" $
    let
      solver = makeSolver pc assertNonZero_
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
        circuitSpecPure' constraints eval solver satisfied_ gen
        circuitSpecPure' constraints eval solver expectDivideByZero (pure $ F zero)

  it "assertEqual Circuit is Valid" $
    let
      solver = makeSolver pc (uncurry assertEqual_)
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
        circuitSpecPure' constraints eval solver unsatisfied distinct
        circuitSpecPure' constraints eval solver satisfied_ same

  it "assertNotEqual Circuit is Valid" $
    let
      solver = makeSolver pc (uncurry assertNotEqual_)
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
        circuitSpecPure' constraints eval solver expectDivideByZero same
        circuitSpecPure' constraints eval solver satisfied_ distinct

  it "assertSquare Circuit is Valid" $
    let
      solver = makeSolver pc (uncurry assertSquare_)
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
        circuitSpecPure' constraints eval solver satisfied_ squares
        circuitSpecPure' constraints eval solver unsatisfied nonSquares