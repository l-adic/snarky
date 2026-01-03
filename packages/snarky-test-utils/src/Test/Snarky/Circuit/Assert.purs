module Test.Snarky.Circuit.Assert (spec) where

import Prelude

import Data.Tuple (Tuple(..), uncurry)
import Snarky.Backend.Builder (class Finalizer, CircuitBuilderState, CircuitBuilderT)
import Snarky.Backend.Compile (Checker, compilePure, makeSolver)
import Snarky.Backend.Prover (ProverT)
import Snarky.Circuit.DSL (F(..), assertEqual_, assertNonZero_, assertNotEqual_, assertSquare_)
import Snarky.Circuit.DSL.Monad (class ConstraintM)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (suchThat)
import Test.Snarky.Circuit.Utils (PostCondition, circuitSpecPure', expectDivideByZero, satisfied_, unsatisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall f c r c'
   . PrimeField f
  => BasicSystem f c'
  => ConstraintM (CircuitBuilderT c r) c'
  => ConstraintM (ProverT f) c'
  => Finalizer c r
  => Proxy f
  -> Proxy c'
  -> Checker f c
  -> PostCondition f c r
  -> CircuitBuilderState c r
  -> Spec Unit
spec _ pc eval postCondition initialState = describe "Assertion Circuit Specs" do

  it "assertNonZero Circuit is Valid" $
    let
      solver = makeSolver pc assertNonZero_
      s =
        compilePure
          (Proxy @(F f))
          (Proxy @Unit)
          pc
          assertNonZero_
          initialState
      gen = do
        a <- arbitrary `suchThat` (_ /= zero)
        pure $ F a
    in
      do
        circuitSpecPure' s eval solver satisfied_ gen postCondition
        circuitSpecPure' s eval solver expectDivideByZero (pure zero) postCondition

  it "assertEqual Circuit is Valid" $
    let
      solver = makeSolver pc (uncurry assertEqual_)
      s =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Unit)
          pc
          (uncurry assertEqual_)
          initialState
      same = arbitrary <#> \a -> Tuple a a
      distinct = do
        a <- arbitrary
        b <- arbitrary `suchThat` \x -> x /= a
        pure $ Tuple (F a) (F b)
    in
      do
        circuitSpecPure' s eval solver unsatisfied distinct postCondition
        circuitSpecPure' s eval solver satisfied_ same postCondition

  it "assertNotEqual Circuit is Valid" $
    let
      solver = makeSolver pc (uncurry assertNotEqual_)
      s =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Unit)
          pc
          (uncurry assertNotEqual_)
          initialState
      same = arbitrary <#> \a -> Tuple a a
      distinct = do
        a <- arbitrary
        b <- arbitrary `suchThat` \x -> x /= a
        pure $ Tuple (F a) (F b)
    in
      do
        circuitSpecPure' s eval solver expectDivideByZero same postCondition
        circuitSpecPure' s eval solver satisfied_ distinct postCondition

  it "assertSquare Circuit is Valid" $
    let
      solver = makeSolver pc (uncurry assertSquare_)
      s =
        compilePure
          (Proxy @(Tuple (F f) (F f)))
          (Proxy @Unit)
          pc
          (uncurry assertSquare_)
          initialState
      squares = do
        x <- arbitrary
        pure $ Tuple (F x) (F (x * x))
      nonSquares = do
        x <- arbitrary
        y <- arbitrary `suchThat` \y -> y /= x * x
        pure $ Tuple (F x) (F y)
    in
      do
        circuitSpecPure' s eval solver satisfied_ squares postCondition
        circuitSpecPure' s eval solver unsatisfied nonSquares postCondition