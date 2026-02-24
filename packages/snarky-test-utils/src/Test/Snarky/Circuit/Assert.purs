module Test.Snarky.Circuit.Assert (spec) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Tuple (Tuple(..), uncurry)
import Snarky.Backend.Builder (class CompileCircuit)
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, assertEqual_, assertNonZero_, assertNotEqual_, assertSquare_)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (suchThat)
import Test.Snarky.Circuit.Utils (TestConfig, circuitTest', expectDivideByZero, satisfied_, unsatisfied)
import Test.Spec (Spec, describe, it)

spec
  :: forall f c r c'
   . CompileCircuit f c c' r
  => SolveCircuit f c'
  => TestConfig f c r
  -> Spec Unit
spec cfg = describe "Assertion Circuit Specs" do

  it "assertNonZero Circuit is Valid" $ void $
    let
      gen = do
        a <- arbitrary `suchThat` (_ /= zero)
        pure $ F a

      circuit :: forall t. CircuitM f c' t Identity => FVar f -> Snarky c' t Identity Unit
      circuit = assertNonZero_
    in
      circuitTest' @f 100
        cfg
        ( NEA.cons'
            { testFunction: satisfied_, gen }
            [ { testFunction: expectDivideByZero, gen: pure zero } ]
        )
        circuit

  it "assertEqual Circuit is Valid" $ void $
    let
      same = arbitrary <#> \a -> Tuple a a
      distinct = do
        a <- arbitrary
        b <- arbitrary `suchThat` \x -> x /= a
        pure $ Tuple (F a) (F b)

      circuit :: forall t. CircuitM f c' t Identity => Tuple (FVar f) (FVar f) -> Snarky c' t Identity Unit
      circuit = uncurry assertEqual_
    in
      circuitTest' @f 100
        cfg
        ( NEA.cons'
            { testFunction: unsatisfied, gen: distinct }
            [ { testFunction: satisfied_, gen: same } ]
        )
        circuit

  it "assertNotEqual Circuit is Valid" $ void $
    let
      same = arbitrary <#> \a -> Tuple a a
      distinct = do
        a <- arbitrary
        b <- arbitrary `suchThat` \x -> x /= a
        pure $ Tuple (F a) (F b)

      circuit :: forall t. CircuitM f c' t Identity => Tuple (FVar f) (FVar f) -> Snarky c' t Identity Unit
      circuit = uncurry assertNotEqual_
    in
      circuitTest' @f 100
        cfg
        ( NEA.cons'
            { testFunction: expectDivideByZero, gen: same }
            [ { testFunction: satisfied_, gen: distinct } ]
        )
        circuit

  it "assertSquare Circuit is Valid" $ void $
    let
      squares = do
        x <- arbitrary
        pure $ Tuple (F x) (F (x * x))
      nonSquares = do
        x <- arbitrary
        y <- arbitrary `suchThat` \y -> y /= x * x
        pure $ Tuple (F x) (F y)

      circuit :: forall t. CircuitM f c' t Identity => Tuple (FVar f) (FVar f) -> Snarky c' t Identity Unit
      circuit = uncurry assertSquare_
    in
      circuitTest' @f 100
        cfg
        ( NEA.cons'
            { testFunction: satisfied_, gen: squares }
            [ { testFunction: unsatisfied, gen: nonSquares } ]
        )
        circuit
