module Test.Snarky.Circuit.Field (spec) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Foldable (sum)
import Data.Identity (Identity)
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Data.Vector (Vector)
import Data.Vector as Vector
import Snarky.Backend.Builder (class CompileCircuit)
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, div_, equals_, inv_, mul_, negate_, seal, sum_)
import Test.QuickCheck (arbitrary)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall f c r c'
   . CompileCircuit f c c' r
  => SolveCircuit f c'
  => TestConfig f c r
  -> Spec Unit
spec cfg = describe "Field Circuit Specs" do

  it "mul Circuit is Valid" $ void $
    let
      circuit :: forall t. CircuitM f c' t Identity => Tuple (FVar f) (FVar f) -> Snarky c' t Identity (FVar f)
      circuit = uncurry mul_
    in
      circuitTest' @f
        cfg
        (NEA.singleton { testFunction: satisfied \(Tuple (F a) (F b)) -> F (a * b), input: QuickCheck 100 arbitrary })
        circuit

  it "eq Circuit is Valid" $ void $
    let
      f :: Tuple (F f) (F f) -> Boolean
      f = uncurry (==)
      same = do
        a <- arbitrary
        pure $ Tuple (F a) (F a)
      distinct = do
        a <- arbitrary
        b <- arbitrary
        pure $ Tuple (F a) (F b)

      circuit :: forall t. CircuitM f c' t Identity => Tuple (FVar f) (FVar f) -> Snarky c' t Identity (BoolVar f)
      circuit = uncurry equals_
    in
      circuitTest' @f
        cfg
        ( NEA.cons'
            { testFunction: satisfied f, input: QuickCheck 100 same }
            [ { testFunction: satisfied f, input: QuickCheck 100 distinct } ]
        )
        circuit

  it "inv Circuit is Valid" $ void $
    let
      f (F a) =
        if a == zero then F zero
        else F @f (recip a)

      circuit :: forall t. CircuitM f c' t Identity => FVar f -> Snarky c' t Identity (FVar f)
      circuit = inv_
    in
      circuitTest' @f
        cfg
        (NEA.singleton { testFunction: satisfied f, input: QuickCheck 100 arbitrary })
        circuit

  it "div Circuit is Valid" $ void $
    let
      f (Tuple (F a) (F b)) =
        if b == zero then F zero
        else F @f (a / b)

      circuit :: forall t. CircuitM f c' t Identity => Tuple (FVar f) (FVar f) -> Snarky c' t Identity (FVar f)
      circuit = uncurry div_
    in
      circuitTest' @f
        cfg
        (NEA.singleton { testFunction: satisfied f, input: QuickCheck 100 arbitrary })
        circuit

  it "sum Circuit is Valid" $ void $
    let
      f :: Vector 10 (F f) -> F f
      f as = F $ sum (un F <$> as)

      circuit :: forall t. CircuitM f c' t Identity => Vector 10 (FVar f) -> Snarky c' t Identity (FVar f)
      circuit = pure <<< sum_ <<< Vector.toUnfoldable
    in
      circuitTest' @f
        cfg
        (NEA.singleton { testFunction: satisfied f, input: QuickCheck 100 (Vector.generator (Proxy @10) arbitrary) })
        circuit

  it "negate Circuit is Valid" $ void $
    let
      circuit :: forall t. CircuitM f c' t Identity => FVar f -> Snarky c' t Identity (FVar f)
      circuit = pure <<< negate_
    in
      circuitTest' @f
        cfg
        (NEA.singleton { testFunction: satisfied \(F a) -> F (negate a), input: QuickCheck 100 arbitrary })
        circuit

  it "seal Circuit is Valid" $ void $
    let
      circuit :: forall t. CircuitM f c' t Identity => FVar f -> Snarky c' t Identity (FVar f)
      circuit = seal
    in
      circuitTest' @f
        cfg
        (NEA.singleton { testFunction: satisfied (identity :: F f -> F f), input: QuickCheck 100 arbitrary })
        circuit
