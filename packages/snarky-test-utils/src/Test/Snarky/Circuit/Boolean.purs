module Test.Snarky.Circuit.Boolean (spec) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Foldable (foldMap)
import Data.Identity (Identity)
import Data.Monoid.Conj (Conj(..))
import Data.Monoid.Disj (Disj(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, uncurry3)
import Data.Vector (Vector)
import Data.Vector as Vector
import Snarky.Backend.Builder (class CompileCircuit)
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, all_, and_, any_, if_, not_, or_, xor_)
import Test.QuickCheck (arbitrary)
import Test.Snarky.Circuit.Utils (TestConfig, circuitTest', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall f c c' r
   . CompileCircuit f c c' r
  => SolveCircuit f c'
  => TestConfig f c r
  -> Spec Unit
spec cfg = describe "Boolean Circuit Specs" do

  it "not Circuit is Valid" $ void $
    let
      circuit :: forall t. CircuitM f c' t Identity => BoolVar f -> Snarky c' t Identity (BoolVar f)
      circuit = pure <<< not_
    in
      circuitTest' @f 100
        cfg
        (NEA.singleton { testFunction: satisfied (not :: Boolean -> Boolean), gen: arbitrary })
        circuit

  it "and Circuit is Valid" $ void $
    let
      circuit :: forall t. CircuitM f c' t Identity => Tuple (BoolVar f) (BoolVar f) -> Snarky c' t Identity (BoolVar f)
      circuit = uncurry and_
    in
      circuitTest' @f 100
        cfg
        (NEA.singleton { testFunction: satisfied (uncurry (&&) :: Tuple Boolean Boolean -> Boolean), gen: arbitrary })
        circuit

  it "or Circuit is Valid" $ void $
    let
      circuit :: forall t. CircuitM f c' t Identity => Tuple (BoolVar f) (BoolVar f) -> Snarky c' t Identity (BoolVar f)
      circuit = uncurry or_
    in
      circuitTest' @f 100
        cfg
        (NEA.singleton { testFunction: satisfied (uncurry (||) :: Tuple Boolean Boolean -> Boolean), gen: arbitrary })
        circuit

  it "xor Circuit is Valid" $ void $
    let
      f :: Tuple Boolean Boolean -> Boolean
      f (Tuple a b) = (a && not b) || (not a && b)

      circuit :: forall t. CircuitM f c' t Identity => Tuple (BoolVar f) (BoolVar f) -> Snarky c' t Identity (BoolVar f)
      circuit = uncurry xor_
    in
      circuitTest' @f 100
        cfg
        (NEA.singleton { testFunction: satisfied f, gen: arbitrary })
        circuit

  it "if Circuit is Valid" $ void $
    let
      f :: Tuple3 Boolean (F f) (F f) -> F f
      f = uncurry3 \b t e ->
        if b then t else e

      circuit :: forall t. CircuitM f c' t Identity => Tuple3 (BoolVar f) (FVar f) (FVar f) -> Snarky c' t Identity (FVar f)
      circuit = uncurry3 if_
    in
      circuitTest' @f 100
        cfg
        (NEA.singleton { testFunction: satisfied f, gen: arbitrary })
        circuit

  it "all Circuit is Valid" $ void $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Conj <<< foldMap Conj

      circuit :: forall t. CircuitM f c' t Identity => Vector 10 (BoolVar f) -> Snarky c' t Identity (BoolVar f)
      circuit = all_ <<< Vector.toUnfoldable
    in
      circuitTest' @f 100
        cfg
        (NEA.singleton { testFunction: satisfied f, gen: Vector.generator (Proxy @10) arbitrary })
        circuit

  it "any Circuit is Valid" $ void $
    let
      f :: forall n. Vector n Boolean -> Boolean
      f = un Disj <<< foldMap Disj

      circuit :: forall t. CircuitM f c' t Identity => Vector 10 (BoolVar f) -> Snarky c' t Identity (BoolVar f)
      circuit = any_ <<< Vector.toUnfoldable
    in
      circuitTest' @f 100
        cfg
        (NEA.singleton { testFunction: satisfied f, gen: Vector.generator (Proxy @10) arbitrary })
        circuit
