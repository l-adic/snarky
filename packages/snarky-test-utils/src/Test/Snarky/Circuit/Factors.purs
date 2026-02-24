module Test.Snarky.Circuit.Factors (spec) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Array.NonEmpty as NEA
import Effect (Effect)
import Effect.Exception (throw)
import Snarky.Backend.Builder (class CompileCircuit)
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, all_, assert_, const_, equals_, exists, mul_, neq_, read)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, randomSampleOne, suchThat)
import Test.Snarky.Circuit.Utils (TestConfig, circuitTestM', satisfied_)
import Test.Spec (Spec, describe, it)

class Monad m <= FactorM f m where
  factor :: F f -> m { a :: F f, b :: F f }

factorsCircuit
  :: forall t m f c
   . FactorM f m
  => CircuitM f c t m
  => FVar f
  -> Snarky c t m Unit
factorsCircuit n = do
  { a, b } <- exists do
    nVal <- read n
    lift $ factor @f nVal
  c1 <- equals_ n =<< mul_ a b
  c2 <- neq_ a (const_ one)
  c3 <- neq_ b (const_ one)
  assert_ =<< all_ [ c1, c2, c3 ]

instance (PrimeField f) => FactorM f Gen where
  factor n = do
    a <- arbitrary @(F f) `suchThat` \a ->
      a /= one && a /= n
    let b = n / a
    pure $ { a, b }

instance FactorM f Effect where
  factor _ = do
    throw "unhandled request: Factor"

spec
  :: forall f c c' r
   . CompileCircuit f c c' r
  => SolveCircuit f c'
  => TestConfig f c r
  -> Spec Unit
spec cfg = describe "Factors Specs" do

  it "factors Circuit is Valid" $ void $
    let
      gen :: Gen (F f)
      gen = arbitrary `suchThat` \a -> a /= zero && a /= one

      circuit :: forall t. CircuitM f c' t Gen => FVar f -> Snarky c' t Gen Unit
      circuit = factorsCircuit
    in
      circuitTestM' @f 100 randomSampleOne
        cfg
        (NEA.singleton { testFunction: satisfied_, gen })
        circuit
