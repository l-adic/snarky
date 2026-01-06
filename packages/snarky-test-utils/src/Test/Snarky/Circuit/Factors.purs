module Test.Snarky.Circuit.Factors (spec) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Snarky.Backend.Builder (class Finalizer, CircuitBuilderState, CircuitBuilderT)
import Snarky.Backend.Compile (Checker, compile, makeSolver)
import Snarky.Backend.Prover (ProverT)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, all_, assert_, const_, equals_, exists, mul_, neq_, read)
import Snarky.Circuit.DSL.Monad (class ConstraintM)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, randomSampleOne, suchThat)
import Test.Snarky.Circuit.Utils (PostCondition, circuitSpec', satisfied_)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

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
   . BasicSystem f c'
  => ConstraintM (CircuitBuilderT c r) c'
  => Finalizer c r
  => ConstraintM (ProverT f) c'
  => Proxy f
  -> Proxy c'
  -> Checker f c
  -> PostCondition f c r
  -> CircuitBuilderState c r
  -> Spec Unit
spec _ pc eval postCondition initialState = describe "Factors Specs" do

  it "factors Circuit is Valid" do

    s <- liftEffect $
      compile
        (Proxy @(F f))
        (Proxy @Unit)
        pc
        factorsCircuit
        initialState
    let solver = makeSolver pc factorsCircuit
    let
      gen :: Gen (F f)
      gen = arbitrary `suchThat` \a -> a /= zero && a /= one
    circuitSpec' randomSampleOne
      { builtState: s
      , checker: eval
      , solver: solver
      , testFunction: satisfied_
      , postCondition: postCondition
      }
      gen