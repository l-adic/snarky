module Test.Snarky.Circuit.Factors (spec) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Snarky.Circuit.Compile (compile, makeSolver)
import Snarky.Circuit.Constraint (R1CS, evalR1CSConstraint)
import Snarky.Circuit.DSL (class CircuitM, FVar, F, all_, assert_, const_, equals_, exists, mul_, neq_, read, Snarky)
import Snarky.Circuit.TestUtils (satisfied_, circuitSpec')
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, randomSampleOne, suchThat)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

class Monad m <= FactorM f m where
  factor :: F f -> m { a :: F f, b :: F f }

factorsCircuit
  :: forall t m f
   . FactorM f m
  => CircuitM f (R1CS f) t m
  => FVar f
  -> Snarky t m Unit
factorsCircuit n = do
  { a, b } <- exists do
    nVal <- read n
    lift $ factor @f nVal
  c1 <- equals_ n =<< mul_ a b
  c2 <- neq_ a (const_ one)
  c3 <- neq_ b (const_ one)
  assert_ =<< all_ [ c1, c2, c3 ]

instance (Arbitrary f, PrimeField f) => FactorM f Gen where
  factor n = do
    a <- arbitrary @(F f) `suchThat` \a ->
      a /= one && a /= n
    let b = n / a
    pure $ { a, b }

instance FactorM f Effect where
  factor _ = do
    throw "unhandled request: Factor"

spec :: forall f. Arbitrary f => PrimeField f => Proxy f -> Spec Unit
spec _ = describe "Factors Specs" do

  it "factors Circuit is Valid" $ do
    { constraints } <- liftEffect $
      compile
        (Proxy @(F f))
        (Proxy @Unit)
        factorsCircuit
    let solver = makeSolver (Proxy @(R1CS f)) factorsCircuit
    let
      gen :: Gen (F f)
      gen = arbitrary `suchThat` \a -> a /= zero && a /= one
    circuitSpec' randomSampleOne constraints evalR1CSConstraint solver satisfied_ gen