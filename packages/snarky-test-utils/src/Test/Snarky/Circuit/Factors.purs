module Test.Snarky.Circuit.Factors (spec) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Snarky.Backend.Compile (compile, makeSolver)
import Test.Snarky.Circuit.Utils (satisfied_, circuitSpec')
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, Variable, all_, assert_, const_, equals_, exists, mul_, neq_, read)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, randomSampleOne, suchThat)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

class Monad m <= FactorM f m where
  factor :: F f -> m { a :: F f, b :: F f }

factorsCircuit
  :: forall t m f c
   . FactorM f m
  => CircuitM f c t m
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
spec _ pc eval = describe "Factors Specs" do

  it "factors Circuit is Valid" $ do
    { constraints } <- liftEffect $
      compile
        (Proxy @(F f))
        (Proxy @Unit)
        factorsCircuit
    let solver = makeSolver pc factorsCircuit
    let
      gen :: Gen (F f)
      gen = arbitrary `suchThat` \a -> a /= zero && a /= one
    circuitSpec' randomSampleOne constraints eval solver satisfied_ gen