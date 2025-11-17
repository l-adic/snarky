module Test.Snarky.Circuit.Factors (spec) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Snarky.Circuit.Compile (compile, makeSolver)
import Snarky.Circuit.Constraint (evalR1CSConstraint)
import Snarky.Circuit.DSL (class CircuitM, CVar, exists, read, assert, all_, eq_, mul_, neq_, FieldElem(..), Variable, const_)
import Snarky.Circuit.TestUtils (AssertionExpectation(..), ConstraintSystem, makeAssertionSpec)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, Result, arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

class Monad m <= FactorM f m where
  factor :: f -> m (Tuple f f)

factorsCircuit
  :: forall t m f
   . FactorM f m
  => CircuitM f (ConstraintSystem f) t m
  => CVar f Variable
  -> t m Unit
factorsCircuit n = do
  Tuple a b <- exists do
    FieldElem nVal <- read n
    Tuple a b <- lift $ factor @f nVal
    pure $ Tuple (FieldElem a) (FieldElem b)
  c1 <- mul_ a b >>= eq_ n
  c2 <- neq_ a (const_ one)
  c3 <- neq_ b (const_ one)
  assert =<< all_ [ c1, c2, c3 ]

instance (Arbitrary f, PrimeField f) => FactorM f Gen where
  factor n = do
    a <- arbitrary @f `suchThat` \a ->
      a /= one && a /= n
    let b = n / a
    pure $ Tuple a b

instance FactorM f Effect where
  factor _ = do
    throw "unhandled request: Factor"

spec :: forall f. Arbitrary f => PrimeField f => Proxy f -> Spec Unit
spec _ = describe "Factors Specs" do

  it "factors Circuit is Valid" $ do
    { constraints } <- liftEffect $
      compile
        (Proxy @(FieldElem f))
        (Proxy @Unit)
        factorsCircuit
    let solver = makeSolver (Proxy @(ConstraintSystem f)) factorsCircuit
    let gen = arbitrary `suchThat` \(FieldElem a) -> a /= zero && a /= one
    quickCheck $
      gen >>= \a ->
        ( makeAssertionSpec
            { constraints
            , solver
            , evalConstraint: evalR1CSConstraint
            , isValid: \(FieldElem _) -> Satisfied
            }
            a :: Gen Result
        )