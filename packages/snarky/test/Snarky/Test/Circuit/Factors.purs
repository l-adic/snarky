module Test.Snarky.Test.Circuit.Factors (spec) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.Compile (compile_, makeAssertionSpec)
import Snarky.Circuit.Constraint (R1CS, evalR1CSConstraint)
import Snarky.Circuit.DSL (class CircuitM, exists, publicInputs, read)
import Snarky.Circuit.DSL.Assert (assert)
import Snarky.Circuit.DSL.Boolean (all_)
import Snarky.Circuit.DSL.Field (eq_, mul_, neq_)
import Snarky.Circuit.Types (FieldElem(..), Variable)
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (Result, arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))

type Fr = Vesta.ScalarField

type ConstraintSystem = R1CS Fr Variable

class Monad m <= FactorM f m where
  factor :: f -> m (Tuple f f)

factorsCircuit
  :: forall t m
   . FactorM Fr m
  => CircuitM Fr ConstraintSystem t m
  => t m Unit
factorsCircuit = do
  n <- publicInputs @Fr (Proxy @(FieldElem Fr))
  Tuple a b <- exists do
    FieldElem nVal <- read n
    Tuple a b <- lift $ factor @Fr nVal
    pure $ Tuple (FieldElem a) (FieldElem b)
  c1 <- mul_ a b >>= eq_ n
  c2 <- neq_ a (const_ one)
  c3 <- neq_ b (const_ one)
  assert =<< all_ [ c1, c2, c3 ]

instance FactorM Fr Gen where
  factor n = do
    a <- arbitrary @Fr `suchThat` \a ->
      a /= one && a /= n
    let b = n / a
    pure $ Tuple a b

instance FactorM Fr Effect where
  factor _ = do
    throw "unhandled request: Factor"

spec :: Spec Unit
spec = describe "Factors Specs" do

  it "factors Circuit is Valid" $ do
    { constraints } <- liftEffect $
      compile_ (Proxy @(FieldElem Fr)) factorsCircuit
    quickCheck $ do
      { solver } <- compile_ (Proxy @(FieldElem Fr)) factorsCircuit
      a <- arbitrary @(FieldElem Fr)
      ( makeAssertionSpec
          { constraints
          , solver
          , evalConstraint: evalR1CSConstraint
          , isValid: \(FieldElem _) -> true
          }
          a :: Gen Result
      )