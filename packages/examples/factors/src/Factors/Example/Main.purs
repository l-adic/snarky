module Factors.Example.Main where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Exception (throw)
import Snarky.Circuit.Compile (compile, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, CVar, exists, read, assert, all_, eq_, mul_, neq_, FieldElem(..), Variable, const_)
import Snarky.Circuit.TestUtils (ConstraintSystem, satisfied_)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
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

compileFactorsCircuit :: Effect { constraints :: ConstraintSystem Vesta.ScalarField, solver :: FieldElem Vesta.ScalarField -> Effect Unit }
compileFactorsCircuit = do
  { constraints } <- compile
    (Proxy @(FieldElem Vesta.ScalarField))
    (Proxy @Unit)
    factorsCircuit
  let solver = makeSolver (Proxy @(ConstraintSystem Vesta.ScalarField)) factorsCircuit
  pure { constraints, solver }

main :: Effect Unit
main = compileFactorsCircuit >>= \_ -> pure unit