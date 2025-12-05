module Factors.Example.Main where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Exception (throw)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, all_, assert_, const_, equals_, exists, mul_, neq_, readCVar)
import Snarky.Constraint.R1CS (R1CS)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)

class Monad m <= FactorM f m where
  factor :: F f -> m (Tuple (F f) (F f))

factorsCircuit
  :: forall t m f
   . FactorM f m
  => CircuitM f (R1CS f) t m
  => FVar f
  -> Snarky t m Unit
factorsCircuit n = do
  Tuple a b <- exists do
    nVal <- readCVar n
    lift $ factor nVal
  c1 <- equals_ n =<< mul_ a b
  c2 <- neq_ a (const_ one)
  c3 <- neq_ b (const_ one)
  assert_ =<< all_ [ c1, c2, c3 ]

instance (Arbitrary f, PrimeField f) => FactorM f Gen where
  factor n = do
    a <- arbitrary `suchThat` \a ->
      a /= one && a /= n
    let b = n / a
    pure $ Tuple a b

instance FactorM f Effect where
  factor _ =
    throw "unhandled request: Factor"