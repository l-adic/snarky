module Test.Snarky.Circuit.Factors (spec) where

import Prelude

import Data.Array.NonEmpty as NEA
import Effect (Effect)
import Run (Run)
import Run as Run
import Snarky.Backend.Builder (class CompileCircuit)
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Circuit.DSL (class BasicSystem, F, FVar, Snarky, all_, assert_, const_, equals_, exists, liftAdvice, mul_, neq_, read)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, randomSampleOne, suchThat)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTestM', satisfied_)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

-- | The advice effect: ask the environment to factor a field element. This is
-- | the Run replacement for the old `FactorM` advice CLASS over the base
-- | monad — the circuit carries it as an unknown effect in its row, and the
-- | test interprets it (prove time samples a factorization; compile time
-- | never runs witnesses, so the effect never fires).
data FactorF f a = Factor (F f) ({ a :: F f, b :: F f } -> a)

derive instance Functor (FactorF f)

type FACTOR f r = (factor :: FactorF f | r)

_factor :: Proxy "factor"
_factor = Proxy

factor :: forall f r. F f -> Run (FACTOR f + r) { a :: F f, b :: F f }
factor n = Run.lift _factor (Factor n identity)

-- | Interpret `FACTOR` into `Effect` by sampling a random factorization.
runFactor :: forall f. PrimeField f => Run (FACTOR f ()) ~> Effect
runFactor = Run.runRec $ Run.match
  { factor: \(Factor n k) -> k <$> randomSampleOne (genFactor n) }
  where
  genFactor :: F f -> Gen { a :: F f, b :: F f }
  genFactor n = do
    a <- arbitrary @(F f) `suchThat` \a -> a /= one && a /= n
    pure { a, b: n / a }

factorsCircuit
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> Snarky f c (FACTOR f + r) Unit
factorsCircuit n = do
  -- NOTE: no `lift` — the advice effect unifies straight into the witness row.
  { a, b } <- exists do
    nVal <- read n
    liftAdvice (factor nVal)
  c1 <- equals_ n =<< mul_ a b
  c2 <- neq_ a (const_ one)
  c3 <- neq_ b (const_ one)
  assert_ =<< all_ [ c1, c2, c3 ]

spec
  :: forall f c c' aux
   . CompileCircuit f c c' aux
  => SolveCircuit f c'
  => TestConfig f c aux
  -> Spec Unit
spec cfg = describe "Factors Specs" do

  it "factors Circuit is Valid" $ void $
    let
      gen :: Gen (F f)
      gen = arbitrary `suchThat` \a -> a /= zero && a /= one
    in
      circuitTestM' @f runFactor
        cfg
        (NEA.singleton { testFunction: satisfied_, input: QuickCheck 100 gen })
        factorsCircuit
