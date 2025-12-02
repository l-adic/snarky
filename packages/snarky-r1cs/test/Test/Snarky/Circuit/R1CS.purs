module Test.Snarky.Circuit.R1CS (spec) where

import Prelude

import Control.Monad.Except (mapExceptT, runExceptT)
import Control.Monad.Trans.Class (lift)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Class.Console (error)
import Effect.Exception (throw)
import Snarky.Backend.Bulletproof.Gate (makeGates, makeMulGates, makeWitness, satisfies)
import Snarky.Backend.Compile (SolverT, compile, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, all_, assert_, const_, equals_, exists, mul_, neq_, read)
import Snarky.Constraint.R1CS (R1CS, eval)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, randomSample, randomSampleOne, suchThat)
import Test.Snarky.Circuit as CircuitTests
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = do
  CircuitTests.spec (Proxy @Vesta.BaseField) (Proxy @(R1CS Vesta.BaseField)) eval
  factorsSpec (Proxy @Vesta.BaseField)

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

factorsSpec
  :: forall f
   . PrimeField f
  => Proxy f
  -> Spec Unit
factorsSpec _ = describe "Factors Spec" do

  it "factors Circuit is Valid" $ liftEffect $ do
    { constraints } <-
      compile
        (Proxy @(F f))
        (Proxy @Unit)
        factorsCircuit
    let
      gates = makeGates constraints
      mulGates = makeMulGates constraints

      solver :: SolverT f (R1CS f) Gen (F f) Unit
      solver = makeSolver (Proxy @(R1CS f)) factorsCircuit

      gen :: Gen (F f)
      gen = arbitrary `suchThat` \a -> a /= zero && a /= one
      solve n = do
        Tuple _ assignments <- solver n
        makeWitness { assignments, mulGates }
    ns <- randomSample gen
    for_ ns \n -> do
      runExceptT (mapExceptT randomSampleOne $ solve n) >>= case _ of
        Left e -> error $ show e
        Right witness -> satisfies witness gates `shouldEqual` true
