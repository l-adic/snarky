module Test.Snarky.Circuit.Groth16 (spec) where

import Prelude

import Control.Monad.Except (mapExceptT, runExceptT, throwError)
import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (error, throw)
import Snarky.Backend.Builder (initialState)
import Snarky.Backend.Compile (SolverT, compile, makeSolver)
import Snarky.Backend.Groth16.Class (class Groth16, circuitIsSatisfiedBy, prove, setup, verify)
import Snarky.Backend.Groth16.Gate (makeGates, makeGatesWitness, satisfies)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, all_, assert_, const_, equals_, exists, mul_, neq_, read)
import Snarky.Constraint.Groth16 (R1CS, eval)
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, randomSampleOne, suchThat)
import Test.Snarky.Circuit as CircuitTests
import Test.Snarky.Circuit.Utils (nullPostCondition)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = do
  CircuitTests.spec (Proxy @BN254.ScalarField) (Proxy @(R1CS BN254.ScalarField)) eval nullPostCondition initialState
  factorsSpec (Proxy @BN254.G) (Proxy @BN254.ScalarField) (Proxy @(R1CS BN254.ScalarField)) "BN254"

--------------------------------------------------------------------------------

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

factorsSpec
  :: forall g f
   . Groth16 g f
  => PrimeField f
  => Proxy g
  -> Proxy f
  -> Proxy (R1CS f)
  -> String
  -> Spec Unit
factorsSpec (_ :: Proxy g) (_ :: Proxy f) pc name = describe (name <> " Factors Spec") do

  it (name <> " Groth16 Prove/Verify Flow") $ liftEffect $ do
    { constraints: cs, publicInputs } <-
      compile
        (Proxy @(F f))
        (Proxy @Unit)
        pc
        factorsCircuit
        initialState
    let
      gates = makeGates { publicInputs, constraints: cs }

      solver :: SolverT f (R1CS f) Gen (F f) Unit
      solver = makeSolver (Proxy @(R1CS f)) factorsCircuit

      gen :: Gen (F f)
      gen = arbitrary `suchThat` \a -> a /= zero && a /= one
      solve n = do
        Tuple _ assignments <- solver n
        makeGatesWitness { assignments, constraints: cs, publicInputs }

    k <- randomSampleOne gen
    runExceptT (mapExceptT randomSampleOne $ solve k) >>= case _ of
      Left e -> throwError $ error (show e)
      Right gatesWitness -> do
        let psSatisfies = satisfies gatesWitness gates
        psSatisfies `shouldEqual` true

        let rustSatisfies = circuitIsSatisfiedBy @g @f { gates, witness: gatesWitness }
        rustSatisfies `shouldEqual` true

        let { provingKey, verifyingKey } = setup @g @f { gates, seed: 42 }

        let
          proof = prove @g @f
            { provingKey
            , gates
            , witness: gatesWitness
            , seed: 54321
            }

          publicInputValues = Array.mapMaybe (\i -> Array.index gatesWitness i) gates.publicInputIndices

          verifyResult = verify @g @f
            { verifyingKey
            , proof
            , publicInputs: publicInputValues
            }

        verifyResult `shouldEqual` true