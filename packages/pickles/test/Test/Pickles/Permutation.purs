module Test.Pickles.Permutation where

-- | Tests for the permutation argument circuit.
-- | Verifies that the in-circuit computation of permScalar matches
-- | the field-level reference computation.

import Prelude

import Data.Newtype (unwrap, wrap)
import Data.Vector as Vector
import Pickles.PlonkChecks.Permutation (PermutationInput, permScalar, permScalarCircuit)
import Poseidon (class PoseidonField)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky)
import Snarky.Circuit.Types (F)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class HasEndo, class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = do
  describe "Pickles.Permutation" do
    describe "Pallas" do
      permutationTests (Proxy :: Proxy Pallas.BaseField)
    describe "Vesta" do
      permutationTests (Proxy :: Proxy Vesta.BaseField)

-------------------------------------------------------------------------------
-- | Reference functions
-- | Since F f has PrimeField instance, we can use the plain functions directly.
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- | Generator
-------------------------------------------------------------------------------

-- | Generate arbitrary PermutationInput (F f)
genPermutationInput :: forall f. PrimeField f => Gen (PermutationInput (F f))
genPermutationInput = do
  w <- Vector.generator (Proxy @7) arbitrary
  sigma <- Vector.generator (Proxy @6) arbitrary
  zZeta <- arbitrary
  zOmega <- arbitrary
  shifts <- Vector.generator (Proxy @7) arbitrary
  alpha <- arbitrary
  beta <- arbitrary
  gamma <- arbitrary
  zkPolynomial <- arbitrary
  zetaToNMinus1 <- arbitrary
  omegaToMinusZkRows <- arbitrary
  zeta <- arbitrary
  pure
    { w
    , sigma
    , z: { zeta: zZeta, omegaTimesZeta: zOmega }
    , shifts
    , alpha
    , beta
    , gamma
    , zkPolynomial
    , zetaToNMinus1
    , omegaToMinusZkRows
    , zeta
    }

-------------------------------------------------------------------------------
-- | Parameterized tests
-------------------------------------------------------------------------------

permutationTests
  :: forall f f'
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => KimchiVerify f f'
  => Proxy f
  -> Spec Unit
permutationTests _ = do
  it "permScalarCircuit matches permScalar" do
    let
      circuit
        :: forall t m
         . CircuitM f (KimchiConstraint f) t m
        => PermutationInput (FVar f)
        -> Snarky (KimchiConstraint f) t m (FVar f)
      circuit = permScalarCircuit

      solver = makeSolver (Proxy @(KimchiConstraint f)) circuit

      builtState = compilePure
        (Proxy @(PermutationInput (F f)))
        (Proxy @(F f))
        (Proxy @(KimchiConstraint f))
        circuit
        Kimchi.initialState

    circuitSpecPure' 1
      { builtState
      , checker: Kimchi.eval
      , solver
      , testFunction: satisfied (permScalar :: PermutationInput (F f) -> F f)
      , postCondition: Kimchi.postCondition
      }
      (genPermutationInput :: Gen (PermutationInput (F f)))
