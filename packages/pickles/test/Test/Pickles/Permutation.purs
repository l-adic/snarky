module Test.Pickles.Permutation where

-- | Tests for the permutation argument circuit.
-- | Verifies that the in-circuit computation of permScalar matches
-- | the field-level reference computation.

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Vector as Vector
import Pickles.PlonkChecks.Permutation (PermutationInput, permContribution, permContributionCircuit, permScalar, permScalarCircuit)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class HasEndo, class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Test.Snarky.Circuit.Utils (TestConfig, circuitTest', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

kimchiTestConfig :: forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)
kimchiTestConfig = { checker: eval, postCondition: Kimchi.postCondition, initState: Kimchi.initialState }

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

-- | Generate PermutationInput avoiding division by zero.
-- | The boundary quotient denominator is (zeta - omegaToMinusZkRows) * (zeta - 1),
-- | so we need zeta ≠ omegaToMinusZkRows and zeta ≠ 1.
genPermutationInputNonZeroDenom :: forall f. PrimeField f => Gen (PermutationInput (F f))
genPermutationInputNonZeroDenom =
  genPermutationInput `suchThat` \input ->
    input.zeta /= input.omegaToMinusZkRows && input.zeta /= one

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
      circuit'
        :: forall t
         . CircuitM f (KimchiConstraint f) t Identity
        => PermutationInput (FVar f)
        -> Snarky (KimchiConstraint f) t Identity (FVar f)
      circuit' = permScalarCircuit
    void $ circuitTest' @f 1
      kimchiTestConfig
      ( NEA.singleton
          { testFunction: satisfied (permScalar :: PermutationInput (F f) -> F f)
          , gen: genPermutationInput :: Gen (PermutationInput (F f))
          }
      )
      circuit'

  it "permContributionCircuit matches permContribution" do
    let
      circuit'
        :: forall t
         . CircuitM f (KimchiConstraint f) t Identity
        => PermutationInput (FVar f)
        -> Snarky (KimchiConstraint f) t Identity (FVar f)
      circuit' = permContributionCircuit
    void $ circuitTest' @f 1
      kimchiTestConfig
      ( NEA.singleton
          { testFunction: satisfied (permContribution :: PermutationInput (F f) -> F f)
          , gen: genPermutationInputNonZeroDenom :: Gen (PermutationInput (F f))
          }
      )
      circuit'
