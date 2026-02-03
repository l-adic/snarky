module Test.Pickles.IPA where

-- | Tests for IPA (Inner Product Argument) circuits.
-- | Verifies that in-circuit computations match field-level reference implementations.

import Prelude

import Data.Vector as Vector
import Pickles.IPA (BPolyInput, ComputeBInput, bPoly, bPolyCircuit, computeB, computeBCircuit)
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
  describe "Pickles.IPA" do
    describe "Pallas" do
      ipaTests (Proxy :: Proxy Pallas.BaseField)
    describe "Vesta" do
      ipaTests (Proxy :: Proxy Vesta.BaseField)

-------------------------------------------------------------------------------
-- | Test size for bPoly / computeB
-------------------------------------------------------------------------------

-- | Use a small vector size for bPoly/computeB circuit tests.
-- | 8 is enough to exercise the algorithm without excessive constraint count.
type TestChallengeSize = 8

-------------------------------------------------------------------------------
-- | Generators
-------------------------------------------------------------------------------

-- | Generate arbitrary BPolyInput with TestChallengeSize challenges
genBPolyInput :: forall f. PrimeField f => Gen (BPolyInput TestChallengeSize (F f))
genBPolyInput = do
  challenges <- Vector.generator (Proxy @TestChallengeSize) arbitrary
  x <- arbitrary
  pure { challenges, x }

-- | Generate arbitrary ComputeBInput with TestChallengeSize challenges
genComputeBInput :: forall f. PrimeField f => Gen (ComputeBInput TestChallengeSize (F f) ())
genComputeBInput = do
  challenges <- Vector.generator (Proxy @TestChallengeSize) arbitrary
  zeta <- arbitrary
  zetaOmega <- arbitrary
  evalscale <- arbitrary
  pure { challenges, zeta, zetaOmega, evalscale }

-------------------------------------------------------------------------------
-- | Parameterized tests
-------------------------------------------------------------------------------

ipaTests
  :: forall f f'
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => KimchiVerify f f'
  => Proxy f
  -> Spec Unit
ipaTests _ = do
  it "bPolyCircuit matches bPoly" do
    let
      circuit
        :: forall t m
         . CircuitM f (KimchiConstraint f) t m
        => BPolyInput TestChallengeSize (FVar f)
        -> Snarky (KimchiConstraint f) t m (FVar f)
      circuit = bPolyCircuit

      solver = makeSolver (Proxy @(KimchiConstraint f)) circuit

      builtState = compilePure
        (Proxy @(BPolyInput TestChallengeSize (F f)))
        (Proxy @(F f))
        (Proxy @(KimchiConstraint f))
        circuit
        Kimchi.initialState

      -- Reference function: convert BPolyInput to bPoly call
      bPolyRef :: BPolyInput TestChallengeSize (F f) -> F f
      bPolyRef { challenges, x } = bPoly challenges x

    circuitSpecPure' 1
      { builtState
      , checker: Kimchi.eval
      , solver
      , testFunction: satisfied bPolyRef
      , postCondition: Kimchi.postCondition
      }
      (genBPolyInput :: Gen (BPolyInput TestChallengeSize (F f)))

  it "computeBCircuit matches computeB" do
    let
      circuit
        :: forall t m
         . CircuitM f (KimchiConstraint f) t m
        => ComputeBInput TestChallengeSize (FVar f) ()
        -> Snarky (KimchiConstraint f) t m (FVar f)
      circuit = computeBCircuit

      solver = makeSolver (Proxy @(KimchiConstraint f)) circuit

      builtState = compilePure
        (Proxy @(ComputeBInput TestChallengeSize (F f) ()))
        (Proxy @(F f))
        (Proxy @(KimchiConstraint f))
        circuit
        Kimchi.initialState

      -- Reference function: convert ComputeBInput to computeB call
      computeBRef :: ComputeBInput TestChallengeSize (F f) () -> F f
      computeBRef { challenges, zeta, zetaOmega, evalscale } =
        computeB challenges { zeta, zetaOmega, evalscale }

    circuitSpecPure' 1
      { builtState
      , checker: Kimchi.eval
      , solver
      , testFunction: satisfied computeBRef
      , postCondition: Kimchi.postCondition
      }
      (genComputeBInput :: Gen (ComputeBInput TestChallengeSize (F f) ()))
