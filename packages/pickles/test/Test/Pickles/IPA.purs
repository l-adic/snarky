module Test.Pickles.IPA where

-- | Tests for IPA (Inner Product Argument) circuits.
-- | Verifies that in-circuit computations match field-level reference implementations.

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Vector as Vector
import Pickles.IPA (BPolyInput, ComputeBInput, bPoly, bPolyCircuit, computeB, computeBCircuit)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class HasEndo, class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: (forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)) -> Spec Unit
spec cfg = do
  describe "Pickles.IPA" do
    describe "Pallas" do
      ipaTests cfg (Proxy :: Proxy Pallas.BaseField)
    describe "Vesta" do
      ipaTests cfg (Proxy :: Proxy Vesta.BaseField)

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
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> Spec Unit
ipaTests cfg _ = do
  it "bPolyCircuit matches bPoly" do
    let
      circuit'
        :: forall t
         . CircuitM f (KimchiConstraint f) t Identity
        => BPolyInput TestChallengeSize (FVar f)
        -> Snarky (KimchiConstraint f) t Identity (FVar f)
      circuit' = bPolyCircuit

      -- Reference function: convert BPolyInput to bPoly call
      bPolyRef :: BPolyInput TestChallengeSize (F f) -> F f
      bPolyRef { challenges, x } = bPoly challenges x

    void $ circuitTest' @f
      cfg
      ( NEA.singleton
          { testFunction: satisfied bPolyRef
          , input: QuickCheck 1 (genBPolyInput :: Gen (BPolyInput TestChallengeSize (F f)))
          }
      )
      circuit'

  it "computeBCircuit matches computeB" do
    let
      circuit'
        :: forall t
         . CircuitM f (KimchiConstraint f) t Identity
        => ComputeBInput TestChallengeSize (FVar f) ()
        -> Snarky (KimchiConstraint f) t Identity (FVar f)
      circuit' = computeBCircuit

      -- Reference function: convert ComputeBInput to computeB call
      computeBRef :: ComputeBInput TestChallengeSize (F f) () -> F f
      computeBRef { challenges, zeta, zetaOmega, evalscale } =
        computeB challenges { zeta, zetaOmega, evalscale }

    void $ circuitTest' @f
      cfg
      ( NEA.singleton
          { testFunction: satisfied computeBRef
          , input: QuickCheck 1 (genComputeBInput :: Gen (ComputeBInput TestChallengeSize (F f) ()))
          }
      )
      circuit'
