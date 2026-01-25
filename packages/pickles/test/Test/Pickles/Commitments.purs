module Test.Pickles.Commitments where

-- | Tests for the commitment verification circuits.
-- | Verifies that in-circuit computations match field-level reference implementations.

import Prelude

import Data.Vector as Vector
import Pickles.Commitments (BPolyInput, CombinedInnerProductInput, ComputeBInput, NumEvals, bPoly, bPolyCircuit, combinedInnerProduct, combinedInnerProductCircuit, computeB, computeBCircuit)
import Pickles.Linearization.FFI (PointEval)
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
  describe "Pickles.Commitments" do
    describe "Pallas" do
      commitmentsTests (Proxy :: Proxy Pallas.BaseField)
    describe "Vesta" do
      commitmentsTests (Proxy :: Proxy Vesta.BaseField)

-------------------------------------------------------------------------------
-- | Test size for bPoly / computeB
-------------------------------------------------------------------------------

-- | Use a small vector size for bPoly/computeB circuit tests.
-- | 8 is enough to exercise the algorithm without excessive constraint count.
type TestChallengeSize = 8

-------------------------------------------------------------------------------
-- | Generators
-------------------------------------------------------------------------------

-- | Generate arbitrary PointEval
genPointEval :: forall f. PrimeField f => Gen (PointEval (F f))
genPointEval = do
  zeta <- arbitrary
  omegaTimesZeta <- arbitrary
  pure { zeta, omegaTimesZeta }

-- | Generate arbitrary CombinedInnerProductInput
genCombinedInnerProductInput :: forall f. PrimeField f => Gen (CombinedInnerProductInput (F f))
genCombinedInnerProductInput = do
  polyscale <- arbitrary
  evalscale <- arbitrary
  evals <- Vector.generator (Proxy @NumEvals) genPointEval
  pure { polyscale, evalscale, evals }

-- | Generate arbitrary BPolyInput with TestChallengeSize challenges
genBPolyInput :: forall f. PrimeField f => Gen (BPolyInput TestChallengeSize (F f))
genBPolyInput = do
  challenges <- Vector.generator (Proxy @TestChallengeSize) arbitrary
  x <- arbitrary
  pure { challenges, x }

-- | Generate arbitrary ComputeBInput with TestChallengeSize challenges
genComputeBInput :: forall f. PrimeField f => Gen (ComputeBInput TestChallengeSize (F f))
genComputeBInput = do
  challenges <- Vector.generator (Proxy @TestChallengeSize) arbitrary
  zeta <- arbitrary
  zetaOmega <- arbitrary
  evalscale <- arbitrary
  pure { challenges, zeta, zetaOmega, evalscale }

-------------------------------------------------------------------------------
-- | Parameterized tests
-------------------------------------------------------------------------------

commitmentsTests
  :: forall f f'
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => KimchiVerify f f'
  => Proxy f
  -> Spec Unit
commitmentsTests _ = do
  it "combinedInnerProductCircuit matches combinedInnerProduct" do
    let
      circuit
        :: forall t m
         . CircuitM f (KimchiConstraint f) t m
        => CombinedInnerProductInput (FVar f)
        -> Snarky (KimchiConstraint f) t m (FVar f)
      circuit = combinedInnerProductCircuit

      solver = makeSolver (Proxy @(KimchiConstraint f)) circuit

      builtState = compilePure
        (Proxy @(CombinedInnerProductInput (F f)))
        (Proxy @(F f))
        (Proxy @(KimchiConstraint f))
        circuit
        Kimchi.initialState

    circuitSpecPure' 1
      { builtState
      , checker: Kimchi.eval
      , solver
      , testFunction: satisfied (combinedInnerProduct :: CombinedInnerProductInput (F f) -> F f)
      , postCondition: Kimchi.postCondition
      }
      (genCombinedInnerProductInput :: Gen (CombinedInnerProductInput (F f)))

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
        => ComputeBInput TestChallengeSize (FVar f)
        -> Snarky (KimchiConstraint f) t m (FVar f)
      circuit = computeBCircuit

      solver = makeSolver (Proxy @(KimchiConstraint f)) circuit

      builtState = compilePure
        (Proxy @(ComputeBInput TestChallengeSize (F f)))
        (Proxy @(F f))
        (Proxy @(KimchiConstraint f))
        circuit
        Kimchi.initialState

      -- Reference function: convert ComputeBInput to computeB call
      computeBRef :: ComputeBInput TestChallengeSize (F f) -> F f
      computeBRef { challenges, zeta, zetaOmega, evalscale } =
        computeB challenges { zeta, zetaOmega, evalscale }

    circuitSpecPure' 1
      { builtState
      , checker: Kimchi.eval
      , solver
      , testFunction: satisfied computeBRef
      , postCondition: Kimchi.postCondition
      }
      (genComputeBInput :: Gen (ComputeBInput TestChallengeSize (F f)))
