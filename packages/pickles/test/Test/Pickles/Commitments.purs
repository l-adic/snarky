module Test.Pickles.Commitments where

-- | Tests for the commitment batching circuits.
-- | Verifies that in-circuit computations match field-level reference implementations.

import Prelude

import Data.Vector as Vector
import Pickles.Commitments (CombinedInnerProductInput, NumEvals, combinedInnerProduct, combinedInnerProductCircuit)
import Pickles.Linearization.FFI (PointEval)
import Poseidon (class PoseidonField)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky)
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
