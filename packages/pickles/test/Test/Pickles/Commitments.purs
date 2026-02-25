module Test.Pickles.Commitments where

-- | Tests for the commitment batching circuits.
-- | Verifies that in-circuit computations match field-level reference implementations.

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Vector as Vector
import Pickles.Commitments (CombinedInnerProductInput, NumEvals, combinedInnerProduct, combinedInnerProductCircuit)
import Pickles.Linearization.FFI (PointEval)
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
  describe "Pickles.Commitments" do
    describe "Pallas" do
      commitmentsTests cfg (Proxy :: Proxy Pallas.BaseField)
    describe "Vesta" do
      commitmentsTests cfg (Proxy :: Proxy Vesta.BaseField)

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
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> Spec Unit
commitmentsTests cfg _ = do
  it "combinedInnerProductCircuit matches combinedInnerProduct" do
    let
      circuit'
        :: forall t
         . CircuitM f (KimchiConstraint f) t Identity
        => CombinedInnerProductInput (FVar f)
        -> Snarky (KimchiConstraint f) t Identity (FVar f)
      circuit' = combinedInnerProductCircuit
    void $ circuitTest' @f
      cfg
      ( NEA.singleton
          { testFunction: satisfied (combinedInnerProduct :: CombinedInnerProductInput (F f) -> F f)
          , input: QuickCheck 1 (genCombinedInnerProductInput :: Gen (CombinedInnerProductInput (F f)))
          }
      )
      circuit'
