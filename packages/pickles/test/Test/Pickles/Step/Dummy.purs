module Test.Pickles.Step.Dummy
  ( spec
  ) where

-- | Tests for dummy proof generation used in Pickles bootstrapping.

import Prelude

import Data.Array as Array
import Data.Maybe (fromJust)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.Step.Dummy (dummyBulletproofChallenges, dummyDeferredValues, dummyPlonkMinimal, dummyScalarChallenge, dummyUnfinalizedProof)
import Pickles.Step.Types (BulletproofChallenges, DeferredValues, PlonkMinimal, ScalarChallenge, UnfinalizedProof)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.DSL as SizedF
import Snarky.Curves.Vesta as Vesta
import Snarky.Types.Shifted (Type1(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

-- | Step circuit operates on Vesta.ScalarField (= Pallas.BaseField = Fp)
-- | It verifies Wrap proofs which use Pallas.ScalarField (= Vesta.BaseField = Fq)
-- | Since |Fq| < |Fp|, we use Type1 shifted values.
type StepField = Vesta.ScalarField

-- Helper to get a dummy scalar challenge for StepField
dummyScalarChallenge' :: ScalarChallenge (F StepField)
dummyScalarChallenge' = dummyScalarChallenge

-- Helper to get dummy bulletproof challenges for StepField
dummyBulletproofChallenges' :: BulletproofChallenges (F StepField)
dummyBulletproofChallenges' = dummyBulletproofChallenges

-- Helper to get dummy plonk minimal for StepField
dummyPlonkMinimal' :: PlonkMinimal (F StepField)
dummyPlonkMinimal' = dummyPlonkMinimal

-- Helper to get dummy deferred values for StepField
dummyDeferredValues' :: DeferredValues (F StepField) (Type1 (F StepField))
dummyDeferredValues' = dummyDeferredValues

-- Helper to get dummy unfinalized proof for StepField
dummyUnfinalizedProof'
  :: Proxy StepField
  -> UnfinalizedProof (F StepField) (Type1 (F StepField)) Boolean
dummyUnfinalizedProof' _ = dummyUnfinalizedProof

spec :: Spec Unit
spec = describe "Dummy values" do
  it "dummyScalarChallenge is zero" do
    let F x = SizedF.toField dummyScalarChallenge'
    x `shouldEqual` zero

  it "dummyBulletproofChallenges has 16 zero challenges" do
    let chals = dummyBulletproofChallenges'
    let arr = Vector.toUnfoldable chals :: Array _
    Array.length arr `shouldEqual` 16
    -- Check first challenge is zero
    let (F first) = SizedF.toField $ unsafePartial fromJust $ Array.head arr
    first `shouldEqual` zero

  it "dummyPlonkMinimal has zero challenges" do
    let p = dummyPlonkMinimal'
    let F alpha = SizedF.toField p.alpha
    let F beta = p.beta
    let F gamma = p.gamma
    let F zeta = SizedF.toField p.zeta
    alpha `shouldEqual` zero
    beta `shouldEqual` zero
    gamma `shouldEqual` zero
    zeta `shouldEqual` zero

  it "dummyDeferredValues has zero values" do
    let d = dummyDeferredValues'
    let Type1 (F cip) = d.combinedInnerProduct
    let Type1 (F b) = d.b
    cip `shouldEqual` zero
    b `shouldEqual` zero

  it "dummyUnfinalizedProof has shouldFinalize = false" do
    let proof = dummyUnfinalizedProof' (Proxy :: Proxy StepField)
    proof.shouldFinalize `shouldEqual` false
