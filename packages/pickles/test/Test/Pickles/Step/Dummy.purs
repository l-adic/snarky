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
import Pickles.Verify.Types (BulletproofChallenges, PlonkMinimal, ScalarChallenge)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.DSL as SizedF
import Snarky.Circuit.Kimchi (Type2, fromShifted)
import Pickles.Types (WrapIPARounds)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | Step circuit operates on Vesta.ScalarField (= Pallas.BaseField = Fp)
-- | It verifies Wrap proofs which use Pallas.ScalarField (= Vesta.BaseField = Fq)
-- | Since |Fq| > |Fp|, we use Type2 shifted values.
type StepField = Vesta.ScalarField
type OtherField = Pallas.ScalarField

spec :: Spec Unit
spec = describe "Dummy values" do
  it "dummyScalarChallenge is zero" do
    let
      F x = SizedF.toField (dummyScalarChallenge :: ScalarChallenge (F StepField))
    x `shouldEqual` zero

  it "dummyBulletproofChallenges has correct number of challenges" do
    let
      chals :: BulletproofChallenges WrapIPARounds (F StepField)
      chals = dummyBulletproofChallenges @WrapIPARounds
      arr = Vector.toUnfoldable chals :: Array _
    Array.length arr `shouldEqual` 16
    -- Check first challenge is zero
    let (F first) = SizedF.toField $ unsafePartial fromJust $ Array.head arr
    first `shouldEqual` zero

  it "dummyPlonkMinimal has zero challenges" do
    let
      p :: PlonkMinimal (F StepField)
      p = dummyPlonkMinimal
      F alpha = SizedF.toField p.alpha
      F beta = SizedF.toField p.beta
      F gamma = SizedF.toField p.gamma
      F zeta = SizedF.toField p.zeta
    alpha `shouldEqual` zero
    beta `shouldEqual` zero
    gamma `shouldEqual` zero
    zeta `shouldEqual` zero

  it "dummyDeferredValues has one values (shifted one to avoid forbidden zero)" do
    let
      d = dummyDeferredValues @WrapIPARounds @StepField @OtherField @(Type2 (F StepField) Boolean)
      F cip = fromShifted d.combinedInnerProduct :: F OtherField
      F b = fromShifted d.b :: F OtherField
    cip `shouldEqual` one
    b `shouldEqual` one

  it "dummyUnfinalizedProof has shouldFinalize = false" do
    let
      proof = dummyUnfinalizedProof @WrapIPARounds @StepField @OtherField @(Type2 (F StepField) Boolean)
    proof.shouldFinalize `shouldEqual` false
