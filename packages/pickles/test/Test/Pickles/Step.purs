module Test.Pickles.Step
  ( spec
  ) where

-- | Tests for Step circuit types and dummy proof generation.
-- |
-- | These tests verify the bootstrapping mechanism for Pickles recursion.
-- | At the base case (Step0), we use dummy unfinalized proofs with
-- | `shouldFinalize = false` to satisfy the uniform circuit structure.

import Prelude

import Pickles.Types (StepField)
import Snarky.Constraint.Kimchi (KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Test.Pickles.Step.ChallengeDigest as ChallengeDigest
import Test.Pickles.Step.Circuit as Circuit
import Test.Pickles.Step.Dummy as Dummy
import Test.Pickles.Step.FinalizeOtherProof as FinalizeOtherProof
import Test.Snarky.Circuit.Utils (TestConfig)
import Test.Spec (Spec, describe)

spec :: TestConfig StepField (KimchiGate StepField) (AuxState StepField) -> Spec Unit
spec cfg = describe "Pickles.Step" do
  Dummy.spec
  Circuit.spec cfg
  ChallengeDigest.spec cfg
  FinalizeOtherProof.spec cfg
