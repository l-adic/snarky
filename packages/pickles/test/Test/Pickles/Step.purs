module Test.Pickles.Step
  ( spec
  ) where

-- | Tests for Step circuit types and dummy proof generation.
-- |
-- | These tests verify the bootstrapping mechanism for Pickles recursion.
-- | At the base case (Step0), we use dummy unfinalized proofs with
-- | `shouldFinalize = false` to satisfy the uniform circuit structure.

import Prelude

import Test.Pickles.Step.ChallengeDigest as ChallengeDigest
import Test.Pickles.Step.Circuit as Circuit
import Test.Pickles.Step.Dummy as Dummy
import Test.Spec (Spec, describe)

spec :: Spec Unit
spec = describe "Pickles.Step" do
  Dummy.spec
  Circuit.spec
  ChallengeDigest.spec
