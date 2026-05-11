-- | End-to-end verify of an OCaml-produced NRR wrap proof. Loads the
-- | NRR fixture (`vk + kimchi proof + statement + wrapping`), builds
-- | a `Verifier`, and runs `verifyOcamlProof`. Asserts the result is
-- | `true`.
-- |
-- | Strongest cross-stack compatibility check: PS's verifier accepts
-- | an OCaml-produced wrap proof against an OCaml-produced VK, given
-- | correctly decoded deferred-values + message digests + AllEvals.
module Test.Pickles.Sideload.VerifyNrrSpec
  ( spec
  ) where

import Prelude
import Pickles (mkVerifier)

import Effect.Aff (Aff)
import Test.Pickles.Sideload.Loader (OcamlProof(..), loadNrrFixture, verifyOcamlProof)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Sideload.NRR verify" do
  it "verifyOcamlProof accepts the OCaml-produced NRR wrap proof" \_ -> do
    fixture <- loadNrrFixture "packages/pickles/test/fixtures/sideload/nrr"
    let
      OcamlProof p = fixture.ocamlProof
      verifier = mkVerifier
        { wrapVK: fixture.vk
        , vestaSrs: fixture.vestaSrs
        , stepDomainLog2: p.stepDomainLog2
        }
    verifyOcamlProof verifier fixture.ocamlProof `shouldEqual` true
