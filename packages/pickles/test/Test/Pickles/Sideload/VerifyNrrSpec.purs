-- | End-to-end verify of an OCaml-produced NRR wrap proof: load the NRR
-- | fixture, then run the canonical `Pickles.Verify.verify` on the
-- | loader-assembled `Verifier` + `VerifiableProof`.
-- |
-- | Strongest cross-stack compatibility check: PS's verifier accepts an
-- | OCaml-produced wrap proof against an OCaml-produced VK, given correctly
-- | decoded deferred-values + message digests + evals.
module Test.Pickles.Sideload.VerifyNrrSpec (spec) where

import Prelude

import Colog (LoggerT, Message)
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Pickles (verify)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Pickles.Sideload.Loader (decodeHex, loadFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Sideload.NRR verify" do
  it "verify accepts the OCaml-produced NRR wrap proof" (liftAff <<< body)
  where
  body :: SharedSrs -> Aff Unit
  body { pallasSrs, vestaSrs } = do
    fixture <- loadFixture { decodeStatement: decodeHex, statementToFields: \f -> [ f ] } { pallasSrs, vestaSrs }
      "packages/pickles/test/fixtures/sideload/nrr"
    verify fixture.verifier fixture.verifiableProof `shouldEqual` true
