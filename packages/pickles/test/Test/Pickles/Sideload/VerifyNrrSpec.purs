-- | `verify` must accept an OCaml-produced NRR wrap proof against an
-- | OCaml-produced VK, and reject it once the application state
-- | changes. Passing means the deferred values, message digests and
-- | evals were all decoded correctly from the fixture.
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
  it "verify rejects the same proof under a different application state" (liftAff <<< tampered)
  where
  load { pallasSrs, vestaSrs } =
    loadFixture { decodeStatement: decodeHex, statementToFields: \f -> [ f ] } { pallasSrs, vestaSrs }
      "packages/pickles/test/fixtures/sideload/nrr"

  body :: SharedSrs -> Aff Unit
  body srs = do
    fixture <- load srs
    verify fixture.verifier fixture.verifiableProof `shouldEqual` true

  -- The step-message digest is recomputed from the claimed state, so a
  -- proof presented for any other state must fail the kimchi check.
  tampered :: SharedSrs -> Aff Unit
  tampered srs = do
    fixture <- load srs
    let vp = fixture.verifiableProof
    verify fixture.verifier (vp { appState = map (add one) vp.appState }) `shouldEqual` false
