-- | The OCaml-emitted NRR fixture in
-- | `packages/pickles/test/fixtures/sideload/nrr/`, from three angles:
-- |
-- |   * its kimchi `VerifierIndex` re-serializes byte-identically, so
-- |     the `kimchi-napi` serializer reproduces `vk.serde.json` exactly;
-- |   * its statement decodes to zero, the rule's constant output;
-- |   * its `VerifiableProof` and `Verifier` survive a JSON round trip
-- |     through `Pickles.Prove.Codecs`, and the decoded proof verifies.
-- |
-- | The codec is therefore exercised on externally produced values;
-- | `Test.Pickles.Prove.Codecs` only round-trips proofs made here.
module Test.Pickles.Sideload.RoundTripNrrSpec (spec) where

import Prelude

import Colog (LoggerT, Message)
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles (StepField, verify)
import Pickles.Prove.Codecs (decodeVerifiableProof, decodeVerifier, encodeVerifiableProof, encodeVerifier)
import Pickles.Sideload (vestaVerifierIndexToSerdeJson)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Pickles.Sideload.Loader (decodeHex, loadFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Sideload.NRR roundtrip" do
  it "VK byte-identity + VerifiableProof codec round-trip verifies" (liftAff <<< body)
  where
  body :: SharedSrs -> Aff Unit
  body { pallasSrs, vestaSrs } = do
    fixture <- loadFixture { decodeStatement: decodeHex, statementToFields: \f -> [ f ] } { pallasSrs, vestaSrs }
      "packages/pickles/test/fixtures/sideload/nrr"

    -- Re-serializing the loaded VK must reproduce the on-disk JSON.
    vestaVerifierIndexToSerdeJson fixture.vk `shouldEqual` fixture.vkJson

    fixture.statement `shouldEqual` (fromInt 0 :: StepField)

    let
      proofJson = encodeVerifiableProof fixture.verifiableProof
      verifierJson = encodeVerifier fixture.verifier
    vp' <- case decodeVerifiableProof proofJson of
      Right x -> pure x
      Left e -> liftEffect (Exc.throw ("decodeVerifiableProof: " <> show e))
    verifier' <- case decodeVerifier { pallasSrs, vestaSrs } verifierJson of
      Right x -> pure x
      Left e -> liftEffect (Exc.throw ("decodeVerifier: " <> show e))
    -- Re-encoding the decode reproduces the JSON exactly.
    encodeVerifiableProof vp' `shouldEqual` proofJson
    verify verifier' vp' `shouldEqual` true
