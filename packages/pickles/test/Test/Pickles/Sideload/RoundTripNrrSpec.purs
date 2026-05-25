-- | Round-trip validation for the OCaml-emitted NRR side-load fixture
-- | (`packages/pickles/test/fixtures/sideload/nrr/`). Loads the
-- | OCaml-produced fixture, then checks:
-- |
-- |   * the kimchi `VerifierIndex` re-serialises byte-identically via Rust
-- |     serde — cross-stack serde determinism (OCaml's `vk.serde.json`
-- |     reproduced exactly by PS's `kimchi-napi` serializer);
-- |   * the NRR statement decodes to `StepField.zero` (NRR's hard-coded
-- |     `public_output`);
-- |   * the loaded `VerifiableProof` + `Verifier` survive a full JSON
-- |     round-trip through `Pickles.Prove.Codecs` and the decoded proof
-- |     still verifies. This exercises the codec against OCaml-SOURCED
-- |     values — `Test.Pickles.Prove.Codecs` only round-trips PS-produced
-- |     proofs.
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

    -- Cross-stack VK serde byte-identity: re-serialize the loaded VK and
    -- check it matches OCaml's on-disk JSON.
    vestaVerifierIndexToSerdeJson fixture.vk `shouldEqual` fixture.vkJson

    -- NRR's public_output is hard-coded to StepField.zero.
    fixture.statement `shouldEqual` (fromInt 0 :: StepField)

    -- Full codec round-trip on the OCaml-sourced proof + verifier, then
    -- verify the decoded proof against the decoded verifier.
    let
      proofJson = encodeVerifiableProof fixture.verifiableProof
      verifierJson = encodeVerifier fixture.verifier
    vp' <- case decodeVerifiableProof proofJson of
      Right x -> pure x
      Left e -> liftEffect (Exc.throw ("decodeVerifiableProof: " <> show e))
    verifier' <- case decodeVerifier { pallasSrs, vestaSrs } verifierJson of
      Right x -> pure x
      Left e -> liftEffect (Exc.throw ("decodeVerifier: " <> show e))
    -- Re-encoding the decoded proof yields identical JSON (faithful codec).
    encodeVerifiableProof vp' `shouldEqual` proofJson
    verify verifier' vp' `shouldEqual` true
