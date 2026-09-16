-- | `RoundTripNrrSpec`'s three checks on a second fixture,
-- | `packages/pickles/test/fixtures/sideload_main_child/` — the
-- | no-recursion child of a side-loaded parent, whose public input is
-- | zero.
module Test.Pickles.Sideload.RoundTripMainChildSpec (spec) where

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
spec = describe "Pickles.Sideload.MainChild roundtrip" do
  it "VK byte-identity + VerifiableProof codec round-trip verifies" (liftAff <<< body)
  where
  body :: SharedSrs -> Aff Unit
  body { pallasSrs, vestaSrs } = do
    fixture <- loadFixture { decodeStatement: decodeHex, statementToFields: \f -> [ f ] } { pallasSrs, vestaSrs }
      "packages/pickles/test/fixtures/sideload_main_child"

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
    encodeVerifiableProof vp' `shouldEqual` proofJson
    verify verifier' vp' `shouldEqual` true
