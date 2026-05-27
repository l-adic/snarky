module Test.Snarky.Circuit.Schnorr.Verify
  ( spec
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Int as Int
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Simple.JSON (readJSON)
import Snarky.Backend.Kimchi.Impl.Vesta (vestaCrsCreate)
import Snarky.Backend.Kimchi.Proof (pallasProofFromSerdeJson, pallasVerifierIndexFromSerdeJson, verifyOpeningProof)
import Snarky.Curves.Class (fromHexLe)
import Snarky.Curves.Pallas as Pallas
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

fixtureDir :: String
fixtureDir = "packages/schnorr/test/fixtures/schnorr_signature_proof"

readFile :: String -> Aff String
readFile path = liftEffect do
  buf <- FS.readFile path
  Buffer.toString UTF8 buf

spec :: Spec Unit
spec = describe "Snarky.Circuit.Schnorr.Verify (kimchi-only fixture)" do

  it "verifies the OCaml-emitted Schnorr signature proof" do
    -- Load fixture files written by
    -- `mina/src/lib/crypto/pickles/dump_schnorr_signature_proof.exe`.
    vkJson <- readFile (fixtureDir <> "/vk.serde.json")
    proofJson <- readFile (fixtureDir <> "/proof.serde.json")
    publicInputJson <- readFile (fixtureDir <> "/public_input.json")

    -- Parse the 6-element LE-hex public-input array (pk_x, pk_y, r, s,
    -- message[0], boolean output = 1).
    publicInputHex :: Array String <- case readJSON publicInputJson of
      Right xs -> pure xs
      Left e -> liftEffect $ throw $
        "parse public_input.json: " <> show e
    let
      publicInput :: Array Pallas.BaseField
      publicInput = map fromHexLe publicInputHex

    -- Reconstruct the step-side Vesta SRS (the OCaml dumper uses the
    -- default Tick URS, which is 2^16 = `Pickles.Backend.Tick`'s
    -- `max_poly_size`). The deserialized VK re-attaches this SRS;
    -- without it the verifier crashes on `lagrange_basis` lookup.
    let crs = vestaCrsCreate (Int.pow 2 16)

    -- Reattach VK + proof from JSON via the kimchi-napi serde codecs.
    let verifierIndex = pallasVerifierIndexFromSerdeJson vkJson crs
    let proof = pallasProofFromSerdeJson proofJson

    -- Inject the public input and verify.
    let ok = verifyOpeningProof verifierIndex { proof, publicInput }
    ok `shouldEqual` true
