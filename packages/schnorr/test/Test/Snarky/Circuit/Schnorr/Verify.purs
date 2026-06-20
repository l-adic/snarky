module Test.Snarky.Circuit.Schnorr.Verify
  ( spec
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Foldable (for_)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Simple.JSON (readJSON)
import Snarky.Backend.Kimchi.Proof (pallasProofFromSerdeJson, pallasVerifierIndexFromSerdeJson, verifyOpeningProof)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Class (fromHexLe)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | The three proof fixtures emitted by
-- | `mina/src/lib/crypto/pickles/dump_schnorr_signature_proof.exe` — one
-- | per deterministic (sk, msg) case. Each compiles the production
-- | `Signature_lib.Schnorr.Chunked.Checked.verifies` (via
-- | `Dump_schnorr_circuit_lib.schnorr_verify_circuit`), signs with
-- | `Schnorr.Chunked.sign ~signature_kind:Mainnet`, and emits a kimchi
-- | proof. (The proofs share one VK — it's circuit- not input-dependent.)
fixtureDirs :: Array String
fixtureDirs =
  [ "packages/schnorr/test/fixtures/schnorr_signature_proof"
  , "packages/schnorr/test/fixtures/schnorr_signature_proof_2"
  , "packages/schnorr/test/fixtures/schnorr_signature_proof_3"
  ]

-- | Reattach the VK + proof from a fixture dir and full-verify against
-- | its 260-field public input ([pk.x, pk.y, r, s_bits[0..254], msg,
-- | output_bool]).
verifyAt :: CRS VestaG -> String -> Aff Unit
verifyAt crs dir = do
  vkJson <- liftEffect $ FS.readTextFile UTF8 (dir <> "/vk.serde.json")
  proofJson <- liftEffect $ FS.readTextFile UTF8 (dir <> "/proof.serde.json")
  publicInputJson <- liftEffect $ FS.readTextFile UTF8
    (dir <> "/public_input.json")
  publicInputHex :: Array String <- case readJSON publicInputJson of
    Right xs -> pure xs
    Left e -> liftEffect $ throw $
      "parse " <> dir <> "/public_input.json: " <> show e
  let
    publicInput = map fromHexLe publicInputHex :: Array Pallas.BaseField
    -- The deserialized VK re-attaches this SRS (the OCaml dumper's
    -- default Tick URS, 2^16); without it the verifier crashes on the
    -- `lagrange_basis` lookup.
    verifierIndex = pallasVerifierIndexFromSerdeJson vkJson crs
    proof = pallasProofFromSerdeJson proofJson
  verifyOpeningProof verifierIndex { proof, publicInput } `shouldEqual` true

-- | The shared input-independent SRS is built once in `Test.Schnorr.Main`
-- | through the on-disk cache (the same vesta-2^16 generators every other suite
-- | uses) and threaded in here.
spec :: CRS VestaG -> Spec Unit
spec crs = describe "Snarky.Circuit.Schnorr.Verify (kimchi-only fixtures)" do
  for_ fixtureDirs \dir ->
    it ("verifies the OCaml-emitted Schnorr signature proof: " <> dir)
      (verifyAt crs dir)
