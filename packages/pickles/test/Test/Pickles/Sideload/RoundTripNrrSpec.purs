-- | Round-trip validation for the OCaml-emitted NRR side-load fixture.
-- | Confirms:
-- |
-- | * `loadNrrFixture` parses the OCaml-emitted files without error.
-- | * The kimchi `VerifierIndex` re-serialises byte-identically via
-- |   Rust serde (same kimchi crate on both ends).
-- | * The NRR statement is `StepField.zero` (NRR's hard-coded
-- |   `public_output`).
-- | * The wire proof handle was constructed without crashing.
-- |
-- | Wire-proof byte-round-trip is intentionally NOT tested: the source
-- | of truth on the OCaml side is yojson (Pickles' hand-written
-- | shape), which encodes the same data as Rust serde but differs
-- | structurally.
module Test.Pickles.Sideload.RoundTripNrrSpec
  ( spec
  ) where

import Prelude

import Effect.Aff (Aff)
import Pickles (StepField)
import Pickles.Sideload (vestaVerifierIndexToSerdeJson)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.Sideload.Loader (OcamlProof(..), loadNrrFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Sideload.NRR roundtrip" do
  it "loads + parses + round-trips VK byte-identical" \_ -> do
    fixture <- loadNrrFixture "packages/pickles/test/fixtures/sideload/nrr"
    -- VK byte-identity round-trip: re-serialize the loaded handle and check
    -- it matches the original on-disk JSON.
    let
      reSerializedVk = vestaVerifierIndexToSerdeJson fixture.vk
      OcamlProof p = fixture.ocamlProof
    reSerializedVk `shouldEqual` fixture.vkJson
    -- NRR's public_output is hard-coded to `StepField.zero`.
    p.statement `shouldEqual` (fromInt 0 :: StepField)
