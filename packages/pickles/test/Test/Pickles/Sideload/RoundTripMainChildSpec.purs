-- | Round-trip validation for the OCaml-emitted side-loaded child fixture
-- | at `packages/pickles/test/fixtures/sideload_main_child/`.
module Test.Pickles.Sideload.RoundTripMainChildSpec
  ( spec
  ) where

import Prelude

import Effect.Aff (Aff)
import Pickles.Field (StepField)
import Pickles.Sideload.FFI (vestaVerifierIndexToSerdeJson)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.Sideload.Loader (OcamlProof(..), loadNrrFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Sideload.MainChild roundtrip" do
  it "loads + parses + round-trips VK byte-identical" \_ -> do
    fixture <- loadNrrFixture
      "packages/pickles/test/fixtures/sideload_main_child"
    let
      reSerializedVk = vestaVerifierIndexToSerdeJson fixture.vk
      OcamlProof p = fixture.ocamlProof
    reSerializedVk `shouldEqual` fixture.vkJson
    -- The side-loaded child's public input is `StepField.Constant.zero`.
    p.statement `shouldEqual` (fromInt 0 :: StepField)
