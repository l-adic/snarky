-- | Round-trip validation for the OCaml-emitted side-loaded child fixture
-- | at `packages/pickles/test/fixtures/sideload_main_child/`.
module Test.Pickles.Sideload.RoundTripMainChildSpec
  ( spec
  ) where

import Prelude

import Effect.Aff (Aff)
import Pickles.Sideload.FFI (vestaVerifierIndexToSerdeJson)
import Pickles.Types (StepField)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.Sideload.Loader (loadNrrFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Sideload.MainChild roundtrip" do
  it "loads + parses + round-trips VK byte-identical" \_ -> do
    fixture <- loadNrrFixture
      "packages/pickles/test/fixtures/sideload_main_child"
    let reSerializedVk = vestaVerifierIndexToSerdeJson fixture.vk
    reSerializedVk `shouldEqual` fixture.vkJson
    -- The side-loaded child's public INPUT is `Field.Constant.zero`
    -- (per `dump_side_loaded_main.ml:103`: `step Field.Constant.zero`).
    fixture.statement `shouldEqual` (fromInt 0 :: StepField)
