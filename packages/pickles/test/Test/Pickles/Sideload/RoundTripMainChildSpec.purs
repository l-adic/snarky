-- | Round-trip validation for the OCaml-emitted side-loaded child fixture
-- | at `packages/pickles/test/fixtures/sideload_main_child/`.
module Test.Pickles.Sideload.RoundTripMainChildSpec
  ( spec
  ) where

import Prelude

import Effect.Aff (Aff)
import Pickles (StepField)
import Pickles.Sideload (vestaVerifierIndexToSerdeJson)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Pickles.Sideload.Loader (OcamlProof(..), loadNrrFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff SharedSrs Aff Unit
spec = describe "Pickles.Sideload.MainChild roundtrip" do
  it "loads + parses + round-trips VK byte-identical" \{ pallasSrs, vestaSrs } -> do
    fixture <- loadNrrFixture { pallasSrs, vestaSrs }
      "packages/pickles/test/fixtures/sideload_main_child"
    let
      reSerializedVk = vestaVerifierIndexToSerdeJson fixture.vk
      OcamlProof p = fixture.ocamlProof
    reSerializedVk `shouldEqual` fixture.vkJson
    -- The side-loaded child's public input is `StepField.Constant.zero`.
    p.statement `shouldEqual` (fromInt 0 :: StepField)
