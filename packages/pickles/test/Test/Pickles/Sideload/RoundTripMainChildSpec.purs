-- | Round-trip validation for the OCaml-emitted side-loaded child fixture
-- | at `packages/pickles/test/fixtures/sideload_main_child/`.
-- |
-- | DEFERRED — see `VerifyNrrSpec` for the explanation. Restore by
-- | swapping `pending` for `it "<name>" _roundTripMainChildBody` once
-- | the slice 3.5 sideload-serde port lands.
module Test.Pickles.Sideload.RoundTripMainChildSpec
  ( spec
  -- Preserved test body; restore by swapping `pending` for
  -- `it "<name>" _roundTripMainChildBody` once the deferred work lands.
  , _roundTripMainChildBody
  ) where

import Prelude

import Colog (LoggerT, Message)
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Pickles (StepField)
import Pickles.Sideload (vestaVerifierIndexToSerdeJson)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Pickles.Sideload.Loader (OcamlProof(..), loadNrrFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Sideload.MainChild roundtrip" do
  it "loads + parses + round-trips VK byte-identical" (liftAff <<< _roundTripMainChildBody)

_roundTripMainChildBody :: SharedSrs -> Aff Unit
_roundTripMainChildBody { pallasSrs, vestaSrs } = do
  fixture <- loadNrrFixture { pallasSrs, vestaSrs }
    "packages/pickles/test/fixtures/sideload_main_child"
  let
    reSerializedVk = vestaVerifierIndexToSerdeJson fixture.vk
    OcamlProof p = fixture.ocamlProof
  reSerializedVk `shouldEqual` fixture.vkJson
  -- The side-loaded child's public input is `StepField.Constant.zero`.
  p.statement `shouldEqual` (fromInt 0 :: StepField)
