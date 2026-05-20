-- | OCaml ↔ PureScript NRR VK compatibility test.
-- |
-- | Compiles the NRR rule on the PureScript side via `compileMulti` and
-- | loads the OCaml-emitted NRR fixture's wrap VK, then compares the two
-- | via the full-VK JSON key used by `Pickles.ProofCache` (covers every
-- | stable kimchi `VerifierIndex` field — domain, evals, shifts,
-- | max_poly_size, public, prev_challenges, zk_rows). Stringwise
-- | equality of the JSON key implies bit-equivalent VKs at the kimchi
-- | level — the same byte-equality guarantee the prior `VerifierIndex
-- | .digest` Poseidon sponge gave, without needing a host-side sponge port.
-- |
-- | This is a stronger compatibility check than the byte-identity round-trip
-- | in `RoundTripNrrSpec`: that one only verifies that we can round-trip a
-- | given JSON; this one verifies that PS's `compileMulti` produces the
-- | same kimchi VerifierIndex that OCaml's `Pickles.compile_promise` does
-- | for the same rule.
-- |
-- | DEFERRED — the OCaml-side VK comes from `loadNrrFixture`, which
-- | routes through `Pickles.Sideload.FFI`'s snarky-crypto-backed serde.
-- | After the kimchi-napi migration the External tags don't match, so
-- | loading fails with "Failed to get external value" before the
-- | comparison runs. Restore by swapping `pending` for
-- | `it "<name>" _digestEqNrrBody` once the slice 3.5 sideload-serde
-- | port lands. The PS-side `compileMulti` half of this test is
-- | unaffected and ready.
module Test.Pickles.Sideload.DigestEqNrrSpec
  ( spec
  -- Preserved test body; restore by swapping `pending` for
  -- `it "<name>" _digestEqNrrBody` once the deferred work lands.
  , _digestEqNrrBody
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (tuple1)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles (NoSlots, StepField, compileMulti, mkRuleEntry)
import Pickles.ProofFFI (vestaVerifierIndexJsonKey)
import Snarky.Circuit.DSL (F)
import Test.Pickles.Prove.NoRecursionReturn (NrrRules, nrrRule)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Pickles.Sideload.Loader (loadNrrFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff SharedSrs Aff Unit
spec = describe "Pickles.Sideload.NRR VK equality" do
  it "PS compileMulti VK == OCaml compile VK (full-JSON key)" _digestEqNrrBody

_digestEqNrrBody :: SharedSrs -> Aff Unit
_digestEqNrrBody { pallasSrs, vestaSrs } = do
  -- PureScript-side compile: produce the wrap VK for NRR.
  nrrEntry <- liftEffect $ mkRuleEntry @0 @(F StepField) @Unit @1 @1 nrrRule unit
  let rules = tuple1 nrrEntry
  output <- liftEffect $ compileMulti
    @NrrRules
    @(F StepField)
    @Unit
    @NoSlots
    @1
    { srs: { vestaSrs, pallasSrs }
    , debug: false
    , wrapDomainOverride: Nothing
    , proofCache: Nothing
    }
    rules

  -- OCaml-side fixture: load the wrap VK from the dumped serde JSON.
  fixture <- loadNrrFixture { pallasSrs, vestaSrs } "packages/pickles/test/fixtures/sideload/nrr"

  -- Compare full-VK JSON keys. `vestaVerifierIndexJsonKey` serializes
  -- every stable kimchi `VerifierIndex` field (domain, evals, shifts,
  -- max_poly_size, public, prev_challenges, zk_rows). String equality
  -- ⇒ bit-equivalent VKs at the kimchi level.
  let psKey = vestaVerifierIndexJsonKey output.verifier.wrapVK
  let ocamlKey = vestaVerifierIndexJsonKey fixture.vk
  psKey `shouldEqual` ocamlKey
