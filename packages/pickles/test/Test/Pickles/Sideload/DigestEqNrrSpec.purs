-- | OCaml ↔ PureScript NRR VK compatibility test.
-- |
-- | Compiles the NRR rule on the PureScript side via `compileMulti` and
-- | loads the OCaml-emitted NRR fixture's wrap VK, then compares the two
-- | via kimchi's `VerifierIndex.digest` (a Poseidon sponge hash over the
-- | VK's stable fields). If both sides produce the same digest, the
-- | underlying VKs are bit-equivalent at the kimchi level.
-- |
-- | This is a stronger compatibility check than the byte-identity round-trip
-- | in `RoundTripNrrSpec`: that one only verifies that we can round-trip a
-- | given JSON; this one verifies that PS's `compileMulti` produces the
-- | same kimchi VerifierIndex that OCaml's `Pickles.compile_promise` does
-- | for the same rule.
module Test.Pickles.Sideload.DigestEqNrrSpec
  ( spec
  ) where

import Prelude

import Data.Int.Bits as Int
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (tuple1)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles (NoSlots, StepField, compileMulti, mkRuleEntry)
import Pickles.ProofFFI (vestaVerifierIndexDigest)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F)
import Test.Pickles.Prove.NoRecursionReturn (NrrRules, nrrRule)
import Test.Pickles.Sideload.Loader (loadNrrFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Sideload.NRR digest equality" do
  it "PS compileMulti VK digest == OCaml compile VK digest" \_ -> do
    -- PureScript-side compile: produce the wrap VK for NRR.
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField
    nrrEntry <- liftEffect $ mkRuleEntry @0 @(F StepField) @Unit nrrRule unit
    let rules = tuple1 nrrEntry
    output <- liftEffect $ compileMulti
      @NrrRules
      @(F StepField)
      @Unit
      @NoSlots
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      }
      rules

    -- OCaml-side fixture: load the wrap VK from the dumped serde JSON.
    fixture <- loadNrrFixture "packages/pickles/test/fixtures/sideload/nrr"

    -- Compare digests. `vestaVerifierIndexDigest` calls kimchi's
    -- `VerifierIndex.digest::<VestaBaseSponge>()` under the hood, hashing
    -- the VK's stable fields via Poseidon in the OTHER curve's scalar field
    -- (= Fp = StepField for the wrap VK on Pallas).
    let psDigest = vestaVerifierIndexDigest output.verifier.wrapVK
    let ocamlDigest = vestaVerifierIndexDigest fixture.vk
    psDigest `shouldEqual` ocamlDigest
