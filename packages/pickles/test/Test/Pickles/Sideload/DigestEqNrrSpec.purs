-- | OCaml ↔ PureScript NRR VK compatibility test.
-- |
-- | Compiles the NRR rule on the PureScript side via `compileMulti` and
-- | loads the OCaml-emitted NRR fixture's wrap VK, then compares the two
-- | via the full-VK JSON key used by `Snarky.Backend.Kimchi.ProofCache` (covers every
-- | stable kimchi `VerifierIndex` field — domain, evals, shifts,
-- | max_poly_size, public, prev_challenges, zk_rows). Stringwise equality
-- | of the JSON key implies bit-equivalent VKs at the kimchi level.
-- |
-- | Stronger than the byte-identity round-trip in `RoundTripNrrSpec`: that
-- | one verifies we can round-trip a given JSON; this one verifies that
-- | PS's `compileMulti` produces the same kimchi `VerifierIndex` that
-- | OCaml's `Pickles.compile_promise` does for the same rule.
module Test.Pickles.Sideload.DigestEqNrrSpec (spec) where

import Prelude

import Colog (LoggerT, Message, withSpan)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (tuple1)
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Pickles (NoSlots, RuleEntry, StepField, compileMulti, mkRuleEntry)
import Run as Run
import Snarky.Backend.Kimchi.ProofCache (vestaVerifierIndexJsonKey)
import Snarky.Circuit.DSL (F)
import Test.Pickles.Prove.NoRecursionReturn (NrrRules, nrrRule)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Pickles.Sideload.Loader (decodeHex, loadFixture)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Sideload.NRR VK equality" do
  it "PS compileMulti VK == OCaml compile VK (full-JSON key)" body
  where
  body :: SharedSrs -> LoggerT Message Aff Unit
  body { pallasSrs, vestaSrs } = do
    -- PureScript-side compile: produce the wrap VK for NRR.
    nrrEntry :: RuleEntry _ _ _ _ _ Unit _ _ _ _ _ _ <-
      liftEffect $ mkRuleEntry @0 @(F StepField) @Unit @1 @1 nrrRule unit
    let rules = tuple1 nrrEntry
    output <- withSpan "[DigestEqNrr] compile" $ liftEffect $ Run.runBaseEffect $ compileMulti
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
    fixture <- liftAff $ loadFixture { decodeStatement: decodeHex, statementToFields: \f -> [ f ] } { pallasSrs, vestaSrs }
      "packages/pickles/test/fixtures/sideload/nrr"

    -- Compare full-VK JSON keys; string equality ⇒ bit-equivalent VKs.
    let psKey = vestaVerifierIndexJsonKey output.verifier.wrapVK
    let ocamlKey = vestaVerifierIndexJsonKey fixture.vk
    psKey `shouldEqual` ocamlKey
