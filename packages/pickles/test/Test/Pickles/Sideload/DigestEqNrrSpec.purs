-- | `compileMulti` must produce, for `nrrRule`, the same kimchi
-- | `VerifierIndex` that the OCaml compile produced for the same rule.
-- |
-- | The two wrap VKs are compared through the full-VK JSON key of
-- | `Snarky.Backend.Kimchi.ProofCache`, which covers every stable
-- | `VerifierIndex` field — domain, evals, shifts, `max_poly_size`,
-- | public, `prev_challenges`, `zk_rows` — so equal keys mean
-- | bit-equivalent VKs. `RoundTripNrrSpec` only pins the codec on one
-- | JSON; this pins the compile itself.
module Test.Pickles.Sideload.DigestEqNrrSpec (spec) where

import Prelude

import Colog (LoggerT, Message, withSpan)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (tuple1)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Pickles (RuleEntry, StepField, compileMulti, mkRuleEntry)
import Snarky.Backend.Advice (noAdvice)
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
  body { pallasSrs, vestaSrs, lagrangeCache } = do
    nrrEntry :: RuleEntry _ _ _ _ Unit _ _ _ <-
      liftEffect $ mkRuleEntry @0 @(F StepField) nrrRule Vector.nil
    let rules = tuple1 nrrEntry
    output <- withSpan "[DigestEqNrr] compile" $ liftEffect $ compileMulti
      @NrrRules
      @(F StepField)
      @1
      noAdvice
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: Nothing
      , lagrangeCache: Just lagrangeCache
      }
      rules

    -- The reference wrap VK comes from the dumped serde JSON.
    fixture <- liftAff $ loadFixture { decodeStatement: decodeHex, statementToFields: \f -> [ f ] } { pallasSrs, vestaSrs }
      "packages/pickles/test/fixtures/sideload/nrr"

    let psKey = vestaVerifierIndexJsonKey output.verifier.wrapVK
    let ocamlKey = vestaVerifierIndexJsonKey fixture.vk
    psKey `shouldEqual` ocamlKey
