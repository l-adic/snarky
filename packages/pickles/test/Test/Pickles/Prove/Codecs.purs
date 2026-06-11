-- | End-to-end test for OUT-OF-CIRCUIT pickles-proof serialization:
-- | compile + prove a real (NRR) proof, project it to a `VerifiableProof`,
-- | round-trip BOTH the proof and the `Verifier` through JSON
-- | (`Pickles.Prove.Codecs`), and confirm the decoded proof still verifies
-- | against the decoded verifier.
-- |
-- | This exercises: the wrap kimchi proof + wrap VK through the Rust serde
-- | codecs; the carried statement skeleton through the simple-json leaf
-- | codecs; and the reconstructed-not-serialized data (the verifier's
-- | linearization constant + the SRSes supplied to `decodeVerifier`).
module Test.Pickles.Prove.Codecs (spec) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (tuple1)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Node.Process (lookupEnv)
import Pickles (BranchProver(..), NoSlots, StepField, compileMulti, mkRuleEntry, toVerifiable, verify)
import Pickles.Prove.Codecs (decodeVerifiableProof, decodeVerifier, encodeVerifiableProof, encodeVerifier)
import Run as Run
import Run.Except as Except
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.DSL (F)
import Test.Pickles.Prove.NoRecursionReturn (NrrRules, nrrRule)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.Codecs" do
  it "serialize -> deserialize -> verify a pickles wrap proof + verifier"
    \{ pallasSrs, vestaSrs } -> do
      cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR"
        <#> map \dir -> mkProofCache (dir <> "/Codecs.json")

      nrrEntry <- liftEffect $ mkRuleEntry @0 @(F StepField) @Unit @1 @1 nrrRule unit
      let rules = tuple1 nrrEntry

      logInfo "[Codecs] compiling…"
      output <- withSpan "[Codecs] compile" $ liftEffect $ Run.runBaseEffect $ compileMulti
        @NrrRules
        @(F StepField)
        @Unit
        @NoSlots
        @1
        { srs: { vestaSrs, pallasSrs }
        , debug: false
        , wrapDomainOverride: Nothing
        , proofCache: cache
        }
        rules

      let BranchProver nrrProver = fst output.provers
      logInfo "[Codecs] proving"
      eResult <- withSpan "[Codecs] prove" $ liftEffect $ Run.runBaseEffect $ Except.runExcept $ nrrProver
        { appInput: unit, prevs: unit, sideloadedVKs: unit }
      case eResult of
        Left e -> liftEffect $ Exc.throw ("Codecs prover: " <> show e)
        Right compiledProof -> do
          let vp = toVerifiable compiledProof

          -- Sanity: the proof verifies before any serialization.
          verify output.verifier vp `shouldEqual` true

          -- Round-trip the proof through JSON.
          let proofJson = encodeVerifiableProof vp
          case decodeVerifiableProof proofJson of
            Left errs -> liftEffect $ Exc.throw ("decodeVerifiableProof: " <> show errs)
            Right vp' -> do
              -- Re-encoding the decoded proof yields identical JSON
              -- (codec is a faithful round-trip).
              encodeVerifiableProof vp' `shouldEqual` proofJson

              -- Round-trip the verifier through JSON; the SRSes are supplied
              -- on decode (not embedded), the linearization is reconstructed.
              let verifierJson = encodeVerifier output.verifier
              case decodeVerifier { pallasSrs, vestaSrs } verifierJson of
                Left errs -> liftEffect $ Exc.throw ("decodeVerifier: " <> show errs)
                Right verifier' -> do
                  logInfo "[Codecs] verifying round-tripped proof against round-tripped verifier…"
                  verify verifier' vp' `shouldEqual` true
                  logInfo "[Codecs] round-trip verification complete"
