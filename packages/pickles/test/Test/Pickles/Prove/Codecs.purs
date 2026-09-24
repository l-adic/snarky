-- | `Pickles.Prove.Codecs` out of circuit: a real proof and its
-- | `Verifier` both go through JSON, and the decoded proof must verify
-- | against the decoded verifier.
-- |
-- | That covers the wrap proof and wrap VK through the Rust serde
-- | codecs, the carried statement skeleton through the simple-json leaf
-- | codecs, and the data that is rebuilt rather than serialized: the
-- | verifier's linearization constant, and the SRSes handed to
-- | `decodeVerifier`.
module Test.Pickles.Prove.Codecs (spec) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (tuple1)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Node.Process (lookupEnv)
import Pickles (BranchProver(..), StepField, compileMulti, mkRuleEntry, toVerifiable, verify)
import Pickles.Prove.Codecs (decodeVerifiableProof, decodeVerifier, encodeVerifiableProof, encodeVerifier)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.DSL (F)
import Test.Pickles.Prove.NoRecursionReturn (NrrRules, nrrRule)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.Codecs" do
  it "serialize -> deserialize -> verify a pickles wrap proof + verifier"
    \{ pallasSrs, vestaSrs, lagrangeCache } -> do
      cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR"
        <#> map \dir -> mkProofCache (dir <> "/Codecs.json")

      nrrEntry <- liftEffect $ mkRuleEntry @0 @(F StepField) nrrRule Vector.nil
      let rules = tuple1 nrrEntry

      logInfo "[Codecs] compiling…"
      output <- withSpan "[Codecs] compile" $ liftEffect $ compileMulti
        @NrrRules
        @(F StepField)
        @1
        { srs: { vestaSrs, pallasSrs }
        , debug: false
        , wrapDomainOverride: Nothing
        , proofCache: cache
        , lagrangeCache: Just lagrangeCache
        }
        rules

      let BranchProver nrrProver = fst output.provers
      logInfo "[Codecs] proving"
      eResult <- withSpan "[Codecs] prove" $ liftEffect $ nrrProver noAdvice
        { appInput: unit, prevs: unit }
      case eResult of
        Left e -> liftEffect $ Exc.throw ("Codecs prover: " <> show e)
        Right compiledProof -> do
          let vp = toVerifiable compiledProof

          -- The proof verifies before any serialization.
          verify output.verifier vp `shouldEqual` true

          let proofJson = encodeVerifiableProof vp
          case decodeVerifiableProof proofJson of
            Left errs -> liftEffect $ Exc.throw ("decodeVerifiableProof: " <> show errs)
            Right vp' -> do
              -- Re-encoding the decode reproduces the JSON exactly.
              encodeVerifiableProof vp' `shouldEqual` proofJson

              -- The verifier's SRSes are supplied on decode rather than
              -- embedded, and its linearization is reconstructed.
              let verifierJson = encodeVerifier output.verifier
              case decodeVerifier { pallasSrs, vestaSrs } verifierJson of
                Left errs -> liftEffect $ Exc.throw ("decodeVerifier: " <> show errs)
                Right verifier' -> do
                  logInfo "[Codecs] verifying round-tripped proof against round-tripped verifier…"
                  verify verifier' vp' `shouldEqual` true
                  logInfo "[Codecs] round-trip verification complete"
