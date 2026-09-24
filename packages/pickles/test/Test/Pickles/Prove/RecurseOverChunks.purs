-- | Recursion over a chunked proof: `chunks2Rule` compiled at
-- | `stepChunks = 2`, then a second system whose one rule takes a
-- | proof of it as an `External` prev that must verify.
-- |
-- | The second system's step circuit finalizes the two-chunk step
-- | proof's deferred values: the one test in which the step
-- | finalize-other-proof reads evaluations of more than one chunk.
module Test.Pickles.Prove.RecurseOverChunks
  ( spec
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (Tuple1, tuple1, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Node.Process (lookupEnv)
import Pickles (BranchProver(..), PrevSlot(..), PrevStatement(..), RulesCons, RulesNil, Slot, SlotWrapKey(..), StatementIO(..), StepRule, compileMulti, mkRuleEntry, toPrevs, toVerifiable, verify)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.DSL (true_)
import Test.Pickles.Prove.Chunks2 (Chunks2Rules, chunks2Rule)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

type RecursePrevsSpec =
  Tuple1 (Slot 0 (StatementIO Unit Unit))

-- | One prev, a `Chunks2` proof, which must verify.
recurseRule :: StepRule RecursePrevsSpec Unit Unit Unit Unit
recurseRule _ _ = pure
  { prevs: toPrevs $
      PrevStatement { publicInput: StatementIO { input: unit, output: unit }, proofMustVerify: true_ }
        /\ unit
  , publicOutput: unit
  }

-- | Carrier for the single `recurseRule`, at width 1.
type RecurseRules =
  RulesCons 1
    RecursePrevsSpec
    RulesNil

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.RecurseOverChunks" do
  it "a step circuit finalizes a chunks=2 step proof, end-to-end verify" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/RecurseOverChunks.json")

    chunks2Entry <- liftEffect $ mkRuleEntry @Unit chunks2Rule Vector.nil

    logInfo "[RecurseOverChunks] compiling chunks2…"
    chunks2 <- withSpan "[RecurseOverChunks] compile chunks2" $ liftEffect $ compileMulti
      @Chunks2Rules
      @Unit
      @2
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Just 14
      , proofCache: cache
      , lagrangeCache: Just lagrangeCache
      }
      (tuple1 chunks2Entry)

    let BranchProver chunks2Prover = fst chunks2.provers
    logInfo "[RecurseOverChunks] proving chunks2"
    eChunks2Cp <- withSpan "[RecurseOverChunks] prove chunks2" $ liftEffect $ chunks2Prover noAdvice
      { appInput: unit, prevs: unit }
    chunks2Cp <- case eChunks2Cp of
      Left e -> liftEffect $ Exc.throw ("chunks2Prover: " <> show e)
      Right p -> pure p
    verify chunks2.verifier (toVerifiable chunks2Cp) `shouldEqual` true

    recurseEntry <- liftEffect $ mkRuleEntry @Unit
      recurseRule
      (External chunks2.tagData :< Vector.nil)

    logInfo "[RecurseOverChunks] compiling recurse…"
    recurse <- withSpan "[RecurseOverChunks] compile recurse" $ liftEffect $ compileMulti
      @RecurseRules
      @Unit
      @1
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: cache
      , lagrangeCache: Just lagrangeCache
      }
      (tuple1 recurseEntry)

    let BranchProver recurseProver = fst recurse.provers
    logInfo "[RecurseOverChunks] proving recurse"
    eRecurseCp <- withSpan "[RecurseOverChunks] prove recurse" $ liftEffect $ recurseProver noAdvice
      { appInput: unit
      , prevs: tuple1 (InductivePrev chunks2Cp chunks2.tag)
      }
    case eRecurseCp of
      Left e -> liftEffect $ Exc.throw ("recurseProver: " <> show e)
      Right recurseCp -> do
        logInfo "[RecurseOverChunks] verifying proof…"
        verify recurse.verifier (toVerifiable recurseCp) `shouldEqual` true
        logInfo "[RecurseOverChunks] verification complete"
