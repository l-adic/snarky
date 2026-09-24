-- | The simplest pickles rule: no prevs, unit input, constant output
-- | `0`. One `compileMulti` call, one prove, one verify — the smallest
-- | end-to-end path through the system.
-- |
-- | The proof must verify and must stop verifying once its application
-- | state is altered, so a verifier that failed to bind the state to
-- | the step-message digest would fail here.
-- |
-- | `nrrRule` is exported for the specs that need a real proof of it to
-- | build on.
module Test.Pickles.Prove.NoRecursionReturn
  ( NrrRules
  , nrrRule
  , spec
  ) where

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
import Pickles (BranchProver(..), RulesCons, RulesNil, StepField, StepRule, compileMulti, mkRuleEntry, toPrevs, toVerifiable, verify)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.DSL (F, FVar, const_)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | Returns the constant zero, with no prevs and nothing asserted.
nrrRule :: StepRule Unit Unit Unit (F StepField) (FVar StepField)
nrrRule _ _ = pure
  { prevs: toPrevs unit
  , publicOutput: const_ zero
  }

-- | Carrier for the single `nrrRule`, at width 0 with no prevs.
type NrrRules =
  RulesCons 0 Unit
    RulesNil

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.NoRecursionReturn" do
  it "compileMulti + prover.step end-to-end verify returns true" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/NoRecursionReturn.json")

    nrrEntry <- liftEffect $ mkRuleEntry @0 @(F StepField) nrrRule Vector.nil

    let rules = tuple1 nrrEntry

    logInfo "[NoRecursionReturn] compiling…"
    output <- withSpan "[NoRecursionReturn] compile" $ liftEffect $ compileMulti
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
    logInfo "[NoRecursionReturn] proving"
    eResult <- withSpan "[NoRecursionReturn] prove" $ liftEffect $ nrrProver noAdvice
      { appInput: unit, prevs: unit }
    case eResult of
      Left e -> liftEffect $ Exc.throw ("nrrProver: " <> show e)
      Right compiledProof -> do
        logInfo "[NoRecursionReturn] verifying proof…"
        verify output.verifier (toVerifiable compiledProof) `shouldEqual` true
        -- The verifier binds the proof to the claimed application state
        -- through the recomputed step-message digest.
        let vp = toVerifiable compiledProof
        verify output.verifier (vp { appState = map (add one) vp.appState }) `shouldEqual` false
        logInfo "[NoRecursionReturn] verification complete"
