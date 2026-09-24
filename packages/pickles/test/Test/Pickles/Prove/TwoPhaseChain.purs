-- | The smallest multi-branch proof system: `makeZeroRule` (branch 0,
-- | no prevs, asserts `self = 0`) and `incrementRule` (branch 1, one
-- | self-prev, asserts `self = prev + 1`), sharing one wrap VK.
-- |
-- | The spec chains b0..b3 across both branches and discharges all four
-- | proofs in one `verifyBatch`, so it fails if the wrap circuit
-- | dispatches on the wrong branch or a proof's step domain is taken
-- | from another branch.
module Test.Pickles.Prove.TwoPhaseChain
  ( spec
  , makeZeroRule
  , incrementRule
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (Tuple1, tuple1, tuple2, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception as Exc
import Node.Process (lookupEnv)
import Pickles (BranchProver(..), PrevSlot(..), PrevStatement(..), Slot, SlotWrapKey(..), StatementIO(..), StepField, StepRule, compileMulti, mkRuleEntry, prevValues, toPrevs, toVerifiable, verifyBatch)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, assertEqual_, const_, exists, true_)
import Snarky.Curves.Class (fromInt) as Curves
import Test.Pickles.SerializeRoundTrip (mkWidthDummies, roundTripAndVerify)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

--------------------------------------------------------------------------------
-- Rule bodies
--------------------------------------------------------------------------------

-- | Branch 0: assert the public input is zero. No prevs.
makeZeroRule
  :: StepRule Unit
       (F StepField)
       (FVar StepField)
       Unit
       Unit
makeZeroRule _ self = do
  assertEqual_ self (const_ zero)
  pure
    { prevs: toPrevs unit
    , publicOutput: unit
    }

-- | Branch 1: assert the public input is one more than the prev's app
-- | state. The single `Self` prev slot resolves to either branch at
-- | proof time, which is the dispatch this fixture exercises.
incrementRule
  :: StepRule IncrementPrevsSpec
       (F StepField)
       (FVar StepField)
       Unit
       Unit
incrementRule getPrevStates self = do
  prev <- exists $ getPrevStates <#> prevValues <#> \(StatementIO { input } /\ _) -> input
  assertEqual_ self (CVar.add_ (const_ one) prev)
  pure
    -- Branch dispatch happens at the wrap layer, from `whichBranch`,
    -- so the prev is unconditionally verified here.
    { prevs: toPrevs $
        PrevStatement { publicInput: StatementIO { input: prev, output: unit }, proofMustVerify: true_ }
          /\ unit
    , publicOutput: unit
    }

--------------------------------------------------------------------------------
-- Prevs spec
--------------------------------------------------------------------------------

-- | Branch 1's single self-prev slot, at width 1.
type IncrementPrevsSpec =
  Tuple1 (Slot 1 (StatementIO (F StepField) Unit))

--------------------------------------------------------------------------------
-- Test spec
--------------------------------------------------------------------------------

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.TwoPhaseChain" do
  it "b0..b3 chain prove + verify under shared wrap VK" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/TwoPhaseChain.json")

    let
      cfg =
        { srs: { vestaSrs, pallasSrs }
        , debug: false
        , wrapDomainOverride: Nothing
        , proofCache: cache
        , lagrangeCache: Just lagrangeCache
        }

    makeZeroEntry <- liftEffect $ mkRuleEntry @Unit makeZeroRule Vector.nil
    incrementEntry <- liftEffect $ mkRuleEntry @Unit incrementRule (Self :< Vector.nil)
    let rules = tuple2 makeZeroEntry incrementEntry
    logInfo "[TwoPhaseChain] compiling…"
    output <- withSpan "[TwoPhaseChain] compile" $ liftEffect $ compileMulti
      @Unit
      @1
      cfg
      rules

    let
      BranchProver makeZeroProver = fst output.provers
      BranchProver incrementProver = fst (snd output.provers)
      -- Every prev is round-tripped through serialization before it is
      -- consumed, so the chain closes only if that is faithful.
      dummies = mkWidthDummies pallasSrs vestaSrs
    logInfo "[TwoPhaseChain] proving [step0, wrap0]"
    eRes <- withSpan "[TwoPhaseChain] prove b0" $ liftEffect $ makeZeroProver noAdvice
      { appInput: F zero, prevs: unit }
    b0 <- case eRes of
      Left e -> liftEffect $ Exc.throw ("makeZeroProver: " <> show e)
      Right p -> pure p
    b0' <- roundTripAndVerify dummies output.verifier b0

    -- b1's prev is a branch-0 proof; b2 and b3 chain branch 1 onto
    -- itself.
    logInfo "[TwoPhaseChain] proving [step1, wrap1]"
    eB1 <- withSpan "[TwoPhaseChain] prove b1" $ liftEffect $ incrementProver noAdvice
      { appInput: F one
      , prevs: tuple1 (InductivePrev b0' output.tag)
      }
    b1 <- case eB1 of
      Left e -> liftEffect $ Exc.throw ("incrementProver: " <> show e)
      Right p -> pure p
    b1' <- roundTripAndVerify dummies output.verifier b1
    logInfo "[TwoPhaseChain] proving [step2, wrap2]"
    eB2 <- withSpan "[TwoPhaseChain] prove b2" $ liftEffect $ incrementProver noAdvice
      { appInput: F (Curves.fromInt 2 :: StepField)
      , prevs: tuple1 (InductivePrev b1' output.tag)
      }
    b2 <- case eB2 of
      Left e -> liftEffect $ Exc.throw ("incrementProver b2: " <> show e)
      Right p -> pure p
    b2' <- roundTripAndVerify dummies output.verifier b2
    logInfo "[TwoPhaseChain] proving [step3, wrap3]"
    eB3 <- withSpan "[TwoPhaseChain] prove b3" $ liftEffect $ incrementProver noAdvice
      { appInput: F (Curves.fromInt 3 :: StepField)
      , prevs: tuple1 (InductivePrev b2' output.tag)
      }
    b3 <- case eB3 of
      Left e -> liftEffect $ Exc.throw ("incrementProver b3: " <> show e)
      Right p -> pure p

    -- One verifier for proofs of both branches: the `stepDomainLog2`
    -- each `CompiledProof` carries is what lets deferred-values
    -- reconstruction pick that proof's own step domain.
    logInfo "[TwoPhaseChain] verifying 4-proof chain…"
    verifyBatch output.verifier (map toVerifiable [ b0, b1, b2, b3 ]) `shouldEqual` true
    logInfo "[TwoPhaseChain] verification complete"
