-- | An `External` slot whose import has two step domains, beside a
-- | `Self` slot: the blockchain shape. The imported system is
-- | `TwoPhaseChain`, whose `make_zero` and `increment` branches run at
-- | different step domains; each of its proofs is a "transaction". The
-- | chain rule verifies one transaction (slot 0, width 1) and its own
-- | previous proof (slot 1, width 2, gated on the base case), and adds
-- | the transaction's value to its state.
-- |
-- | c0 imports a `make_zero` proof, c1 an `increment` proof and c2 a
-- | `make_zero` proof again, so slot 0 finalizes at both imported
-- | domains, with and without a verified self slot beside it. The test
-- | fails if an `External` slot is given one domain instead of its
-- | import's list, or if the two slots' candidate domains or
-- | verification keys are crossed.
module Test.Pickles.Prove.ImportTwoPhaseChain
  ( spec
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (Tuple2, tuple1, tuple2, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles (BranchProver(..), CompiledProof(..), PrevSlot(..), PrevStatement(..), Slot, SlotWrapKey(..), StatementIO(..), StepField, StepRule, compileMulti, mkRuleEntry, prevValues, toPrevs, toVerifiable, verifyBatch)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, exists, if_, not_, readCVar, true_)
import Test.Pickles.Outputs (appOutputs)
import Test.Pickles.Prove.TwoPhaseChain (incrementRule, makeZeroRule)
import Test.Pickles.SerializeRoundTrip (mkWidthDummies, roundTripAndVerify)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)

-- | Slot 0: a `TwoPhaseChain` proof, whose input is its value. Slot 1:
-- | this chain's previous proof, whose output is its state.
type ChainPrevsSpec =
  Tuple2
    (Slot 1 (StatementIO (F StepField) Unit))
    (Slot 2 (StatementIO Unit (F StepField)))

-- | The state is the transaction's value in the base case, the previous
-- | state plus it otherwise. The transaction always verifies; the
-- | previous proof unless this is the base case, which a dummy previous
-- | state of -1 marks.
chainRule
  :: StepRule ChainPrevsSpec
       Unit
       Unit
       (F StepField)
       (FVar StepField)
chainRule getPrevStates _ = do
  tx <- exists $ getPrevStates <#> prevValues <#> \(StatementIO { input: txIn } /\ _) -> txIn
  prev <- exists $ getPrevStates <#> prevValues <#> \(_ /\ StatementIO { output: prevOut } /\ _) -> prevOut
  isBaseCase <- exists $ readCVar prev <#> (_ == F (negate one))
  selfVal <- if_ isBaseCase tx (CVar.add_ prev tx)
  pure
    { prevs: toPrevs $
        PrevStatement { publicInput: StatementIO { input: tx, output: unit }, proofMustVerify: true_ }
          /\ PrevStatement { publicInput: StatementIO { input: unit, output: prev }, proofMustVerify: not_ isBaseCase }
          /\ unit
    , publicOutput: selfVal
    }

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.ImportTwoPhaseChain" do
  it "an External slot over a two-domain import, beside a Self slot: c0..c2 prove + verify" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    outputs <- liftEffect $ appOutputs "ImportTwoPhaseChain"

    let
      cfg =
        { srs: { vestaSrs, pallasSrs }
        , debug: false
        , wrapDomainOverride: Nothing
        , proofCache: outputs.proofCache
        , lagrangeCache: Just lagrangeCache
        , dump: Nothing
        }
      -- Every prev is round-tripped through serialization before it is
      -- consumed, so the chain closes only if that is faithful.
      dummies = mkWidthDummies pallasSrs vestaSrs

    -- The imported system and its two transactions, one per branch.
    makeZeroEntry <- liftEffect $ mkRuleEntry @Unit makeZeroRule Vector.nil
    incrementEntry <- liftEffect $ mkRuleEntry @Unit incrementRule (Self :< Vector.nil)
    logInfo "[ImportTwoPhaseChain] compiling two_phase_chain…"
    txs <- withSpan "[ImportTwoPhaseChain] compile two_phase_chain" $ liftEffect $ compileMulti
      @Unit
      @1
      cfg { dump = outputs.dumpAt "two_phase_chain" }
      (tuple2 makeZeroEntry incrementEntry)
    let
      BranchProver makeZeroProver = fst txs.provers
      BranchProver incrementProver = fst (snd txs.provers)
    logInfo "[ImportTwoPhaseChain] proving make_zero"
    eTx0 <- withSpan "[ImportTwoPhaseChain] prove make_zero" $ liftEffect $ makeZeroProver noAdvice
      { appInput: F zero, prevs: unit }
    tx0 <- case eTx0 of
      Left e -> liftEffect $ Exc.throw ("makeZeroProver: " <> show e)
      Right p -> roundTripAndVerify dummies txs.verifier p
    logInfo "[ImportTwoPhaseChain] proving increment"
    eTx1 <- withSpan "[ImportTwoPhaseChain] prove increment" $ liftEffect $ incrementProver noAdvice
      { appInput: F one, prevs: tuple1 (InductivePrev tx0 txs.tag) }
    tx1 <- case eTx1 of
      Left e -> liftEffect $ Exc.throw ("incrementProver: " <> show e)
      Right p -> roundTripAndVerify dummies txs.verifier p

    -- The two transactions are at different step domains, so slot 0's
    -- finalize runs at both.
    let domainOf (CompiledProof p) = p.branchData.domainLog2
    domainOf tx0 `shouldNotEqual` domainOf tx1

    chainEntry <- liftEffect $ mkRuleEntry @(F StepField)
      chainRule
      (External txs.tagData :< Self :< Vector.nil)
    logInfo "[ImportTwoPhaseChain] compiling chain…"
    -- Like `TreeProofReturn`'s, the chain's wrap circuit fits 2^14, below
    -- the 2^15 a two-slot tag's wrap domain defaults to.
    chain <- withSpan "[ImportTwoPhaseChain] compile chain" $ liftEffect $ compileMulti
      @(F StepField)
      @1
      cfg { wrapDomainOverride = Just 14, dump = outputs.dumpAt "chain" }
      (tuple1 chainEntry)
    let
      BranchProver chainProver = fst chain.provers

      runStep
        :: CompiledProof 1 (StatementIO (F StepField) Unit)
        -> PrevSlot Unit 2 (StatementIO Unit (F StepField))
        -> Aff (CompiledProof 2 (StatementIO Unit (F StepField)))
      runStep tx selfPrev = do
        eRes <- liftEffect $ chainProver noAdvice
          { appInput: unit
          , prevs: tuple2 (InductivePrev tx txs.tag) selfPrev
          }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("chainProver: " <> show e)
          Right p -> pure p

      basePrevSelf = BasePrev
        { dummyStatement: StatementIO { input: unit, output: F (negate one) :: F StepField }
        }

    logInfo "[ImportTwoPhaseChain] proving c0 over make_zero"
    c0 <- withSpan "[ImportTwoPhaseChain] prove c0" $ liftAff $ runStep tx0 basePrevSelf
    c0' <- roundTripAndVerify dummies chain.verifier c0
    logInfo "[ImportTwoPhaseChain] proving c1 over increment"
    c1 <- withSpan "[ImportTwoPhaseChain] prove c1" $ liftAff $ runStep tx1 (InductivePrev c0' chain.tag)
    c1' <- roundTripAndVerify dummies chain.verifier c1
    logInfo "[ImportTwoPhaseChain] proving c2 over make_zero"
    c2 <- withSpan "[ImportTwoPhaseChain] prove c2" $ liftAff $ runStep tx0 (InductivePrev c1' chain.tag)

    logInfo "[ImportTwoPhaseChain] verifying…"
    verifyBatch txs.verifier (map toVerifiable [ tx0, tx1 ]) `shouldEqual` true
    verifyBatch chain.verifier (map toVerifiable [ c0, c1, c2 ]) `shouldEqual` true

    -- The state adds each transaction's value: 0, then 0 + 1, then 1 + 0.
    let outputOf (CompiledProof p) = let StatementIO s = p.statement in s.output
    map outputOf [ c0, c1, c2 ] `shouldEqual` [ F zero, F one, F one ]
