-- | A two-branch program whose branches have different prev counts, and
-- | whose slots are wider than one.
-- |
-- |   * branch 0 — no prevs (`mpv = 0`)
-- |   * branch 1 — two self prevs, each a proof of THIS system, so each
-- |     slot is `Slot 2` (`mpv = 2`)
-- |
-- | `mpvMax = 2`, so branch 0 is front-padded by two slots, and those
-- | dummy slots are two challenge stacks wide apiece. Nothing else in
-- | the suite has that combination: `SimpleChainN2` is `mpv = 2` but
-- | single-branch, so it pads nothing, and `TwoPhaseChain` is
-- | two-branch but `mpvMax = 1`, so what it pads is one stack wide.
-- |
-- | That gap let a prover-side bug live: `padShapeProveData` gave every
-- | padded slot a single stack regardless of the slot's width, so the
-- | wrap circuit allocated four and the witness supplied two. The two
-- | unassigned variables surfaced as `MissingVariable` inside `b-poly`,
-- | and only the example application caught it.
-- |
-- | Proving branch 0 is the whole test: front-padding happens at prove
-- | time, and the base case is where all of it is dummy. Both rule
-- | bodies are borrowed — what is under test is the branch arrangement,
-- | not the arithmetic.
module Test.Pickles.Prove.PaddedWideSlots
  ( spec
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (Tuple2, tuple2)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Node.Process (lookupEnv)
import Pickles (BranchProver(..), RulesCons, RulesNil, Slot, SlotWrapKey(..), StatementIO, StepField, compileMulti, mkRuleEntry, toVerifiable, verifyBatch)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.DSL (F(..))
import Test.Pickles.Prove.SimpleChainN2 (simpleChainN2Rule)
import Test.Pickles.Prove.TwoPhaseChain (makeZeroRule)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

type Stmt = StatementIO (F StepField) Unit

-- | Branch 0 contributes no slots, branch 1 contributes two of width 2.
-- | `mpvMax` is the max of the two, so the wrap circuit has two slots of
-- | width 2 and branch 0's `mpvPad` is 2 — every slot it presents is a
-- | dummy that must still be two stacks wide.
type PaddedWideSlotsRules =
  RulesCons 0 Unit Unit Unit
    ( RulesCons 2
        (Tuple2 Stmt Stmt)
        (Tuple2 (Slot 2 Stmt) (Slot 2 Stmt))
        (Tuple2 SlotWrapKey SlotWrapKey)
        RulesNil
    )

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.PaddedWideSlots" do
  it "proves the front-padded branch of a program whose slots are wider than one" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR"
      <#> map \dir -> mkProofCache (dir <> "/PaddedWideSlots.json")

    let
      cfg =
        { srs: { vestaSrs, pallasSrs }
        , debug: false
        -- The wrap circuit is the N2 shape, as in `SimpleChainN2`.
        , wrapDomainOverride: Just 14
        , proofCache: cache
        , lagrangeCache: Just lagrangeCache
        }

    baseEntry <- liftEffect $ mkRuleEntry @2 @Unit @(F StepField) makeZeroRule unit
    mergeEntry <- liftEffect $ mkRuleEntry @2 @Unit @(F StepField)
      simpleChainN2Rule
      (tuple2 Self Self)
    let rules = tuple2 baseEntry mergeEntry

    logInfo "[PaddedWideSlots] compiling…"
    output <- withSpan "[PaddedWideSlots] compile" $ liftEffect $ compileMulti
      @PaddedWideSlotsRules
      @Unit
      @(F StepField)
      @1
      noAdvice
      cfg
      rules

    -- Branch 0: no prevs of its own, so the wrap circuit's two slots are
    -- both padding. This is the prove that used to fail.
    let BranchProver baseProver = fst output.provers
    logInfo "[PaddedWideSlots] proving the padded branch…"
    eRes <- withSpan "[PaddedWideSlots] prove branch 0" $ liftEffect $ baseProver noAdvice
      { appInput: F zero, prevs: unit, sideloadedVKs: unit }
    b0 <- case eRes of
      Left e -> liftEffect $ Exc.throw ("PaddedWideSlots base prover: " <> show e)
      Right p -> pure p

    verifyBatch output.verifier (map toVerifiable [ b0 ]) `shouldEqual` true
    logInfo "[PaddedWideSlots] verified"
