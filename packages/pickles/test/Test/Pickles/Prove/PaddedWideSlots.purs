-- | A three-branch program whose branches have different prev counts, and
-- | whose slots are wider than one.
-- |
-- |   * branch 0 — no prevs (`mpv = 0`)
-- |   * branch 1 — two self prevs, each a proof of this system, so
-- |     each slot is `Slot 2` (`mpv = 2`)
-- |   * branch 2 — one self prev at width 2 (`mpv = 1`)
-- |
-- | `mpvMax = 2`, so branch 0 is front-padded by two slots, and those
-- | dummy slots are two challenge stacks wide apiece. Nothing else in
-- | the suite has that combination: `SimpleChainN2` is `mpv = 2` but
-- | single-branch, so it pads nothing, and `TwoPhaseChain` is
-- | two-branch but `mpvMax = 1`, so what it pads is one stack wide.
-- |
-- | So this is where a padded slot's width is load-bearing: if
-- | `padShapeProveData` gave every padded slot a single stack
-- | regardless of width, the wrap circuit would allocate four and the
-- | witness supply two, and the unassigned variables would surface as
-- | `MissingVariable` inside `b-poly`.
-- |
-- | Branches 0 and 2 use different unfinalized padding constants. Their
-- | exported circuits exercise predecessor-count selection in reconstruction.
-- | Proving branches 0 and 2 checks fully and partially padded witnesses.
module Test.Pickles.Prove.PaddedWideSlots
  ( spec
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (Tuple1, tuple1, tuple3, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles (BranchProver(..), PrevSlot(..), PrevStatement(..), Slot, SlotWrapKey(..), StatementIO(..), StepField, StepRule, compileMulti, mkRuleEntry, prevValues, toPrevs, toVerifiable, verifyBatch)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, assertEqual_, const_, exists, true_)
import Test.Pickles.Outputs (appOutputs)
import Test.Pickles.Prove.SimpleChainN2 (simpleChainN2Rule)
import Test.Pickles.Prove.TwoPhaseChain (makeZeroRule)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

type Stmt = StatementIO (F StepField) Unit

-- | Increment a single predecessor from this width-two application.
incrementRule :: StepRule (Tuple1 (Slot 2 Stmt)) (F StepField) (FVar StepField) Unit Unit
incrementRule getPrevStates self = do
  prev <- exists $ getPrevStates <#> prevValues <#> \(StatementIO { input } /\ _) -> input
  assertEqual_ self (CVar.add_ (const_ one) prev)
  pure
    { prevs: toPrevs $
        PrevStatement { publicInput: StatementIO { input: prev, output: unit }, proofMustVerify: true_ }
          /\ unit
    , publicOutput: unit
    }

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.PaddedWideSlots" do
  it "proves the front-padded branch of a program whose slots are wider than one" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    outputs <- liftEffect $ appOutputs "PaddedWideSlots"

    let
      cfg =
        { srs: { vestaSrs, pallasSrs }
        , debug: false
        -- The wrap circuit is the N2 shape, as in `SimpleChainN2`.
        , wrapDomainOverride: Just 14
        , proofCache: outputs.proofCache
        , lagrangeCache: Just lagrangeCache
        , dump: outputs.dumpAt "padded_wide_slots"
        }

    baseEntry <- liftEffect $ mkRuleEntry @Unit makeZeroRule Vector.nil
    mergeEntry <- liftEffect $ mkRuleEntry @Unit
      simpleChainN2Rule
      (Self :< Self :< Vector.nil)
    incrementEntry <- liftEffect $ mkRuleEntry @Unit incrementRule (Self :< Vector.nil)
    let rules = tuple3 baseEntry mergeEntry incrementEntry

    logInfo "[PaddedWideSlots] compiling…"
    output <- withSpan "[PaddedWideSlots] compile" $ liftEffect $ compileMulti
      @Unit
      @1
      cfg
      rules

    -- Branch 0 has no prevs of its own, so both of the wrap circuit's
    -- slots are padding.
    let BranchProver baseProver = fst output.provers
    logInfo "[PaddedWideSlots] proving the padded branch…"
    eRes <- withSpan "[PaddedWideSlots] prove branch 0" $ liftEffect $ baseProver noAdvice
      { appInput: F zero, prevs: unit }
    b0 <- case eRes of
      Left e -> liftEffect $ Exc.throw ("PaddedWideSlots base prover: " <> show e)
      Right p -> pure p

    let BranchProver incrementProver = fst (snd (snd output.provers))
    eB1 <- withSpan "[PaddedWideSlots] prove branch 2" $ liftEffect $ incrementProver noAdvice
      { appInput: F one, prevs: tuple1 (InductivePrev b0 output.tag) }
    b1 <- case eB1 of
      Left e -> liftEffect $ Exc.throw ("PaddedWideSlots increment prover: " <> show e)
      Right p -> pure p
    verifyBatch output.verifier (map toVerifiable [ b0, b1 ]) `shouldEqual` true
    logInfo "[PaddedWideSlots] verified"
