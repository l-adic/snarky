-- | Prove bench: time ONE recursive N=2 tree prove (b1).
-- |
-- | `prepareProve` does all the untimed setup — compile (NRR + tree),
-- | the NRR proof, and b0 — against the shared, pre-warmed SRS, and
-- | returns the b1 prove as an `Aff Unit` thunk. `Bench.Pickles.Main`
-- | wraps it in a memoized getter that `group` runs as benchlib's
-- | `prepareInput` (untimed, outside `measureTime`): the first sample's
-- | prepare does the real work — after the compile group, so compile is
-- | never measured with prove state resident — and later samples hit
-- | the memo. Only the b1 prove is measured.
-- |
-- | The prover-call shape mirrors the passing `Test.Pickles.Prove.
-- | TreeProofReturn` (record `{ appInput, prevs }` with
-- | `PrevSlot` constructors) — the live `BranchProver` API.
module Bench.Pickles.Prove
  ( prepareProve
  , group
  ) where

import Prelude

import Bench.Harness (Group)
import Bench.Pickles.Common (BenchSrs, NrrRules, TreeRules, benchTreeRule, nrrRule)
import Bench.Pickles.FfiTimer as FfiTimer
import Control.Promise (fromAff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (tuple1, tuple2)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Effect.Ref as Ref
import Pickles (BranchProver(..), PrevSlot(..), SlotWrapKey(..), StatementIO(..), StepField, compileMulti, mkRuleEntry)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Circuit.DSL (F(..))

-- | Untimed setup against the shared SRS: compile (NRR + tree), prove
-- | the NRR base, prove b0; return the b1 prove as a runnable thunk.
prepareProve :: BenchSrs -> Effect (Aff Unit)
prepareProve srs = do
  nrrEntry <- mkRuleEntry @(F StepField) nrrRule Vector.nil
  nrr <- compileMulti
    @NrrRules
    @(F StepField)
    @1
    { srs, debug: false, wrapDomainOverride: Nothing, proofCache: Nothing, lagrangeCache: Nothing }
    (tuple1 nrrEntry)
  treeEntry <- mkRuleEntry @(F StepField)
    benchTreeRule
    (External nrr.tagData :< Self :< Vector.nil)
  tree <- compileMulti
    @TreeRules
    @(F StepField)
    @1
    { srs, debug: false, wrapDomainOverride: Just 14, proofCache: Nothing, lagrangeCache: Nothing }
    (tuple1 treeEntry)

  let
    BranchProver nrrProver = fst nrr.provers
    BranchProver treeProver = fst tree.provers

  nrrCp <- nrrProver noAdvice { appInput: unit, prevs: unit } >>= case _ of
    Left e -> Exc.throw (show e)
    Right r -> pure r

  let
    basePrevSelf = BasePrev
      { dummyStatement: StatementIO { input: unit, output: F (negate one) :: F StepField } }

  b0 <-
    treeProver noAdvice
      { appInput: unit
      , prevs: tuple2 (InductivePrev nrrCp nrr.tag) basePrevSelf
      } >>= case _ of
      Left e -> Exc.throw (show e)
      Right r -> pure r

  pure $ do
    _ <-
      liftEffect
        ( treeProver noAdvice
            { appInput: unit
            , prevs: tuple2 (InductivePrev nrrCp nrr.tag) (InductivePrev b0 tree.tag)
            }
        ) >>= case _ of
        Left e -> liftEffect $ Exc.throw (show e)
        Right _ -> pure unit
    pure unit

-- | Benchmark group: the timed b1 prove. The thunk (compile + b0 done)
-- | is captured; each `sizes` entry produces an independent
-- | `SampleResult`, giving us per-trial timings (benchlib's `iterations`
-- | averages internally and discards the spread).
-- | The bench label: keys the results-JSON entry and the
-- | `[bench-window]` markers `parse_gclog.mjs` matches GC lines to.
benchLabel :: String
benchLabel = "b1 recursive prove (shared warm SRS)"

-- | `prepare` runs `prepareProve` once (untimed: compile + NRR + b0) and stashes
-- | the b1 prove thunk; `work` runs that thunk (the one timed unit) `trials`
-- | times. Because `runBench` runs each group's `prepare` in order, the heavy
-- | prove setup happens AFTER the compile group — so compile is never measured
-- | with prove's prepared state resident. `FfiTimer` brackets the timed prove
-- | (the napi prove-phase split), as before. The per-trial GC / window / FFI-
-- | counter wrapping is in the shared `runBench`.
group :: Int -> BenchSrs -> Effect Group
group trials srs = do
  ref <- Ref.new (pure unit :: Aff Unit)
  pure
    { label: benchLabel
    , trials
    , prepare: fromAff do
        thunk <- liftEffect (prepareProve srs)
        liftEffect (Ref.write thunk ref)
    , work: fromAff do
        liftEffect FfiTimer.start
        join (liftEffect (Ref.read ref))
        liftEffect FfiTimer.reportSplit
    }
