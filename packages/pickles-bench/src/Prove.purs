-- | Prove bench: time ONE recursive N=2 tree prove (b1).
-- |
-- | `prepareProve` does all the untimed setup — compile (NRR + tree),
-- | the NRR proof, and b0 — against the shared, pre-warmed SRS, and
-- | returns the b1 prove as an `Aff Unit` thunk. `Bench.Pickles.Main`
-- | runs `prepareProve` exactly once (NOT inside benchlib's
-- | `prepareInput`, which re-runs per iteration) and hands the thunk to
-- | `group`, so only the b1 prove is measured.
-- |
-- | The prover-call shape mirrors the passing `Test.Pickles.Prove.
-- | TreeProofReturn` (record `{ appInput, prevs, sideloadedVKs }` with
-- | `PrevSlot` constructors) — the live `BranchProver` API.
module Bench.Pickles.Prove
  ( prepareProve
  , group
  ) where

import Prelude

import Bench.Pickles.BenchUtils as BenchUtils
import Bench.Pickles.Common (BenchSrs, NrrRules, TreeRules, benchIterations, benchTreeRule, nrrRule)
import Bench.Pickles.FfiTimer as FfiTimer
import BenchLib as BL
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (tuple1, tuple2)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles (BranchProver(..), NoSlots, PrevSlot(..), SlotWrapKey(..), Slots2, StatementIO(..), StepField, compileMulti, mkRuleEntry)
import Run as Run
import Run.Except (runExcept) as RunExcept
import Snarky.Circuit.DSL (F(..))

-- | Untimed setup against the shared SRS: compile (NRR + tree), prove
-- | the NRR base, prove b0; return the b1 prove as a runnable thunk.
prepareProve :: BenchSrs -> Effect (Aff Unit)
prepareProve srs = do
  nrrEntry <- mkRuleEntry @0 @(F StepField) @Unit @1 @1 nrrRule unit
  nrr <- Run.runBaseEffect $ compileMulti
    @NrrRules
    @(F StepField)
    @Unit
    @NoSlots
    @1
    { srs, debug: false, wrapDomainOverride: Nothing, proofCache: Nothing }
    (tuple1 nrrEntry)
  let
    nrrProverVKs =
      { stepCompileResult: fst nrr.vks.perBranchStep
      , wrapCompileResult: nrr.vks.wrap
      , wrapDomainLog2: nrr.vks.wrapDomainLog2
      , stepNumChunks: nrr.vks.stepChunks
      }

  treeEntry <- mkRuleEntry @2 @(F StepField) @(F StepField) @1 @1
    benchTreeRule
    (tuple2 (External nrrProverVKs) Self)
  tree <- Run.runBaseEffect $ compileMulti
    @TreeRules
    @(F StepField)
    @(F StepField)
    @(Slots2 0 2)
    @1
    { srs, debug: false, wrapDomainOverride: Just 14, proofCache: Nothing }
    (tuple1 treeEntry)

  let
    BranchProver nrrProver = fst nrr.provers
    BranchProver treeProver = fst tree.provers

  nrrCp <- Run.runBaseEffect (RunExcept.runExcept (nrrProver { appInput: unit, prevs: unit, sideloadedVKs: unit })) >>= case _ of
    Left e -> Exc.throw (show e)
    Right r -> pure r

  let
    basePrevSelf = BasePrev
      { dummyStatement: StatementIO { input: unit, output: F (negate one) :: F StepField } }

  b0 <-
    Run.runBaseEffect
      ( RunExcept.runExcept
          ( treeProver
              { appInput: unit
              , prevs: tuple2 (InductivePrev nrrCp nrr.tag) basePrevSelf
              , sideloadedVKs: tuple2 unit unit
              }
          )
      ) >>= case _ of
      Left e -> Exc.throw (show e)
      Right r -> pure r

  pure $ do
    _ <-
      liftEffect
        ( Run.runBaseEffect $ RunExcept.runExcept
            ( treeProver
                { appInput: unit
                , prevs: tuple2 (InductivePrev nrrCp nrr.tag) (InductivePrev b0 tree.tag)
                , sideloadedVKs: tuple2 unit unit
                }
            )
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

group :: Aff Unit -> BL.Group
group proveThunk =
  BL.group "prove: N=2 tree b1 (compile + b0 untimed)"
    -- iterations = 1, sizes = [0, 0, …, 0] of length `benchIterations`
    -- → benchIterations independent samples, each with its own time.
    (\o -> o { iterations = 1, sizes = Array.replicate benchIterations 0 })
    [ BL.benchAff_ benchLabel
        (\_ -> pure unit)
        ( \_ -> do
            liftEffect FfiTimer.start
            liftEffect $ BenchUtils.startFfiTracking benchLabel
            liftEffect BenchUtils.startGcTracking
            _ <- proveThunk
            liftEffect $ BenchUtils.stopFfiTracking benchLabel
            liftEffect $ BenchUtils.captureTrial benchLabel
            liftEffect FfiTimer.reportSplit
            liftEffect BenchUtils.report
            _ <- liftEffect BenchUtils.stopGcTracking
            pure unit
        )
    ]
