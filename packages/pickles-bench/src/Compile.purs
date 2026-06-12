-- | Compile bench: time the FULL compilation of a maximal N=2 recursive
-- | step circuit (NRR + tree `compileMulti`) against the shared,
-- | pre-warmed SRS.
-- |
-- | The SRS is NOT created or warmed here — it is passed in from
-- | `Bench.Pickles.Main` (one shared, lagrange-prewarmed instance), so
-- | SRS construction and lagrange-basis computation are excluded from
-- | the measured region. What remains timed is the actual compilation:
-- | gate building + prover-/verifier-index creation for both the NRR
-- | base rule and the N=2 tree rule.
module Bench.Pickles.Compile
  ( fullCompile
  , group
  ) where

import Prelude

import Bench.Pickles.BenchUtils as BenchUtils
import Bench.Pickles.Common (BenchSrs, NrrRules, TreeRules, benchIterations, benchTreeRule, nrrRule)
import BenchLib as BL
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (tuple1, tuple2)
import Effect (Effect)
import Effect.Class (liftEffect)
import Pickles (NoSlots, RuleEntry, SlotWrapKey(..), Slots2, StepField, compileMulti, mkRuleEntry)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Circuit.DSL (F)

-- | Pin a compile-only `RuleEntry`'s input VALUE type to `Unit` (and its
-- | witness monad to `Effect`). `fullCompile` never runs a prover, so the
-- | rule's `inputVal` is never fixed structurally by an `appInput` (as it
-- | is at prove time); and `CircuitType` has no `var -> value` fundep, so
-- | `inputVar = Unit` alone can't determine it. Both example rules carry
-- | `inputVal = Unit`, so this `identity` cast supplies the missing pin
-- | with named type variables (no wildcard warnings).
pinCompileEntry
  :: forall prevsSpec mpv nd wvc valCarrier carrier outputSize slotVKs vkCarrier blueprints
   . RuleEntry prevsSpec mpv nd wvc valCarrier Unit carrier outputSize slotVKs vkCarrier blueprints ()
  -> RuleEntry prevsSpec mpv nd wvc valCarrier Unit carrier outputSize slotVKs vkCarrier blueprints ()
pinCompileEntry = identity

-- | The full example-circuit compilation against the shared SRS: the
-- | NRR `compileMulti`, then the N=2 tree `compileMulti`. The tree
-- | result is forced (the `fst … .constraints` read) so the whole
-- | pipeline actually runs.
fullCompile :: BenchSrs -> Effect Int
fullCompile srs = do
  -- `fullCompile` only compiles (never runs a prover), so the rule's
  -- witness monad `m` is never pinned by usage — pin it to `Effect`
  -- explicitly (compile discards the `exists` bodies, so `m` is phantom
  -- here; any `Monad`/`MonadEffect`/`MonadRec` works).
  nrrEntry <- pinCompileEntry <$> mkRuleEntry @0 @(F StepField) @Unit @1 @1 @() nrrRule unit
  nrr <- compileMulti
    @NrrRules
    @(F StepField)
    @Unit
    @NoSlots
    @1
    noAdvice
    { srs, debug: false, wrapDomainOverride: Nothing, proofCache: Nothing }
    (tuple1 nrrEntry)
  let
    nrrProverVKs =
      { stepCompileResult: fst nrr.vks.perBranchStep
      , wrapCompileResult: nrr.vks.wrap
      , wrapDomainLog2: nrr.vks.wrapDomainLog2
      , stepNumChunks: nrr.vks.stepChunks
      }

  treeEntry <- pinCompileEntry <$> mkRuleEntry @2 @(F StepField) @(F StepField) @1 @1 @()
    benchTreeRule
    (tuple2 (External nrrProverVKs) Self)
  tree <- compileMulti
    @TreeRules
    @(F StepField)
    @(F StepField)
    @(Slots2 0 2)
    @1
    noAdvice
    { srs, debug: false, wrapDomainOverride: Just 14, proofCache: Nothing }
    (tuple1 treeEntry)

  -- Force the step constraint system so the compile is not deferred.
  pure (Array.length (fst tree.vks.perBranchStep).constraints)

-- | The bench label: keys the results-JSON entry and the
-- | `[bench-window]` markers `parse_gclog.mjs` matches GC lines to.
benchLabel :: String
benchLabel = "NRR + tree compile (shared warm SRS)"

-- | Benchmark group: the compile workload. SRS shared/pre-warmed in
-- | `Main`; only the NRR + tree compilation is timed.
group :: BenchSrs -> BL.Group
group srs =
  BL.group "compile: N=2 step circuit, domain log2 = 16"
    (\o -> o { iterations = benchIterations, sizes = [ 0 ] })
    [ BL.benchAff_ benchLabel
        (\_ -> pure unit)
        ( \_ -> do
            liftEffect $ BenchUtils.startFfiTracking benchLabel
            liftEffect BenchUtils.startGcTracking
            _ <- liftEffect (fullCompile srs)
            liftEffect $ BenchUtils.stopFfiTracking benchLabel
            liftEffect $ BenchUtils.captureTrial benchLabel
            liftEffect BenchUtils.report
            _ <- liftEffect BenchUtils.stopGcTracking
            pure unit
        )
    ]
