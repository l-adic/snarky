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

import Bench.Harness (Group)
import Bench.Pickles.Common (BenchSrs, NrrRules, TreeRules, benchTreeRule, nrrRule)
import Control.Promise (fromAff)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (tuple1)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (liftEffect)
import Pickles (RuleEntry, SlotWrapKey(..), StepField, compileMulti, mkRuleEntry)
import Snarky.Circuit.DSL (F)

-- | Pin a compile-only `RuleEntry`'s input VALUE type to `Unit` (and its
-- | witness monad to `Effect`). `fullCompile` never runs a prover, so the
-- | rule's `inputVal` is never fixed structurally by an `appInput` (as it
-- | is at prove time); and `CircuitType` has no `var -> value` fundep, so
-- | `inputVar = Unit` alone can't determine it. Both example rules carry
-- | `inputVal = Unit`, so this `identity` cast supplies the missing pin
-- | with named type variables (no wildcard warnings).
pinCompileEntry
  :: forall prevsSpec mpv valCarrier outputSize
   . RuleEntry prevsSpec mpv valCarrier Unit outputSize ()
  -> RuleEntry prevsSpec mpv valCarrier Unit outputSize ()
pinCompileEntry = identity

-- | The full example-circuit compilation against the shared SRS: the
-- | NRR `compileMulti`, then the N=2 tree `compileMulti`. The tree
-- | result is forced (the `Vector.head … .constraints` read) so the whole
-- | pipeline actually runs.
fullCompile :: BenchSrs -> Effect Int
fullCompile srs = do
  -- `fullCompile` only compiles (never runs a prover), so the rule's
  -- witness monad `m` is never pinned by usage — pin it to `Effect`
  -- explicitly (compile discards the `exists` bodies, so `m` is phantom
  -- here; any `Monad`/`MonadEffect`/`MonadRec` works).
  nrrEntry <- pinCompileEntry <$> mkRuleEntry @0 @(F StepField) @() nrrRule Vector.nil
  nrr <- compileMulti
    @NrrRules
    @(F StepField)
    @1
    { srs, debug: false, wrapDomainOverride: Nothing, proofCache: Nothing, lagrangeCache: Nothing }
    (tuple1 nrrEntry)
  treeEntry <- pinCompileEntry <$> mkRuleEntry @2 @(F StepField) @()
    benchTreeRule
    (External nrr.tagData :< Self :< Vector.nil)
  tree <- compileMulti
    @TreeRules
    @(F StepField)
    @1
    { srs, debug: false, wrapDomainOverride: Just 14, proofCache: Nothing, lagrangeCache: Nothing }
    (tuple1 treeEntry)

  -- Force the step constraint system so the compile is not deferred.
  pure (Array.length (Vector.head tree.vks.perBranchStep).constraints)

-- | The bench label: keys the results-JSON entry and the
-- | `[bench-window]` markers `parse_gclog.mjs` matches GC lines to.
benchLabel :: String
benchLabel = "NRR + tree compile (shared warm SRS)"

-- | Benchmark group: the compile workload. SRS shared/pre-warmed in `Main`; only
-- | the NRR + tree compilation is timed. No setup (`prepare` is a no-op — the SRS
-- | is ready); each trial is one full `fullCompile`. The per-trial GC / window /
-- | FFI wrapping lives in the shared `runBench`, not here.
group :: Int -> BenchSrs -> Group
group trials srs =
  { label: benchLabel
  , trials
  , prepare: fromAff (pure unit)
  , work: fromAff (liftEffect (void (fullCompile srs)))
  }
