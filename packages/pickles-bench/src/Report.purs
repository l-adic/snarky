-- | The machine-readable results reporter: feeds benchlib's wall-time
-- | samples into `BenchUtils`'s results collector (`onBenchFinish`) and
-- | writes the run's JSON artifact at `onSuiteFinish`.
-- |
-- | The artifact is the regression baseline: per bench — samples,
-- | mean/stddev/min/max, rust-FFI share, per-napi-call totals — keyed by
-- | git SHA. Compare two runs with `packages/pickles-bench/compare.mjs`;
-- | attach per-trial GC stats from a `--trace-gc` log with
-- | `packages/pickles-bench/parse_gclog.mjs`.
module Bench.Pickles.Report (jsonReporter) where

import Prelude

import Bench.Pickles.BenchUtils as BenchUtils
import BenchLib (Reporter, defaultReporter)
import Data.Newtype (unwrap)
import Effect.Class (liftEffect)

jsonReporter :: Reporter
jsonReporter = defaultReporter
  { onBenchFinish = \{ benchName, samples } ->
      liftEffect $ BenchUtils.recordBenchSamples benchName $
        samples <#> \s -> { iterations: s.iterations, ms: unwrap s.average }
  , onSuiteFinish = \_ -> liftEffect BenchUtils.writeResults
  }
