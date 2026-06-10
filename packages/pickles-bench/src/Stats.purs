-- | A small `BenchLib.Reporter` that extends the default console output
-- | with min / max / mean / stddev across a bench's `samples`. BenchLib's
-- | own `SampleResult` only carries `average` per sample — by running
-- | each trial as its own `size` (see `Bench.Pickles.Prove.group`), the
-- | `samples` array becomes one entry per trial, and aggregating across
-- | them in `onBenchFinish` recovers the spread.
module Bench.Pickles.Stats (statsReporter) where

import Prelude

import BenchLib (BenchResult, Reporter, defaultReporter)
import Data.Array as Array
import Data.Foldable (foldl, maximum, minimum, sum)
import Data.Int as Int
import Data.Maybe (fromMaybe)
import Data.Newtype (unwrap)
import Data.Number (sqrt)
import Data.Number.Format (fixed, toStringWith)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console

statsReporter :: Reporter
statsReporter = defaultReporter
  { onBenchFinish = \br -> liftEffect (logStats br)
  }

logStats :: BenchResult -> Effect Unit
logStats { samples } = do
  let
    ms :: Array Number
    ms = map (\s -> unwrap s.average) samples
    n = Array.length ms
  case n of
    0 -> pure unit
    1 -> pure unit
    _ -> do
      let
        mn = fromMaybe 0.0 (minimum ms)
        mx = fromMaybe 0.0 (maximum ms)
        mean = sum ms / Int.toNumber n
        variance = foldl (\acc x -> acc + (x - mean) * (x - mean)) 0.0 ms / Int.toNumber n
        stddev = sqrt variance
        fmt x = toStringWith (fixed 0) x
        pct x = toStringWith (fixed 1) x
      Console.log
        ( "      └─ " <> show n <> " trials  "
            <> "min="
            <> fmt mn
            <> "ms  "
            <> "max="
            <> fmt mx
            <> "ms  "
            <> "mean="
            <> fmt mean
            <> "ms  "
            <> "stddev="
            <> fmt stddev
            <> "ms  "
            <> "(spread "
            <> fmt (mx - mn)
            <> "ms = "
            <> pct (100.0 * (mx - mn) / mean)
            <> "% of mean)"
        )
