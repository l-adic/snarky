module Bench.Pickles.BenchUtils
  ( installFfiWrappers
  , startFfiTracking
  , stopFfiTracking
  , captureTrial
  , recordBenchSamples
  , writeResults
  , startGcTracking
  , stopGcTracking
  , takeHeapSnapshot
  , report
  , GCEvent
  , WallSample
  ) where

import Prelude

import Effect (Effect)

type GCEvent =
  { time :: Number
  , duration :: Number
  , kind :: String
  , before :: Number
  , after :: Number
  , collected :: Number
  }

-- | One benchlib wall-time sample, flattened for the results JSON.
type WallSample = { iterations :: Int, ms :: Number }

-- | Install the napi-call wrappers on the cached `kimchi-napi` module
-- | object. Idempotent. Counters are inactive until `startFfiTracking`
-- | flips the gate — setup work runs through the wrappers as a no-op.
foreign import installFfiWrappers :: Effect Unit

-- | Open the timed FFI window for the named bench. Resets accumulators,
-- | activates the wrappers, and emits a `[bench-window] start` marker on
-- | stdout (same stream + timestamp base as `--trace-gc`, so
-- | `parse_gclog.mjs` can window GC lines per trial).
foreign import startFfiTracking :: String -> Effect Unit

-- | Close the timed FFI window (and emit the matching end marker).
foreign import stopFfiTracking :: String -> Effect Unit

-- | Snapshot the closed FFI window into the named bench's trial list
-- | (rust wall ms, call count, per-napi-call totals). Call once per
-- | timed trial, after `stopFfiTracking`.
foreign import captureTrial :: String -> Effect Unit

-- | Record benchlib's wall-time samples for a bench (from a reporter's
-- | `onBenchFinish`).
foreign import recordBenchSamples :: String -> Array WallSample -> Effect Unit

-- | Assemble and write the machine-readable results artifact for the
-- | whole run: per bench — samples, mean/stddev/min/max, rust-FFI share,
-- | per-call totals — plus git SHA (+dirty flag), node version, date.
-- | Path: `$BENCH_RESULTS_FILE` or `bench-results/<sha>-<date>.json`
-- | (relative to the CWD, i.e. the repo root under the runner scripts).
foreign import writeResults :: Effect Unit

foreign import startGcTracking :: Effect Unit
foreign import stopGcTracking :: Effect (Array GCEvent)
foreign import takeHeapSnapshot :: String -> Effect Unit
foreign import report :: Effect Unit
