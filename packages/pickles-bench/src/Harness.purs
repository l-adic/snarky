-- | PureScript binding to the shared `bench-harness` lib — the ONE benchmark
-- | runner, used identically by the PS and o1js suites (this is the site-specific
-- | FFI the PS side defines for it; the o1js side has a TS binding to the same
-- | `index.js`). Pure FFI, no logic: the runner lives in the lib.
-- |
-- | A `Group`'s `prepare`/`work` are `Effect (Promise Unit)` — which IS a JS
-- | `() => Promise` — so the lib drives them directly. Build them with
-- | `Control.Promise.fromAff`.
module Bench.Harness
  ( Sample
  , Stats
  , Bench
  , Group
  , Hooks
  , runBench
  , writeArtifact
  ) where

import Prelude

import Control.Promise (Promise, toAffE)
import Data.Nullable (Nullable)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Uncurried (EffectFn1)

type Sample = { iterations :: Int, ms :: Number }

type Stats =
  { n :: Int
  , meanMs :: Nullable Number
  , stddevMs :: Nullable Number
  , minMs :: Nullable Number
  , maxMs :: Nullable Number
  }

-- | What `runBench` returns. Sites may attach extra fields at runtime (the PS
-- | side adds `ffi` via `Bench.Pickles.Ffi.attachFfi`) before `writeArtifact`;
-- | those ride along the JS object even though this row type doesn't name them.
type Bench = { name :: String, samples :: Array Sample, stats :: Stats }

-- | One workload. `prepare` is untimed (run once, in group order); `work` is the
-- | timed unit (run `trials` times). Both are JS `() => Promise` via `fromAff`.
type Group =
  { label :: String
  , trials :: Int
  , prepare :: Effect (Promise Unit)
  , work :: Effect (Promise Unit)
  }

-- | Optional per-trial instrumentation around the timed region (the PS side
-- | supplies napi FFI counters; o1js supplies none). `EffectFn1` so the lib can
-- | call `hooks.onStart(label)` directly (uncurried, runs immediately).
type Hooks =
  { onStart :: EffectFn1 String Unit
  , onEnd :: EffectFn1 String Unit
  }

foreign import runBenchImpl :: Array Group -> Hooks -> Effect (Promise (Array Bench))
foreign import writeArtifactImpl :: { suite :: String, benches :: Array Bench } -> Effect Unit

runBench :: Array Group -> Hooks -> Aff (Array Bench)
runBench groups hooks = toAffE (runBenchImpl groups hooks)

-- | Write the run artifact (the lib fills in the common machine fields). The
-- | `benches` carry the PS `ffi` field at runtime even though the type omits it.
writeArtifact :: { suite :: String, benches :: Array Bench } -> Effect Unit
writeArtifact = writeArtifactImpl
