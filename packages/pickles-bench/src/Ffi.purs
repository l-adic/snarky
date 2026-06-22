-- | The PS suite's site-specific instrumentation for the shared `bench-harness`:
-- | kimchi-napi boundary timing (the Rust-vs-JS split in the artifact's `ffi`
-- | field). `onStart`/`onEnd` are the per-trial `Hooks` passed to `runBench`;
-- | `attachFfi` augments the returned benches before `writeArtifact`. The o1js
-- | suite has no counterpart (its kimchi is WASM in-heap) and passes no hooks.
module Bench.Pickles.Ffi
  ( installFfiWrappers
  , onStart
  , onEnd
  , attachFfi
  ) where

import Prelude

import Bench.Harness (Bench)
import Effect (Effect)
import Effect.Uncurried (EffectFn1)

-- | Install the napi-call timing wrappers (idempotent; inert until `onStart`).
foreign import installFfiWrappers :: Effect Unit

-- | `Hooks.onStart` — reset + arm the FFI counters for a trial.
foreign import onStart :: EffectFn1 String Unit

-- | `Hooks.onEnd` — snapshot the trial's FFI totals under its label.
foreign import onEnd :: EffectFn1 String Unit

-- | Augment each bench with its `ffi` summary (rust mean + share). The added
-- | field rides along the JS object into the artifact.
foreign import attachFfi :: Array Bench -> Effect (Array Bench)
