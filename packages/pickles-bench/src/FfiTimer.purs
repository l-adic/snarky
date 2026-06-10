-- | Exact JS-vs-Rust split for the prove. The V8 CPU profiler cannot
-- | see inside the Rust kimchi prover (no native frames; blocked-FFI
-- | time is mis-attributed). This wraps the two synchronous napi
-- | prover calls (`caml_pasta_f{p,q}_plonk_proof_create`) on the shared
-- | `kimchi-napi` singleton and reports wall-time in Rust vs JS for the
-- | bracketed prove. Zero production edit (bench-local monkeypatch of
-- | the cached CJS module object).
module Bench.Pickles.FfiTimer
  ( install
  , start
  , reportSplit
  ) where

import Data.Unit (Unit)
import Effect (Effect)

-- | Wrap the prover napi calls once (idempotent). Call during untimed
-- | setup, before the timed samples.
foreign import install :: Effect Unit

-- | Reset counters + mark t0. Call at the start of each timed sample.
foreign import start :: Effect Unit

-- | Print: total prove wall, time inside the Rust prover FFI (+ call
-- | count), and JS-side remainder, with percentages.
foreign import reportSplit :: Effect Unit
