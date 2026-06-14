// Worker-pool sizing for the wasm32-wasip1-threads backend.
//
// These are BUILD-TIME parameters, not runtime knobs: POOL_SIZE is baked
// into the generated browser loader's pre-spawned `reuseWorker` pool by
// patch-wasi-browser.mjs, and MAX_RAYON_THREADS is bundled into the host
// worker (e.g. the example app's worker-entry.js). They can't be pure
// runtime values — the pool is pre-spawned during module init, before any
// host code can read `navigator.hardwareConcurrency` — so the pool SIZE is
// a build param (env-overridable, with a default) and the host still picks
// the actual rayon thread count WITHIN MAX_RAYON_THREADS at run time
// (e.g. min(MAX_RAYON_THREADS, hardwareConcurrency - 1)).
//
// Override at build time:
//   KIMCHI_WASM_POOL_SIZE=24 npm run build:wasm   (then rebuild the web bundle)
// The web bundle picks up the same value via a `define` in the example
// app's vite.config.mjs, so the loader's pool and the worker's rayon cap
// stay consistent.

// NB: this MUST be the literal member expression `process.env.KIMCHI_WASM_POOL_SIZE`
// (not a dynamic `process.env[name]`) — vite's `define` only statically
// replaces the literal form when bundling the browser worker. In node
// (patch-wasi-browser.mjs) it reads the real env; the `typeof process`
// guard keeps it safe in a browser build without a process polyfill.
const rawPoolSize =
  typeof process !== "undefined" ? process.env.KIMCHI_WASM_POOL_SIZE : undefined;
const parsedPoolSize = Number(rawPoolSize);

// Pre-spawned worker pool baked into the browser loader.
export const POOL_SIZE =
  Number.isInteger(parsedPoolSize) && parsedPoolSize > 0 ? parsedPoolSize : 16;

// emnapi async-work threads. PINNED to the value the napi CLI hardcodes
// into the browser loader (`asyncWorkPoolSize: 4`); changing it here alone
// would not change the loader, so it is intentionally not env-driven.
export const ASYNC_POOL_SIZE = 4;

// rayon's share of the pool: whatever the async-work threads leave. The
// host caps its rayon pool at this at run time. Floored at 1 so a
// pathological small POOL_SIZE (<= ASYNC_POOL_SIZE) can't yield a
// negative count — which would wrap to a huge u32 in `initThreadPool`.
// (A POOL_SIZE that small is itself invalid; the loader patch rejects it
// at build time.)
export const MAX_RAYON_THREADS = Math.max(1, POOL_SIZE - ASYNC_POOL_SIZE);
