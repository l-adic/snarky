// Single source of truth for the wasm32-wasip1-threads worker-pool
// sizing. Consumed by:
//   - patch-wasi-browser.mjs, which bakes POOL_SIZE into the generated
//     browser loader's `reuseWorker.size`;
//   - a host's worker (e.g. the example app's worker-entry.js), which
//     reads MAX_RAYON_THREADS to bound its rayon pool.
//
// The loader pre-spawns POOL_SIZE workers, shared between rayon and
// emnapi's async-work pool. rayon must stay within
// (POOL_SIZE - ASYNC_POOL_SIZE) threads: beyond that it spawns workers
// on demand, which deadlocks — a nested worker's module script loads
// via the (now blocked) parent thread's event loop.
//
// ASYNC_POOL_SIZE must match the `asyncWorkPoolSize` the napi CLI emits
// into the loader (currently its default).

export const POOL_SIZE = 16;
export const ASYNC_POOL_SIZE = 4;
export const MAX_RAYON_THREADS = POOL_SIZE - ASYNC_POOL_SIZE;
