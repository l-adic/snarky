// The simulation Web Worker: owns the wasm kimchi backend (the
// `kimchi-napi` import is aliased to the wasi-browser loader in
// vite.config.mjs) and runs the engine, bridging its callbacks to
// postMessage. Lives off the UI thread because proving is synchronous.
//
// Everything heavy is imported LAZILY inside the message handler so the
// worker is responsive immediately and any wasm-init failure is caught
// and forwarded to the UI log instead of killing the worker silently.
import { MAX_RAYON_THREADS, ASYNC_POOL_SIZE } from "../../../kimchi-napi/wasm-pool-config.mjs";

// Keep one core for this worker's own JS (witness generation, the event
// loop servicing the wasi threads) between Rust phases.
const RESERVED_FOR_JS = 1;

const post = (tag) => (value) => () => self.postMessage({ tag, value });
const postNow = (tag, value) => self.postMessage({ tag, value });

// rayon pool size: one fewer than the reported core count, never more
// than the pre-spawned worker pool allows. If the core count is
// unreported, fall back to single-threaded (don't oversubscribe blind).
function rayonThreadCount() {
  const cores = self.navigator?.hardwareConcurrency;
  if (!cores) return 1;
  return Math.min(MAX_RAYON_THREADS, Math.max(1, cores - RESERVED_FOR_JS));
}

self.onmessage = async (e) => {
  if (e.data !== "start") return;
  try {
    postNow("phase", "booting wasm kimchi");
    const kimchi = await import("kimchi-napi");
    // Size the rayon pool BEFORE any proving call: wasi reports 1 CPU,
    // so the default global pool would be single-threaded.
    let threads = rayonThreadCount();
    // Guard against a build-time desync: the rayon count is bundled from
    // wasm-pool-config, but the pre-spawned pool size is baked into the
    // loader by a SEPARATE build (build:wasm). If they disagree (e.g.
    // KIMCHI_WASM_POOL_SIZE set for one build but not the other) and we
    // request more threads than the pool can serve, emnapi spawns a worker
    // on demand and DEADLOCKS. The loader exports its baked size; clamp to
    // it and warn loudly rather than hang.
    const bakedPool = kimchi.wasmThreadPoolSize;
    if (typeof bakedPool === "number" && threads > bakedPool - ASYNC_POOL_SIZE) {
      const safe = Math.max(1, bakedPool - ASYNC_POOL_SIZE);
      postNow("log", {
        severity: "warning",
        text:
          `[worker] rayon threads (${threads}) exceed the loader's pool capacity ` +
          `(pool ${bakedPool} - async ${ASYNC_POOL_SIZE} = ${bakedPool - ASYNC_POOL_SIZE}); the wasm ` +
          `backend and web bundle were built with different KIMCHI_WASM_POOL_SIZE. Clamping to ${safe} ` +
          `to avoid a worker-pool deadlock — rebuild both with the same value.`,
      });
      threads = safe;
    }
    kimchi.initThreadPool(threads);
    postNow("log", {
      severity: "info",
      text:
        `[worker] wasm kimchi ready, rayon pool: ${threads} threads ` +
        `(hardwareConcurrency=${self.navigator?.hardwareConcurrency}, ` +
        `crossOriginIsolated=${self.crossOriginIsolated})`,
    });

    const { runSimulation } = await import("../output-es/Snarky.Example.Web.Engine/index.js");
    runSimulation({
      onLog: post("log"),
      onPhase: post("phase"),
      onTxs: post("txs"),
      onScan: post("scan"),
      onVerified: post("verified"),
    })();
  } catch (err) {
    postNow("log", { severity: "error", text: "[worker] " + (err?.stack ?? String(err)) });
    postNow("phase", "failed");
  }
};

postNow("phase", "worker ready");
