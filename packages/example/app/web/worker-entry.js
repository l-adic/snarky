// The coordinator Web Worker: runs the engine + snark manager over a POOL of
// prover Web Workers (prover-entry.js), spawned from here — the
// coordinator-spawns-provers topology validated by the spike. The coordinator
// still loads wasm kimchi itself (it compiles once for the verifier and decodes
// the proofs the provers send back); the provers do the actual proving in
// parallel. Bridges the engine's callbacks to postMessage for the UI thread.
//
// Everything heavy is imported LAZILY inside the message handler so the worker
// is responsive immediately and any wasm-init failure is caught and forwarded
// to the UI log instead of dying silently.
import { MAX_RAYON_THREADS, ASYNC_POOL_SIZE } from "../../../kimchi-napi/wasm-pool-config.mjs";

// Browser pool size. Memory-bound: this is POOL_SIZE+1 wasm instances in one
// tab (coordinator + provers), each up to the wasm32 4GB ceiling, so keep it
// small. 2 proves the pattern; raise only if the tab has the headroom.
const POOL_SIZE = 2;

const post = (tag) => (value) => () => self.postMessage({ tag, value });
const postNow = (tag, value) => self.postMessage({ tag, value });

// Each of the POOL_SIZE+1 wasm instances takes an even share of the cores for
// rayon, so they don't oversubscribe. Clamped to the loader's pre-spawned pool.
function rayonThreadCount() {
  const cores = self.navigator?.hardwareConcurrency;
  if (!cores) return 1;
  return Math.min(MAX_RAYON_THREADS, Math.max(1, Math.floor(cores / POOL_SIZE)));
}

self.onmessage = async (e) => {
  if (e.data !== "start") return;
  try {
    postNow("phase", "booting wasm kimchi");
    const kimchi = await import("kimchi-napi");

    let threads = rayonThreadCount();
    const bakedPool = kimchi.wasmThreadPoolSize;
    if (typeof bakedPool === "number" && threads > bakedPool - ASYNC_POOL_SIZE) {
      threads = Math.max(1, bakedPool - ASYNC_POOL_SIZE);
    }
    kimchi.initThreadPool(threads);
    postNow("log", {
      severity: "info",
      text:
        `[coordinator] wasm kimchi ready; pool ${POOL_SIZE} workers x ${threads} rayon threads ` +
        `(cores=${self.navigator?.hardwareConcurrency}, crossOriginIsolated=${self.crossOriginIsolated})`,
    });

    const { runSimulationPool } = await import("../output-es/Snarky.Example.Web.Pool/index.js");
    // The literal `new Worker(new URL(...))` is what vite must see HERE (in the
    // coordinator module) to emit + wire the prover chunk.
    const spawnProver = () =>
      new Worker(new URL("./prover-entry.js", import.meta.url), { type: "module" });

    runSimulationPool(POOL_SIZE)(spawnProver)({
      onLog: post("log"),
      onPhase: post("phase"),
      onTxs: post("txs"),
      onScan: post("scan"),
      onVerified: post("verified"),
    })();
  } catch (err) {
    postNow("log", { severity: "error", text: "[coordinator] " + (err?.stack ?? String(err)) });
    postNow("phase", "failed");
  }
};

postNow("phase", "worker ready");
