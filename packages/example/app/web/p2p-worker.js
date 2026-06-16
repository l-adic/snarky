// The P2P prover worker. Owns the wasm kimchi backend (the `kimchi-napi` import
// is aliased to the wasi-browser loader in vite.config.mjs) and a `Transport`,
// then runs ONE of two roles per the start message:
//
//   coordinator  the block producer. Proves nothing itself: drives the shared
//                one-block engine over `Snarky.Example.P2P.Backend.runCoordinator`,
//                farming every base AND merge job to the pool of remote peers and
//                verifying the root. Forwards the engine's callbacks to the page.
//   peer         a full-core prover. Runs `Snarky.Example.P2P.WorkerPeer`:
//                compile the circuit once, then answer each `Assign` with a proof.
//
// Everything heavy is imported LAZILY after the wasm pool is sized: `buildProver`
// /the backend pull in the snarky-kimchi FFI, which `require`s kimchi at module
// load — importing them before `initThreadPool` would reverse that order and
// hang (see prover-entry.js / worker-entry.js for the same constraint).
import { MAX_RAYON_THREADS, ASYNC_POOL_SIZE } from "../../../kimchi-napi/wasm-pool-config.mjs";
import { mkTransport } from "./p2p-mk-transport.js";

// Keep one core for this worker's own JS (witness generation, the event loop
// servicing the wasi threads / the transport) between Rust phases.
const RESERVED_FOR_JS = 1;

const post = (tag) => (value) => () => self.postMessage({ tag, value });
const postNow = (tag, value) => self.postMessage({ tag, value });

// rayon pool size: cores - 1, capped at the pre-spawned pool. An explicit
// `threads` override lets several roles share one machine in the headless test
// without oversubscribing the CPU. Unreported core count → single-threaded.
function rayonThreadCount(override) {
  if (override) return Math.max(1, override | 0);
  const cores = self.navigator?.hardwareConcurrency;
  if (!cores) return 1;
  return Math.min(MAX_RAYON_THREADS, Math.max(1, cores - RESERVED_FOR_JS));
}

self.onmessage = async (e) => {
  const m = e.data;
  if (!m || m.type !== "start") return;
  const role = m.role === "coordinator" ? "coordinator" : "peer";
  try {
    postNow("phase", "booting wasm kimchi");
    const kimchi = await import("kimchi-napi");
    let threads = rayonThreadCount(m.threads);
    // Clamp to the loader's baked pool to avoid a worker-pool deadlock if the
    // wasm backend and web bundle were built with different pool sizes.
    const bakedPool = kimchi.wasmThreadPoolSize;
    if (typeof bakedPool === "number" && threads > bakedPool - ASYNC_POOL_SIZE) {
      threads = Math.max(1, bakedPool - ASYNC_POOL_SIZE);
    }
    kimchi.initThreadPool(threads);
    postNow("log", {
      severity: "info",
      text: `[${role}] wasm kimchi ready, rayon ${threads} threads (crossOriginIsolated=${self.crossOriginIsolated})`,
    });

    const transport = await mkTransport(m.transport || "bc", m.session || "snarky-p2p");
    postNow("log", { severity: "info", text: `[${role}] joined session '${m.session}' as ${transport.myId} over ${m.transport || "bc"}` });

    if (role === "coordinator") {
      const { runCoordinator } = await import("../output-es/Snarky.Example.P2P.Backend/index.js");
      runCoordinator(transport)(m.poolSize || 2)({
        onLog: post("log"),
        onPhase: post("phase"),
        onTxs: post("txs"),
        onScan: post("scan"),
        onVerified: post("verified"),
      })();
    } else {
      const { runWorkerPeer } = await import("../output-es/Snarky.Example.P2P.WorkerPeer/index.js");
      postNow("phase", "compiling circuit");
      // Synchronous: buildProver compiles the circuit before returning, then the
      // peer is live (announces + listens for Assign).
      runWorkerPeer(transport)();
      postNow("phase", "ready — awaiting work");
      postNow("log", { severity: "info", text: `[peer] compiled; awaiting work` });
    }
  } catch (err) {
    postNow("log", { severity: "error", text: `[${role}] ` + (err?.stack ?? String(err)) });
    postNow("phase", "failed");
  }
};

postNow("phase", "worker loaded");
