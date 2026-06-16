// The P2P prover worker — pure compute. Owns the wasm kimchi backend (the
// `kimchi-napi` import is aliased to the wasi-browser loader in vite.config.mjs)
// and runs ONE of two roles per the start message, over a BRIDGED transport: the
// real transport (BroadcastChannel / WebRTC) lives on the MAIN thread (p2p-boot.js)
// and is relayed in here via p2p-bridge.js, so this worker can block on synchronous
// proving without ever stalling the network connection (and WebRTC works at all —
// RTCPeerConnection isn't available in a Worker).
//
//   coordinator  the block producer. Proves nothing itself: drives the shared
//                one-block engine (runCoordinator), farming every base AND merge
//                job to the pool of remote peers and verifying the root.
//   peer         a full-core prover. Runs runWorkerPeer: compile the circuit
//                once, then answer each `Assign` with a proof.
//
// Everything heavy is imported LAZILY after the wasm pool is sized: buildProver /
// the backend pull in the snarky-kimchi FFI, which `require`s kimchi at module
// load — importing them before `initThreadPool` would reverse that order and hang.
import { MAX_RAYON_THREADS, ASYNC_POOL_SIZE } from "../../../kimchi-napi/wasm-pool-config.mjs";
import { mkBridgedTransport } from "./p2p-bridge.js";

// Keep one core for this worker's own JS (witness generation, the event loop
// servicing the wasi threads) between Rust phases.
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

const bridge = mkBridgedTransport();
let started = false;

self.onmessage = async (e) => {
  const m = e.data;
  if (!m) return;
  // Transport-bridge frames from the main relay (myId / inbound msg / peer).
  if (m._t) { bridge.handleMessage(m); return; }
  if (m.type !== "start" || started) return;
  started = true;
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

    // Wait for the main relay to hand us our transport id before announcing.
    await bridge.ready;
    postNow("log", { severity: "info", text: `[${role}] transport id ${bridge.transport.myId}` });

    if (role === "coordinator") {
      const { runCoordinator } = await import("../output-es/Snarky.Example.P2P.Backend/index.js");
      runCoordinator(bridge.transport)(m.poolSize || 2)({
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
      runWorkerPeer(bridge.transport)();
      postNow("phase", "ready — awaiting work");
      postNow("log", { severity: "info", text: `[peer] compiled; awaiting work` });
    }
  } catch (err) {
    postNow("log", { severity: "error", text: `[${role}] ` + (err?.stack ?? String(err)) });
    postNow("phase", "failed");
  }
};

postNow("phase", "worker loaded");
