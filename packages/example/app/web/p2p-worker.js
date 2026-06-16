// The P2P prover worker — pure compute. This JS owns only the boot sequence that
// can't be PureScript: the wasm backend must be imported and `initThreadPool`'d
// BEFORE the PS prover module is imported (importing it `require`s kimchi at
// load), so the heavy PS is pulled in LAZILY after boot. Once booted, the only
// JS→PS call is `main()` (its type is `Effect Unit`); the PS entry
// (Snarky.Example.Web.P2P.Worker) reads its role + the bridged transport from the
// globals set here and runs the role.
//
// The real transport lives on the MAIN thread (p2p-boot/Main); this worker gets a
// bridged proxy (transport/bridge.js) so it can block on synchronous proving without
// stalling the connection, and so WebRTC works (RTCPeerConnection isn't available
// in a Worker).
import { MAX_RAYON_THREADS, ASYNC_POOL_SIZE } from "../../../kimchi-napi/wasm-pool-config.mjs";
import { mkBridgedTransport } from "@webjs/transport";

// Keep one core for this worker's own JS between Rust phases.
const RESERVED_FOR_JS = 1;

const postNow = (tag, value) => self.postMessage({ tag, value });

function rayonThreadCount(override) {
  if (override) return Math.max(1, override | 0);
  const cores = self.navigator?.hardwareConcurrency;
  if (!cores) return 1;
  return Math.min(MAX_RAYON_THREADS, Math.max(1, cores - RESERVED_FOR_JS));
}

// Build the bridged transport up front so it buffers inbound frames from the main
// relay even before the PS role registers its handlers; expose it for the PS FFI.
const bridge = mkBridgedTransport();
globalThis.__p2pBridge = bridge;
let started = false;

self.onmessage = async (e) => {
  const m = e.data;
  if (!m) return;
  // Transport-bridge frames from the main relay (myId / inbound msg / peer).
  if (m._t) { bridge.handleMessage(m); return; }
  if (m.type !== "start" || started) return;
  started = true;
  const role = m.role === "coordinator" ? "coordinator" : "peer";
  globalThis.__p2pBoot = { role, threads: m.threads };
  // The coordinator's own prover runs as a NESTED worker (so it proves async,
  // off the coordinator's thread). Expose the factory + thread hint for the PS
  // backend's FFI; the `new URL("./prover.js", …)` literal must live here (a
  // worker-side file vite can resolve + bundle as a nested worker).
  if (role === "coordinator") {
    globalThis.__proverThreads = m.threads || 0;
    globalThis.__spawnProver = () => new Worker(new URL("./prover.js", import.meta.url), { type: "module" });
  }
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

    // Wait for the main relay to hand us our transport id before the role announces.
    await bridge.ready;
    postNow("log", { severity: "info", text: `[${role}] transport id ${bridge.transport.myId}` });

    // LAZY (post-boot) import of the heavy PS, then the single JS→PS call. The PS
    // entry owns the role's phases/logs from here (the engine for a coordinator,
    // runWorkerPeer for a peer).
    const { main } = await import("../output-es/Snarky.Example.Web.P2P.Worker/index.js");
    main();
  } catch (err) {
    postNow("log", { severity: "error", text: `[${role}] ` + (err?.stack ?? String(err)) });
    postNow("phase", "failed");
  }
};

postNow("phase", "worker loaded");
