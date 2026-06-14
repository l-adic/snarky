// Prover RPC service worker for the P2P app. Owns the wasm kimchi backend
// (aliased to the wasi-browser loader in vite.config.mjs) and the compiled
// circuit; answers init/seed/merge/verify requests from the main thread.
// No transport, no UI — pure compute. Protocol:
//   main → worker:  { rpc:id, method, params }
//   worker → main:  { rpc:id, ok } | { rpc:id, err }   (RPC responses)
//                   { ev:"log", severity, text }        (log events)
import { MAX_RAYON_THREADS } from "../../../kimchi-napi/wasm-pool-config.mjs";

const RESERVED_FOR_JS = 1;
// Optional override (set via a {config:{threads}} message before init) so
// several provers can share one machine without oversubscribing the CPU — e.g.
// running a base + merge peer in two tabs. Default: cores - 1 (capped).
function rayonThreadCount() {
  if (self.__cfgThreads) return Math.max(1, self.__cfgThreads | 0);
  const cores = self.navigator?.hardwareConcurrency;
  if (!cores) return 1;
  return Math.min(MAX_RAYON_THREADS, Math.max(1, cores - RESERVED_FOR_JS));
}

// ProverService's log hook → forward structured lines to the page.
globalThis.__svcLog = (o) => self.postMessage({ ev: "log", severity: o.severity, text: o.text });

let st = null; // compiled ServiceState
let booted = false;
let Service = null;

async function boot() {
  if (booted) return;
  booted = true;
  const kimchi = await import("kimchi-napi");
  const threads = rayonThreadCount();
  kimchi.initThreadPool(threads);
  self.postMessage({ ev: "log", severity: "info", text: `[worker] wasm ready, rayon ${threads} threads (COI=${self.crossOriginIsolated})` });
  Service = await import("../output-es/Snarky.Example.P2P.ProverService/index.js");
}

self.onmessage = async (e) => {
  const m = e.data;
  // config message (e.g. a rayon-thread override) before the first RPC
  if (m && m.config) { if (m.config.threads) self.__cfgThreads = m.config.threads; return; }
  if (!m || typeof m.rpc !== "number") return;
  try {
    if (m.method === "init") {
      await boot();
      Service.initService((state) => () => {
        st = state;
        self.postMessage({ rpc: m.rpc, ok: { fingerprint: Service.fingerprint(state) } });
      })((msg) => () => {
        self.postMessage({ rpc: m.rpc, err: msg });
      })();
      return;
    }
    if (!st) throw new Error("prover not initialized — call init first");
    if (m.method === "seed") {
      self.postMessage({ rpc: m.rpc, ok: Service.seedBlock(st)() });
    } else if (m.method === "genBlock") {
      self.postMessage({ rpc: m.rpc, ok: Service.genBlock(st)() });
    } else if (m.method === "proveLeaf") {
      self.postMessage({ rpc: m.rpc, ok: Service.proveBaseLeaf(st)(m.params.j)() });
    } else if (m.method === "merge") {
      self.postMessage({ rpc: m.rpc, ok: Service.merge(st)(m.params)() });
    } else if (m.method === "verify") {
      self.postMessage({ rpc: m.rpc, ok: Service.verifyWire(st)(m.params.wire)() });
    } else {
      throw new Error("unknown rpc method: " + m.method);
    }
  } catch (err) {
    self.postMessage({ rpc: m.rpc, err: String(err?.stack ?? err) });
  }
};
