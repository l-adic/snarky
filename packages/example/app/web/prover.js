// The coordinator's OWN prover, as a nested Web Worker (spawned by p2p-worker.js)
// so it proves ASYNC — in its own thread — without freezing the coordinator. It
// compiles its own circuit (so the coordinator machine compiles twice: its engine
// + this prover) and answers job RPCs over postMessage, driven by the PS backend
// (Snarky.Example.P2P.Backend) like any other pool worker.
//
// Same boot-ordering constraint as p2p-worker.js: import + initThreadPool the wasm
// backend BEFORE importing the kimchi-loading PS (`Snarky.Example.Prover`).
//
// Protocol (PS backend ↔ this worker):
//   backend → worker:  { type:"init", chain, depth, threads } | { type:"job", work }
//   worker → backend:  { tag:"proof", proof } | { tag:"reject", reason }
import { MAX_RAYON_THREADS, ASYNC_POOL_SIZE } from "../../../kimchi-napi/wasm-pool-config.mjs";

const RESERVED_FOR_JS = 1;

function rayonThreadCount(override) {
  if (override) return Math.max(1, override | 0);
  const cores = self.navigator?.hardwareConcurrency;
  if (!cores) return 1;
  return Math.min(MAX_RAYON_THREADS, Math.max(1, cores - RESERVED_FOR_JS));
}

let prove = null; // (encoded WorkItem) -> encoded proof, set once compiled
const queued = []; // jobs that arrived before `prove` was ready (init is async)

// Prove one job synchronously (in THIS worker's thread — the coordinator stays
// free) and reply.
function runJob(work) {
  try {
    self.postMessage({ tag: "proof", proof: prove(work)() });
  } catch (err) {
    self.postMessage({ tag: "reject", reason: String(err?.message ?? err) });
  }
}

self.onmessage = async (e) => {
  const m = e.data;
  if (m.type === "init") {
    try {
      const kimchi = await import("kimchi-napi");
      let threads = rayonThreadCount(m.threads);
      const baked = kimchi.wasmThreadPoolSize;
      if (typeof baked === "number" && threads > baked - ASYNC_POOL_SIZE) {
        threads = Math.max(1, baked - ASYNC_POOL_SIZE);
      }
      kimchi.initThreadPool(threads);
      // LAZY (post-init) import of the kimchi-loading PS, then compile the circuit.
      // The logger forwards SRS/compile + status to the coordinator (it relays
      // "log" messages to its UI); see WorkerLog / P2P.Backend.
      const { mkPostLogger } = await import("../output-es/Snarky.Example.Web.P2P.WorkerLog/index.js");
      const { buildBrowserProver } = await import("../output-es/Snarky.Example.Web.Prover/index.js");
      // buildBrowserProver opens the shared IndexedDB SRS cache and compiles
      // through it (async cache I/O), so it returns a Promise; await it.
      prove = await buildBrowserProver(mkPostLogger())({ chain: m.chain, depth: m.depth })();
      // Compiled: announce readiness. The backend waits for this before marking
      // us an available pool worker, so the pool starts a job's timeout only
      // AFTER we are warm — otherwise the first job's timeout would have to cover
      // the whole (multi-minute) compile and we'd time out on it. (Mirrors a
      // remote peer, which only announces Join after it finishes compiling.)
      self.postMessage({ tag: "ready" });
      // Drain any jobs that arrived while we were compiling (with the ready-gate
      // none should, but init is async so keep this for safety — run in order).
      for (const work of queued.splice(0)) runJob(work);
    } catch (err) {
      // Init/compile failed — "error" both unblocks the backend's ready-wait and
      // reports the failure, so the pool drops this worker instead of hanging.
      self.postMessage({ tag: "error", reason: "init failed: " + String(err?.message ?? err) });
    }
  } else if (m.type === "job") {
    if (prove) runJob(m.work);
    else queued.push(m.work);
  }
};
