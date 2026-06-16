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
      const { buildProver } = await import("../output-es/Snarky.Example.Prover/index.js");
      prove = buildProver({ chain: m.chain, depth: m.depth })();
      // Drain any jobs that arrived while we were compiling (init is async, so a
      // job message can interleave before `prove` is set — run them now, in order).
      for (const work of queued.splice(0)) runJob(work);
    } catch (err) {
      self.postMessage({ tag: "reject", reason: "init failed: " + String(err?.message ?? err) });
    }
  } else if (m.type === "job") {
    if (prove) runJob(m.work);
    else queued.push(m.work);
  }
};
