// Measures wall-time spent INSIDE the Rust kimchi prover, by wrapping
// the two synchronous napi calls `caml_pasta_f{p,q}_plonk_proof_create`
// on the shared `kimchi-napi` CommonJS singleton. Prove/FFI.js calls
// these via `k.<fn>(...)` at call time, so patching the same cached
// module object is seen — no production edit.
//
// This is the only instrument that can attribute Rust time: the V8
// CPU profiler is blind inside native code. Total prove wall is
// measured with the same clock so the JS-vs-Rust split is exact.
import { createRequire } from "module";
import { performance } from "perf_hooks";

const require = createRequire(import.meta.url);
const k = require("kimchi-napi");

let accNs = 0n;
let calls = 0;
let t0 = 0;

const wrap = (obj, name) => {
  const orig = obj[name];
  if (typeof orig !== "function") {
    throw new Error("FfiTimer: kimchi-napi." + name + " is not a function");
  }
  obj[name] = function (...args) {
    const s = process.hrtime.bigint();
    try {
      return orig.apply(this, args);
    } finally {
      accNs += process.hrtime.bigint() - s;
      calls += 1;
    }
  };
};

// Wrap the two prover napi calls once. Idempotent — safe to call per
// timed sample without double-wrapping (which would double-count).
let wrapped = false;
export const install = () => {
  if (wrapped) return;
  wrapped = true;
  wrap(k, "caml_pasta_fp_plonk_proof_create");
  wrap(k, "caml_pasta_fq_plonk_proof_create");
};

// Reset counters and mark t0. Call at the start of each timed sample,
// AFTER one-time setup (NRR + b0), so only the timed prove is counted.
export const start = () => {
  accNs = 0n;
  calls = 0;
  t0 = performance.now();
  // process.uptime() shares V8's --trace-gc timestamp base (ms since
  // process start) — lets the analysis window GC lines to the prove,
  // excluding the untimed setup's GCs.
  console.log(
    "[gc-window] prove-start " + (process.uptime() * 1000).toFixed(0) + " ms"
  );
};

export const reportSplit = () => {
  console.log(
    "[gc-window] prove-end " + (process.uptime() * 1000).toFixed(0) + " ms"
  );
  const total = performance.now() - t0;
  const rust = Number(accNs) / 1e6;
  const js = total - rust;
  const pct = (x) => ((100 * x) / total).toFixed(1);
  console.log(
    "[prove split] total=" +
      total.toFixed(0) +
      "ms  rust-ffi=" +
      rust.toFixed(0) +
      "ms (" +
      pct(rust) +
      "%, " +
      calls +
      " calls)  js-side=" +
      js.toFixed(0) +
      "ms (" +
      pct(js) +
      "%)"
  );
};
