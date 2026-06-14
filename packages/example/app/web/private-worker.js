// Web Worker for the PRIVACY split: owns the wasm kimchi backend (the
// `kimchi-napi` import is aliased to the wasi-browser loader in
// vite.config.mjs) and runs `Snarky.Example.WebBase`, which compiles the
// circuit, generates a block, proves the per-transaction BASE proofs
// LOCALLY (private witnesses stay on-device), and POSTs only the proofs +
// public statements to the server's /merge endpoint (vite proxies it to
// merge-server.mjs). Lives off the UI thread because proving is synchronous.
//
// Bridges WebBase's globalThis hooks + console + errors to a uniform
// { type, value } postMessage protocol consumed by Snarky.Example.Web.Private.Worker.
import { MAX_RAYON_THREADS } from "../../../kimchi-napi/wasm-pool-config.mjs";

// Keep one core for this worker's own JS (witness generation, the event
// loop servicing the wasi threads) between Rust phases.
const RESERVED_FOR_JS = 1;

function rayonThreadCount() {
  const cores = self.navigator?.hardwareConcurrency;
  if (!cores) return 1;
  return Math.min(MAX_RAYON_THREADS, Math.max(1, cores - RESERVED_FOR_JS));
}

const post = (type, value) => self.postMessage({ type, value });

// WebBase's foreign hooks (Snarky.Example.WebBase.{postLeaf,postStatus,postLog}).
globalThis.__postLeaf = (obj) => post("leaf", obj);
globalThis.__postStatus = (s) => post("status", s);
// Structured log lines {severity, text} from the engine logger.
globalThis.__postLog = (obj) => post("log", obj);

// Stray console output (not the colog stream, which goes via __postLog) is
// forwarded as info-severity lines so nothing is lost.
for (const lvl of ["log", "info", "warn", "error"]) {
  const orig = console[lvl].bind(console);
  console[lvl] = (...a) => {
    const text = a.map((x) => (typeof x === "string" ? x : String(x))).join(" ");
    post("log", { severity: lvl === "log" ? "info" : lvl === "warn" ? "warning" : lvl, text });
    orig(...a);
  };
}
self.addEventListener("error", (e) => post("error", String(e.message)));
self.addEventListener("unhandledrejection", (e) => post("error", String(e.reason?.stack ?? e.reason)));

let booted = false;
self.onmessage = async (e) => {
  if (e.data !== "run" || booted) return;
  booted = true;
  try {
    post("status", "booting wasm kimchi");
    const kimchi = await import("kimchi-napi");
    // Size the rayon pool BEFORE any proving call: wasi reports 1 CPU,
    // so the default global pool would be single-threaded.
    const threads = rayonThreadCount();
    kimchi.initThreadPool(threads);
    post("log", { severity: "info", text: `[worker] wasm kimchi ready, rayon pool: ${threads} threads (crossOriginIsolated=${self.crossOriginIsolated})` });

    const { baseMain } = await import("../output-es/Snarky.Example.WebBase/index.js");
    baseMain();
  } catch (err) {
    post("error", String(err?.stack ?? err));
    post("status", "failed");
  }
};

post("status", "worker ready");
