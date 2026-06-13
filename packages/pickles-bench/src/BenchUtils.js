
import { performance, PerformanceObserver } from "perf_hooks";
import v8 from "v8";
import { createRequire } from "module";
import fs from "fs";
import path from "path";
import { execSync } from "child_process";

const require = createRequire(import.meta.url);
const crypto = require("kimchi-napi");

const GCKinds = {
  1: "Scavenge",
  2: "MarkSweepCompact",
  4: "IncrementalMarking",
  8: "WeakPhantom",
  15: "All"
};

/**
 * Enhanced Benchmarking Utilities for Snarky / Pickles
 */
export class BenchUtils {
  static #ffiMetrics = {
    rustTimeNs: 0n,
    callCount: 0,
    calls: new Map(), // name -> { timeNs, count }
  };

  static #gcMetrics = [];
  static #obs = null;
  static #ffiInstalled = false;
  // Gating flag: the FFI wrappers are installed once at boot (so the
  // monkey-patch sits on the cached `kimchi-napi` singleton everyone
  // calls into), but counters only accumulate while this is `true`.
  // Set by `startFfiTracking()` at the start of a timed sample, cleared
  // by `stopFfiTracking()` at the end. Setup work (mkBenchSrs prewarm,
  // prepareProve's compile + b0) runs with the flag `false` and is not
  // counted at all — no reset of a polluted accumulator needed.
  static #ffiActive = false;

  /**
   * (5) Distinguish PureScript from Rust with 100% certainty.
   * Wraps all exported FUNCTIONS from kimchi-napi. Idempotent.
   *
   * Skips PascalCase exports (`Wasm*` / `Napi*` napi class constructors):
   * wrapping a constructor breaks `new k.WasmVecVecFp(...)` — the plain
   * wrapper, invoked with `new`, returns an object without the class
   * methods (e.g. `.push`), so downstream prover code throws
   * "vv.push is not a function".
   */
  static installFfiWrappers() {
    if (BenchUtils.#ffiInstalled) return;
    BenchUtils.#ffiInstalled = true;
    for (const name in crypto) {
      if (/^[A-Z]/.test(name)) continue;
      if (typeof crypto[name] === "function") {
        const orig = crypto[name];
        crypto[name] = function (...args) {
          // Fast path when tracking is off (setup region): no timing,
          // no map lookup, just forward.
          if (!BenchUtils.#ffiActive) {
            return orig.apply(this, args);
          }
          const s = process.hrtime.bigint();
          try {
            return orig.apply(this, args);
          } finally {
            const delta = process.hrtime.bigint() - s;
            BenchUtils.#ffiMetrics.rustTimeNs += delta;
            BenchUtils.#ffiMetrics.callCount++;

            let m = BenchUtils.#ffiMetrics.calls.get(name) || { timeNs: 0n, count: 0 };
            m.timeNs += delta;
            m.count++;
            BenchUtils.#ffiMetrics.calls.set(name, m);
          }
        };
      }
    }
  }

  /**
   * Activate the FFI counters. Resets accumulators and flips the gate
   * so the wrappers (installed once by `installFfiWrappers`) start
   * timing. Call at the start of a timed sample, AFTER all untimed
   * setup; the matching `stopFfiTracking()` call below closes the
   * window before `report()` prints the summary.
   */
  static startFfiTracking(label) {
    BenchUtils.#ffiMetrics.rustTimeNs = 0n;
    BenchUtils.#ffiMetrics.callCount = 0;
    BenchUtils.#ffiMetrics.calls = new Map();
    BenchUtils.#ffiActive = true;
    // Window marker on the SAME stream as `--trace-gc` (stdout), using the
    // same timestamp base (ms since process start) — `parse_gclog.mjs`
    // attributes GC lines between start/end markers to this trial.
    console.log(
      "[bench-window] start " + (process.uptime() * 1000).toFixed(0) + " " + (label || "")
    );
  }

  static stopFfiTracking(label) {
    BenchUtils.#ffiActive = false;
    console.log(
      "[bench-window] end " + (process.uptime() * 1000).toFixed(0) + " " + (label || "")
    );
  }

  // ---- machine-readable results ------------------------------------
  // Per-bench accumulation: `captureTrial` snapshots the FFI window at
  // the end of each timed trial; `recordBenchSamples` adds benchlib's
  // wall-time samples at onBenchFinish; `writeResults` assembles one
  // JSON artifact for the whole run (regression baseline / compare).

  static #results = new Map(); // benchName -> { trials: [], samples: [] }

  static #resultsFor(name) {
    let r = BenchUtils.#results.get(name);
    if (!r) {
      r = { trials: [], samples: [] };
      BenchUtils.#results.set(name, r);
    }
    return r;
  }

  static captureTrial(label) {
    const m = BenchUtils.#ffiMetrics;
    BenchUtils.#resultsFor(label).trials.push({
      rustMs: Number(m.rustTimeNs) / 1e6,
      ffiCalls: m.callCount,
      perCall: [...m.calls.entries()]
        .sort((a, b) => Number(b[1].timeNs - a[1].timeNs))
        .map(([name, c]) => ({ name, ms: Number(c.timeNs) / 1e6, count: c.count })),
    });
  }

  static recordBenchSamples(name, samples) {
    BenchUtils.#resultsFor(name).samples = samples;
  }

  static writeResults() {
    const sh = (cmd) => {
      try { return execSync(cmd, { encoding: "utf8" }).trim(); } catch { return null; }
    };
    const benches = [...BenchUtils.#results.entries()].map(([name, r]) => {
      const ms = r.samples.map((s) => s.ms);
      const n = ms.length;
      const mean = n ? ms.reduce((a, b) => a + b, 0) / n : null;
      const stddev = n > 1
        ? Math.sqrt(ms.reduce((a, b) => a + (b - mean) * (b - mean), 0) / (n - 1))
        : null;
      const rust = r.trials.map((t) => t.rustMs);
      const rustMean = rust.length ? rust.reduce((a, b) => a + b, 0) / rust.length : null;
      return {
        name,
        samples: r.samples,
        stats: { n, meanMs: mean, stddevMs: stddev, minMs: n ? Math.min(...ms) : null, maxMs: n ? Math.max(...ms) : null },
        ffi: {
          rustMeanMs: rustMean,
          rustShare: rustMean != null && mean ? rustMean / mean : null,
          trials: r.trials,
        },
      };
    });
    const out = {
      date: new Date().toISOString(),
      gitSha: process.env.GIT_SHA || sh("git rev-parse HEAD"),
      gitDirty: sh("git status --porcelain") ? true : false,
      node: process.version,
      // V8 flags change GC behavior (e.g. --max-semi-space-size) — results
      // are only comparable between runs with identical flags.
      nodeFlags: process.execArgv,
      // Same-machine artifacts are only comparable at the same power
      // profile: power-saver clamps this box from 5.2GHz to ~1.5GHz
      // (observed 2026-06-11: identical code, 22s vs 42s compile).
      powerProfile: sh("powerprofilesctl get 2>/dev/null") || "unknown",
      benches,
    };
    const sha = (out.gitSha || "unknown").slice(0, 9);
    const file = process.env.BENCH_RESULTS_FILE
      || path.join("bench-results", sha + "-" + out.date.replace(/[:.]/g, "-") + ".json");
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, JSON.stringify(out, null, 2));
    console.log("[bench-results] " + file);
  }

  /**
   * (1) Tracking Garbage Generation over time.
   * Uses PerformanceObserver to listen for 'gc' events.
   * 'detail' contains { beforeGC, afterGC } which is very precise.
   */
  static startGcTracking() {
    this.#gcMetrics = [];
    this.#obs = new PerformanceObserver((list) => {
      for (const entry of list.getEntries()) {
        const detail = entry.detail || {};
        this.#gcMetrics.push({
          time: entry.startTime,
          duration: entry.duration,
          kind: entry.kind,
          before: detail.beforeGC,
          after: detail.afterGC,
          collected: (detail.beforeGC || 0) - (detail.afterGC || 0),
        });
      }
    });
    this.#obs.observe({ entryTypes: ["gc"] });
  }

  static stopGcTracking() {
    if (this.#obs) {
      this.#obs.disconnect();
    }
    return this.#gcMetrics;
  }

  /**
   * (1) "Where is it coming from" - Identifying object types.
   * takeHeapSnapshot returns a stream that can be analyzed for constructors.
   */
  static takeHeapSnapshot(filepath) {
    const snapshotStream = v8.getHeapSnapshot();
    const fileStream = fs.createWriteStream(filepath);
    snapshotStream.pipe(fileStream);
    return new Promise((resolve, reject) => {
      fileStream.on('finish', resolve);
      fileStream.on('error', reject);
    });
  }

  /**
   * Report summary of the benchmark run.
   */
  static report() {
    console.log("\n--- Benchmarking Report ---");
    
    const totalRustMs = Number(this.#ffiMetrics.rustTimeNs) / 1e6;
    console.log(`Rust FFI Time: ${totalRustMs.toFixed(2)}ms (${this.#ffiMetrics.callCount} calls)`);
    
    const sortedCalls = [...this.#ffiMetrics.calls.entries()]
      .sort((a, b) => Number(b[1].timeNs - a[1].timeNs))
      .slice(0, 10);
    
    console.log("Top 10 Rust Functions:");
    for (const [name, m] of sortedCalls) {
      console.log(`  - ${name}: ${(Number(m.timeNs) / 1e6).toFixed(2)}ms (${m.count} calls)`);
    }

    const totalCollected = this.#gcMetrics.reduce((acc, m) => acc + (m.collected || 0), 0);
    console.log(`Total Garbage Collected: ${(totalCollected / 1024 / 1024).toFixed(2)} MB`);
    console.log(`GC Events: ${this.#gcMetrics.length}`);
    
    if (this.#gcMetrics.length > 0) {
        const majorGCs = this.#gcMetrics.filter(m => m.kind === 'major');
        console.log(`Major GC Events: ${majorGCs.length}`);
    }
  }
}

// PureScript FFI bridge. `Bench.Pickles.BenchUtils` imports these as
// top-level named exports; the class above only has statics, which the
// ESM `import { ... } from "./foreign.js"` cannot see. Effect a = a
// nullary thunk; `String -> Effect Unit` = curried.
export const installFfiWrappers = () => {
  BenchUtils.installFfiWrappers();
};

export const startFfiTracking = (label) => () => {
  BenchUtils.startFfiTracking(label);
};

export const stopFfiTracking = (label) => () => {
  BenchUtils.stopFfiTracking(label);
};

export const captureTrial = (label) => () => {
  BenchUtils.captureTrial(label);
};

export const recordBenchSamples = (name) => (samples) => () => {
  BenchUtils.recordBenchSamples(name, samples);
};

export const writeResults = () => {
  BenchUtils.writeResults();
};

export const startGcTracking = () => {
  BenchUtils.startGcTracking();
};

export const stopGcTracking = () => BenchUtils.stopGcTracking();

export const takeHeapSnapshot = (filepath) => () => {
  BenchUtils.takeHeapSnapshot(filepath);
};

export const report = () => {
  BenchUtils.report();
};

// Force a V8 GC if node ran with --expose-gc (no-op otherwise). Called
// between trials so no trial inherits the previous one's garbage — and,
// under KIMCHI_BACKEND=wasm, so dead napi externals (~500MB prover
// indexes) are finalized back to the wasm allocator before the next
// trial allocates (wasm32 has a hard 4GB ceiling; finalizers run via
// FinalizationRegistry a tick AFTER gc, hence callers gc-yield-gc).
export const forceGc = () => {
  if (globalThis.gc) globalThis.gc();
};
