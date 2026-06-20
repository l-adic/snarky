// bench-harness — the ONE benchmark runner + measurement utils, shared by every
// stack (PureScript/snarky, o1js). Backend-neutral: no kimchi, no PureScript, no
// o1js imports. Each site binds to this (PS via an FFI module, TS via index.d.ts)
// and supplies only a `Group[]` (the workload) + optional `hooks` (site-specific
// per-trial instrumentation, e.g. PS's napi FFI counters).
//
// "Same harness" is literal: both sides resolve THIS module and call THIS
// `runBench`. Replaces the PureScript `benchlib` suite/group/runNode + reporters
// and the TS hand-rolled loop with a single ~25-line runner.

import { performance, PerformanceObserver } from "perf_hooks";
import fs from "fs";
import path from "path";
import { execSync } from "child_process";

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const uptimeMs = () => (process.uptime() * 1000).toFixed(0);

// ---- window markers ------------------------------------------------------
// One line per timed region on stdout (same stream + timestamp base as
// `--trace-gc`), so `parse_gclog.mjs` attributes GC lines to the right trial.
export const windowStart = (label) =>
    console.log(`[bench-window] start ${uptimeMs()} ${label}`);
export const windowEnd = (label) =>
    console.log(`[bench-window] end ${uptimeMs()} ${label}`);

// Force a V8 GC if node ran with --expose-gc (no-op otherwise). Called between
// trials so no trial inherits the previous one's garbage.
export const forceGc = () => {
    if (globalThis.gc) globalThis.gc();
};

// ---- per-trial GC observer (main isolate) --------------------------------
// CAVEAT: observes the MAIN isolate only — wasm-backend prover worker heaps are
// invisible here AND to --trace-gc, so wasm-mode reclaim is a lower bound (true
// of every wasm stack, so wasm-vs-wasm pairings stay comparable).
let gcEvents = [];
let gcObs = null;

function startGcTracking() {
    gcEvents = [];
    gcObs = new PerformanceObserver((list) => {
        for (const e of list.getEntries()) {
            const d = e.detail ?? {};
            gcEvents.push({ collected: (d.beforeGC ?? 0) - (d.afterGC ?? 0) });
        }
    });
    gcObs.observe({ entryTypes: ["gc"] });
}

async function stopGcTrackingAndReport() {
    // Yield once so queued observer callbacks land before we disconnect — a
    // synchronous (native-backend) trial never turns the event loop, so every
    // GC entry is still pending here.
    await sleep(0);
    gcObs?.disconnect();
    const collected = gcEvents.reduce((a, e) => a + e.collected, 0);
    console.log("\n--- Benchmarking Report ---");
    console.log(`Total Garbage Collected: ${(collected / 1024 / 1024).toFixed(2)} MB`);
    console.log(`GC Events: ${gcEvents.length}`);
}

// ---- statistics ----------------------------------------------------------
export function stats(samples) {
    const xs = samples.map((s) => s.ms);
    const n = xs.length;
    const mean = n ? xs.reduce((a, b) => a + b, 0) / n : null;
    const stddev =
        n > 1 ? Math.sqrt(xs.reduce((a, x) => a + (x - mean) ** 2, 0) / (n - 1)) : null;
    return {
        n,
        meanMs: mean,
        stddevMs: stddev,
        minMs: n ? Math.min(...xs) : null,
        maxMs: n ? Math.max(...xs) : null,
    };
}

// The console spread line (was the PS `statsReporter`).
function logStats(samples) {
    const xs = samples.map((s) => s.ms);
    const n = xs.length;
    if (n < 2) return;
    const s = stats(samples);
    const f = (x) => x.toFixed(0);
    console.log(
        `      └─ ${n} trials  min=${f(s.minMs)}ms  max=${f(s.maxMs)}ms  ` +
            `mean=${f(s.meanMs)}ms  stddev=${f(s.stddevMs)}ms  ` +
            `(spread ${f(s.maxMs - s.minMs)}ms = ${((100 * (s.maxMs - s.minMs)) / s.meanMs).toFixed(1)}% of mean)`
    );
}

// ---- the runner ----------------------------------------------------------
// A Group = { label, trials, prepare, work }:
//   prepare() : Promise<void> — UNTIMED, run once before the group's trials
//               (= benchlib's `prepareInput`; for prove, the compile + warmup).
//   work()    : Promise<void> — the ONE timed unit, run `trials` times.
// hooks = { onStart?(label), onEnd?(label) } — optional per-trial site
//   instrumentation around the timed region (PS: napi FFI counters; o1js: none).
// Returns benches: [{ name, samples:[{iterations,ms}], stats }]. The caller
// attaches any site-specific per-bench data (e.g. PS `ffi`) and calls
// `writeArtifact`.
export async function runBench(groups, hooks = {}) {
    const benches = [];
    for (const { label, trials, prepare, work } of groups) {
        await prepare(); // untimed setup, once, in group order (keeps prove's
        // resident state out of an earlier group's measured region)
        const samples = [];
        for (let i = 0; i < trials; i++) {
            forceGc();
            await sleep(1);
            forceGc(); // gc → yield → gc: finalize last trial's garbage
            hooks.onStart?.(label);
            windowStart(label);
            startGcTracking();
            const t0 = performance.now();
            await work();
            const ms = performance.now() - t0;
            windowEnd(label);
            hooks.onEnd?.(label);
            await stopGcTrackingAndReport();
            samples.push({ iterations: 1, ms });
        }
        logStats(samples);
        benches.push({ name: label, samples, stats: stats(samples) });
    }
    return benches;
}

// ---- artifact ------------------------------------------------------------
// Writes the run's JSON to `$BENCH_RESULTS_FILE` or
// `bench-results/<sha>-<date>.json`. `payload` carries `suite` + `benches` and
// any site extras (PS: per-bench `ffi`; o1js: `backend`, `o1jsVersion`,
// `circuitRows`). The common machine fields are filled in here so every suite's
// artifact shares one schema (read by compare.mjs / parse_gclog.mjs).
export function writeArtifact(payload) {
    const sh = (cmd) => {
        try {
            return execSync(cmd, { encoding: "utf8" }).trim();
        } catch {
            return null;
        }
    };
    const out = {
        date: new Date().toISOString(),
        gitSha: process.env.GIT_SHA || sh("git rev-parse HEAD"),
        gitDirty: sh("git status --porcelain") ? true : false,
        node: process.version,
        nodeFlags: process.execArgv,
        powerProfile: sh("powerprofilesctl get 2>/dev/null") || "unknown",
        ...payload,
    };
    const sha = (out.gitSha || "unknown").slice(0, 9);
    const infix = payload.backend && payload.backend !== "native" ? payload.backend + "-" : "";
    const file =
        process.env.BENCH_RESULTS_FILE ||
        path.join("bench-results", `${infix}${sha}-${out.date.replace(/[:.]/g, "-")}.json`);
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, JSON.stringify(out, null, 2));
    console.log("[bench-results] " + file);
}
