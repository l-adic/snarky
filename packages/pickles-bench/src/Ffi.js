// The PS suite's site-specific instrumentation: time the kimchi-napi boundary so
// the artifact can report a Rust-vs-JS split (`ffi.rustShare`). This is the part
// the o1js suite CANNOT mirror (its kimchi is WASM inside the JS heap, no
// boundary to wrap), so it lives here on the PS side, not in the shared harness —
// supplied to `runBench` as the optional `onStart`/`onEnd` hooks.
import { createRequire } from "module";
const require = createRequire(import.meta.url);
const crypto = require("kimchi-napi");

let metrics = { rustTimeNs: 0n, callCount: 0, calls: new Map() };
let active = false; // counters accumulate only while a timed window is open
let installed = false;
const trialsByLabel = new Map(); // label -> [{ rustMs, ffiCalls, perCall }]

// Monkey-patch every exported kimchi-napi FUNCTION with a timing wrapper, ONCE.
// Skips PascalCase exports (napi class constructors — wrapping them breaks `new`).
// Counters stay inert until `onStart` flips `active`, so untimed setup is free.
export const installFfiWrappers = () => {
    if (installed) return;
    installed = true;
    for (const name in crypto) {
        if (/^[A-Z]/.test(name)) continue;
        if (typeof crypto[name] !== "function") continue;
        const orig = crypto[name];
        crypto[name] = function (...args) {
            if (!active) return orig.apply(this, args);
            const s = process.hrtime.bigint();
            try {
                return orig.apply(this, args);
            } finally {
                const d = process.hrtime.bigint() - s;
                metrics.rustTimeNs += d;
                metrics.callCount++;
                const m = metrics.calls.get(name) || { timeNs: 0n, count: 0 };
                m.timeNs += d;
                m.count++;
                metrics.calls.set(name, m);
            }
        };
    }
};

// runBench hook: reset + arm the counters at the start of a timed trial.
export const onStart = (_label) => {
    metrics = { rustTimeNs: 0n, callCount: 0, calls: new Map() };
    active = true;
};

// runBench hook: disarm + snapshot the trial's FFI totals for this label.
export const onEnd = (label) => {
    active = false;
    const arr = trialsByLabel.get(label) || [];
    arr.push({
        rustMs: Number(metrics.rustTimeNs) / 1e6,
        ffiCalls: metrics.callCount,
        perCall: [...metrics.calls.entries()]
            .sort((a, b) => Number(b[1].timeNs - a[1].timeNs))
            .map(([n, c]) => ({ name: n, ms: Number(c.timeNs) / 1e6, count: c.count })),
    });
    trialsByLabel.set(label, arr);
    console.log(
        `[ffi] ${label}: rust ${(Number(metrics.rustTimeNs) / 1e6).toFixed(2)}ms (${metrics.callCount} calls)`
    );
};

// Augment each bench (from runBench) with its captured FFI summary, computing
// rustShare against the wall mean. `ffi` rides along the JS object into the
// artifact.
export const attachFfi = (benches) => () =>
    benches.map((b) => {
        const trials = trialsByLabel.get(b.name) || [];
        const rust = trials.map((t) => t.rustMs);
        const rustMean = rust.length ? rust.reduce((a, x) => a + x, 0) / rust.length : null;
        const mean = b.stats.meanMs;
        return {
            ...b,
            ffi: {
                rustMeanMs: rustMean,
                rustShare: rustMean != null && mean ? rustMean / mean : null,
                trials,
            },
        };
    });
