#!/usr/bin/env node
// Window a `--trace-gc` log by the bench's `[bench-window] start/end <ms>
// <label>` markers and summarize GC per timed trial: scavenge/major counts,
// reclaimed MB (Σ before−after over scavenges — the authoritative allocation
// churn; the inspector's counter is known-broken here), total GC pause ms,
// and pause % of the window wall.
//
// The markers share `--trace-gc`'s stream AND timestamp base (ms since
// process start), so attribution is exact even though the log interleaves.
//
// Usage:
//   node parse_gclog.mjs <run.log> [results.json]
//
// With a results.json (written by the bench's jsonReporter), each bench
// entry gains a `gc` field (one entry per trial, in window order) and the
// file is rewritten in place. Without it, prints a table.

import fs from "fs";

const [, , logPath, resultsPath] = process.argv;
if (!logPath) {
  console.error("usage: parse_gclog.mjs <run.log with --trace-gc> [results.json]");
  process.exit(2);
}

const lines = fs.readFileSync(logPath, "utf8").split("\n");

// e.g. `[31058:0x...]    65049 ms: Scavenge 1090.7 (1130.4) -> 1075.0 (1131.7) MB, 1.41 / 0.00 ms  (...)`
//      `[31058:0x...]    70123 ms: Mark-Compact 1234.5 (1300.0) -> 900.1 (1250.0) MB, ...`
const gcRe =
  /^\[\d+(?::0x[0-9a-f]+)?\]\s+([\d.]+) ms: ([A-Za-z][A-Za-z -]*?) (?:\(reduce memory\) )?([\d.]+) \(([\d.]+)\) -> ([\d.]+) \(([\d.]+)\) MB/;
const pauseRe = /, ([\d.]+) \/ [\d.]+ ms/;
const markerRe = /^\[bench-window\] (start|end) (\d+) ?(.*)$/;

const windows = [];
let open = null;
const events = [];

for (const line of lines) {
  const m = line.match(markerRe);
  if (m) {
    const [, which, msStr, label] = m;
    const t = Number(msStr);
    if (which === "start") {
      open = { label: label.trim(), start: t, end: null };
    } else if (open && open.label === label.trim()) {
      open.end = t;
      windows.push(open);
      open = null;
    }
    continue;
  }
  const g = line.match(gcRe);
  if (g) {
    const [, t, kind, before, , after] = g;
    const p = line.match(pauseRe);
    events.push({
      t: Number(t),
      kind: kind.trim(),
      reclaimedMB: Number(before) - Number(after),
      pauseMs: p ? Number(p[1]) : 0,
    });
  }
}

const isScavenge = (k) => /Scavenge|Minor/.test(k);

// NOTE on reading these: `reclaimedGB` (allocation churn) is NOT the cost
// driver — scavenge pause cost tracks SURVIVORS, not reclaimed volume
// (measured 2026-06-11: the transformer stack reclaims MORE GB than the
// Run stack at half the GC pause, because its garbage dies young). Watch
// `avgScavengeMs` (survivor copying per scavenge) and `majorGCs`/
// `majorPauseMs` (promotion pressure) when comparing stacks.
const summarize = (w) => {
  const evs = events.filter((e) => e.t >= w.start && e.t <= w.end);
  const scav = evs.filter((e) => isScavenge(e.kind));
  const major = evs.filter((e) => !isScavenge(e.kind));
  const wallMs = w.end - w.start;
  const pauseMs = evs.reduce((a, e) => a + e.pauseMs, 0);
  const scavPauseMs = scav.reduce((a, e) => a + e.pauseMs, 0);
  const majorPauseMs = major.reduce((a, e) => a + e.pauseMs, 0);
  return {
    label: w.label,
    wallMs,
    scavenges: scav.length,
    majorGCs: major.length,
    reclaimedGB:
      evs.reduce((a, e) => a + Math.max(0, e.reclaimedMB), 0) / 1024,
    gcPauseMs: pauseMs,
    gcPausePct: wallMs > 0 ? (100 * pauseMs) / wallMs : 0,
    avgScavengeMs: scav.length ? scavPauseMs / scav.length : 0,
    majorPauseMs,
  };
};

const summaries = windows.map(summarize);

if (summaries.length === 0) {
  console.error(
    "no [bench-window] markers found — was the bench run with --trace-gc and the current BenchUtils?"
  );
  process.exit(1);
}

if (resultsPath) {
  const results = JSON.parse(fs.readFileSync(resultsPath, "utf8"));
  for (const bench of results.benches) {
    bench.gc = summaries
      .filter((s) => s.label === bench.name)
      .map(({ label, ...rest }) => rest);
  }
  fs.writeFileSync(resultsPath, JSON.stringify(results, null, 2));
  console.log(`[parse_gclog] attached GC stats for ${summaries.length} window(s) -> ${resultsPath}`);
} else {
  for (const s of summaries) {
    console.log(
      `${s.label}: wall=${(s.wallMs / 1000).toFixed(1)}s  reclaimed=${s.reclaimedGB.toFixed(1)}GB  ` +
        `scavenges=${s.scavenges} (avg ${s.avgScavengeMs.toFixed(2)}ms)  major=${s.majorGCs} (${s.majorPauseMs.toFixed(0)}ms)  ` +
        `gcPause=${s.gcPauseMs.toFixed(0)}ms (${s.gcPausePct.toFixed(1)}%)`
    );
  }
}
