#!/usr/bin/env node
// Compare two bench-results JSON artifacts (written by the bench's
// jsonReporter, optionally enriched by parse_gclog.mjs) and flag
// regressions.
//
// Usage:
//   node compare.mjs <baseline.json> <candidate.json>
//
// Per bench: wall mean ± stddev, delta; rust-FFI share delta; GC reclaim
// delta (when present). A wall-time delta is FLAGGED when it exceeds
// max(5%, 2σ of the combined spread) — exits 1 if anything is flagged,
// so the script is CI-able.

import fs from "fs";

const [, , basePath, candPath] = process.argv;
if (!basePath || !candPath) {
  console.error("usage: compare.mjs <baseline.json> <candidate.json>");
  process.exit(2);
}

const load = (p) => JSON.parse(fs.readFileSync(p, "utf8"));
const base = load(basePath);
const cand = load(candPath);

const fmtS = (ms) => (ms / 1000).toFixed(2) + "s";
const fmtPct = (x) => (x >= 0 ? "+" : "") + (100 * x).toFixed(1) + "%";

console.log(`baseline:  ${base.gitSha?.slice(0, 9)}${base.gitDirty ? "+dirty" : ""}  (${base.date})`);
console.log(`candidate: ${cand.gitSha?.slice(0, 9)}${cand.gitDirty ? "+dirty" : ""}  (${cand.date})`);
if (base.node !== cand.node)
  console.log(`⚠ node version mismatch: ${base.node} vs ${cand.node} — timings not comparable`);
if (base.powerProfile !== cand.powerProfile)
  console.log(`⚠ power profile mismatch: ${base.powerProfile ?? "unknown"} vs ${cand.powerProfile ?? "unknown"} — timings not comparable`);
console.log("");

let flagged = false;

for (const cb of cand.benches) {
  const bb = base.benches.find((b) => b.name === cb.name);
  if (!bb) {
    console.log(`~ ${cb.name}: not in baseline (new bench)`);
    continue;
  }
  const bm = bb.stats.meanMs;
  const cm = cb.stats.meanMs;
  const delta = (cm - bm) / bm;
  // Threshold: relative 5%, or 2σ of the combined per-trial spread —
  // whichever is larger (so noisy benches don't false-positive).
  const sigma = Math.max(bb.stats.stddevMs ?? 0, cb.stats.stddevMs ?? 0);
  const threshold = Math.max(0.05, (2 * sigma) / bm);
  const flag = Math.abs(delta) > threshold;
  if (flag && delta > 0) flagged = true;

  const mark = !flag ? "  " : delta > 0 ? "✗ " : "✓ ";
  console.log(`${mark}${cb.name}`);
  console.log(
    `    wall:  ${fmtS(bm)} -> ${fmtS(cm)}  (${fmtPct(delta)}${flag ? `, exceeds ${fmtPct(threshold)} threshold` : ""})`
  );

  if (bb.ffi?.rustShare != null && cb.ffi?.rustShare != null) {
    console.log(
      `    rust-ffi share: ${(100 * bb.ffi.rustShare).toFixed(1)}% -> ${(100 * cb.ffi.rustShare).toFixed(1)}%` +
        `  (js-side: ${fmtS(bm - bb.ffi.rustMeanMs)} -> ${fmtS(cm - cb.ffi.rustMeanMs)})`
    );
  }

  const gcGB = (b) =>
    b.gc?.length ? b.gc.reduce((a, g) => a + g.reclaimedGB, 0) / b.gc.length : null;
  const bg = gcGB(bb);
  const cg = gcGB(cb);
  if (bg != null && cg != null) {
    console.log(`    gc reclaim/trial: ${bg.toFixed(1)}GB -> ${cg.toFixed(1)}GB  (${fmtPct((cg - bg) / bg)})`);
  }
}

console.log("");
console.log(flagged ? "REGRESSION flagged." : "no regressions flagged.");
process.exit(flagged ? 1 : 0);
