#!/usr/bin/env node
// Summarize a V8 .cpuprofile (from `tools/bench.sh --cpu-prof`) for the
// questions this codebase keeps asking:
//
//   * where does JS wall time actually go, per PureScript module?
//   * how much is irreducible bigint field arithmetic vs the dispatch /
//     currying / monad machinery wrapped around it?
//
// Complements `src/resolve_profile.mjs` (per-function ranking with corefn
// resolution) with a category rollup tuned to this repo. Self-time only —
// a frame's own hits, not its callees — so categories are additive.
//
// Usage:
//   node packages/pickles-bench/analyze_cpuprofile.mjs prof/CPU.<...>.cpuprofile
//
// The category regexes match the resolved frame key "<module> <function>".
// Order matters: first match wins.

import fs from "fs";

const path = process.argv[2];
if (!path) {
  console.error("usage: analyze_cpuprofile.mjs <file.cpuprofile>");
  process.exit(2);
}

const profile = JSON.parse(fs.readFileSync(path, "utf8"));
const totalMicros = profile.endTime - profile.startTime;

const MOD_RE = /output(?:-es)?\/([^/]+)\/(index|foreign)\.js/;
const moduleOf = (url) => {
  if (!url) return "<v8>";
  const m = url.match(MOD_RE);
  if (m) return m[2] === "foreign" ? `${m[1]}/foreign` : m[1];
  const parts = url.split("/");
  return parts.slice(-2).join("/");
};

// First match wins.
const CATEGORIES = [
  ["GC / engine", /^<v8> \((garbage collector|program|idle)\)/],
  ["Rust FFI (kimchi-napi, via timing wrappers)", /kimchi-napi|\.node\b|BenchUtils\/foreign crypto\./],
  ["bigint field/curve core (pasta-runtime)", /pasta-runtime\//],
  ["field FFI wrappers + dictionaries", /^Snarky\.Curves\.Pasta(\/foreign)? /],
  ["Run/Free machinery", /^(Data\.CatList|Data\.CatQueue|Control\.Monad\.Free|Run|Run\.[A-Za-z.]+) /],
  ["CVar eval/normalize", /^Snarky\.Circuit\.CVar /],
  ["Kimchi constraint reduction", /^Snarky\.Constraint\.Kimchi/],
  ["prover/builder interpreters", /^Snarky\.Backend\./],
  ["other PureScript", /^[A-Z][A-Za-z0-9.]* /],
];

const byFrame = new Map();
let totalHits = 0;
for (const node of profile.nodes) {
  const hits = node.hitCount || 0;
  if (!hits) continue;
  totalHits += hits;
  const cf = node.callFrame;
  const fn = cf.functionName || "(anonymous)";
  const key = `${moduleOf(cf.url)} ${fn}`;
  byFrame.set(key, (byFrame.get(key) || 0) + hits);
}

const msOf = (hits) => (hits / totalHits) * (totalMicros / 1000);

const catTotals = new Map(CATEGORIES.map(([n]) => [n, 0]));
catTotals.set("uncategorized", 0);
const byModule = new Map();
for (const [key, hits] of byFrame) {
  const cat = CATEGORIES.find(([, re]) => re.test(key));
  catTotals.set(cat ? cat[0] : "uncategorized", (catTotals.get(cat ? cat[0] : "uncategorized") || 0) + hits);
  const mod = key.split(" ")[0];
  byModule.set(mod, (byModule.get(mod) || 0) + hits);
}

console.log(`\n=== CPU profile: ${path}`);
console.log(`total sampled: ${(totalMicros / 1e6).toFixed(1)}s wall, ${totalHits} samples\n`);

console.log("--- self-time by category ---");
for (const [name, hits] of [...catTotals.entries()].sort((a, b) => b[1] - a[1])) {
  if (!hits) continue;
  console.log(`${msOf(hits).toFixed(0).padStart(8)}ms  ${((100 * hits) / totalHits).toFixed(1).padStart(5)}%  ${name}`);
}

console.log("\n--- top 20 modules by self-time ---");
for (const [mod, hits] of [...byModule.entries()].sort((a, b) => b[1] - a[1]).slice(0, 20)) {
  console.log(`${msOf(hits).toFixed(0).padStart(8)}ms  ${((100 * hits) / totalHits).toFixed(1).padStart(5)}%  ${mod}`);
}

console.log("\n--- top 25 frames by self-time ---");
for (const [key, hits] of [...byFrame.entries()].sort((a, b) => b[1] - a[1]).slice(0, 25)) {
  console.log(`${msOf(hits).toFixed(0).padStart(8)}ms  ${((100 * hits) / totalHits).toFixed(1).padStart(5)}%  ${key}`);
}
