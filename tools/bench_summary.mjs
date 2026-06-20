// Aggregate many bench artifacts — N iterations × {pickles,o1js} × {native,wasm}
// — into one summary markdown (stdout). Groups by suite/backend, aggregates each
// bench label across iterations (mean-of-means + spread), and prints the
// cross-stack ratios per backend.
//
//   node tools/bench_summary.mjs <artifact.json> [more.json ...] > summary.md
//
// A reporting view only; the regression gate is compare.mjs (same-stack).
import fs from "node:fs";

const files = process.argv.slice(2);
if (!files.length) {
  console.error("usage: bench_summary.mjs <artifact.json> [...]");
  process.exit(1);
}
const arts = files
  .map((f) => {
    try {
      return JSON.parse(fs.readFileSync(f, "utf8"));
    } catch {
      console.error(`! skipping unreadable ${f}`);
      return null;
    }
  })
  .filter(Boolean);

// PS native artifacts have no `backend` field → treat as native.
const cfg = (a) => `${a.suite ?? "pickles"}/${a.backend ?? "native"}`;
const mean = (xs) => (xs.length ? xs.reduce((a, b) => a + b, 0) / xs.length : null);
const sd = (xs) => {
  if (xs.length < 2) return null;
  const m = mean(xs);
  return Math.sqrt(xs.reduce((a, x) => a + (x - m) ** 2, 0) / (xs.length - 1));
};
const reclaim = (b) => (b?.gc?.length ? mean(b.gc.map((g) => g.reclaimedGB)) : null);
const f = (x, d = 2) => (x == null ? "—" : x.toFixed(d));

const groups = {};
for (const a of arts) (groups[cfg(a)] ??= []).push(a);
const configs = Object.keys(groups).sort();
const labels = [...new Set(arts.flatMap((a) => a.benches.map((b) => b.name)))];

// One config × one bench label, aggregated across iterations.
function agg(config, label) {
  const means = [];
  const reclaims = [];
  const shares = [];
  for (const a of groups[config] ?? []) {
    const b = a.benches.find((x) => x.name === label);
    if (!b) continue;
    if (b.stats.meanMs != null) means.push(b.stats.meanMs);
    const r = reclaim(b);
    if (r != null) reclaims.push(r);
    if (b.ffi?.rustShare != null) shares.push(b.ffi.rustShare);
  }
  return {
    n: means.length,
    mean: mean(means),
    sd: sd(means),
    min: means.length ? Math.min(...means) : null,
    max: means.length ? Math.max(...means) : null,
    reclaim: mean(reclaims),
    rustShare: mean(shares),
  };
}

const meta = arts[0] ?? {};
const o1 = arts.find((a) => a.suite === "o1js");
const out = [];
out.push("# Bench summary — snarky-PS vs o1js, native vs wasm\n");
out.push(`- node: \`${meta.node}\`  ·  power profile: \`${meta.powerProfile ?? "?"}\``);
out.push(`- iterations: ${Math.max(0, ...configs.map((c) => groups[c].length))} per config  ·  configs: ${configs.join(", ")}`);
out.push(`- git: \`${meta.gitSha?.slice(0, 9) ?? "?"}\`${meta.gitDirty ? " (+dirty)" : ""}`);
if (o1) out.push(`- o1js \`${o1.o1jsVersion}\`  ·  rows ${JSON.stringify(o1.circuitRows)}  ·  PS workload domain 2^16`);
out.push("");

for (const label of labels) {
  out.push(`## ${label}\n`);
  out.push("| config | iters | wall mean (s) | iter stddev (s) | min–max (s) | reclaim/trial (GB)¹ | rustShare |");
  out.push("|---|---|---|---|---|---|---|");
  for (const c of configs) {
    const a = agg(c, label);
    if (!a.n) continue;
    out.push(
      `| ${c} | ${a.n} | ${f(a.mean / 1000)} | ${f(a.sd / 1000)} | ${f(a.min / 1000)}–${f(a.max / 1000)} | ${f(a.reclaim, 1)} | ${f(a.rustShare, 3)} |`
    );
  }
  out.push("");
  for (const backend of ["native", "wasm"]) {
    const ps = agg(`pickles/${backend}`, label);
    const o = agg(`o1js/${backend}`, label);
    if (ps.mean && o.mean)
      out.push(
        `- **${backend}: o1js / PS = ${(o.mean / ps.mean).toFixed(2)}×**  (PS ${(ps.mean / 1000).toFixed(1)}s vs o1js ${(o.mean / 1000).toFixed(1)}s)`
      );
  }
  out.push("");
}

out.push("---");
out.push(
  "¹ **wasm reclaim is a main-isolate lower bound.** Both stacks run the prover on worker threads " +
    "(separate isolates / wasm linear memory), invisible to `--trace-gc` and the GC observer — so it captures " +
    "only main-thread (witness-gen) JS churn, not the prover's memory. Native reclaim is trustworthy; compare " +
    "wasm reclaim only wasm-to-wasm, never wasm-to-native."
);
out.push(
  "\n**Parity:** tree.step domain 2^16 both stacks (row *counts* differ by gate accounting; the FFT domain " +
    "governs the work). Same node, same `bench-harness` runner; PS↔o1js runs spaced ≥60s on the `performance` " +
    "power profile so a pairing isn't a thermal artifact."
);

console.log(out.join("\n"));
