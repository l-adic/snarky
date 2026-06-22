// Cross-stack comparison table from N bench artifacts (PS, o1js, …).
//   node tools/bench_table.mjs <a.json> <b.json> [...]
// Per bench label (compile, prove): wall mean ± stddev, reclaim/trial,
// GC pause %, and the napi rustShare where present (PS only). With exactly two
// artifacts it also prints the wall ratio. Cross-stack tables are a reporting
// view only — never the regression gate (that's compare.mjs, same-stack).
import fs from "node:fs";

const arts = process.argv.slice(2).map((f) => {
  const d = JSON.parse(fs.readFileSync(f, "utf8"));
  return { f, d, name: `${d.suite}${d.backend ? "/" + d.backend : ""}` };
});

const mean = (xs) => (xs.length ? xs.reduce((a, b) => a + b, 0) / xs.length : null);
const findBench = (d, label) => d.benches.find((b) => b.name === label);
const reclaimGB = (b) => (b?.gc?.length ? mean(b.gc.map((g) => g.reclaimedGB)) : null);
const pausePct = (b) => (b?.gc?.length ? mean(b.gc.map((g) => g.gcPausePct)) : null);
const fmt = (x, d = 2) => (x == null ? "—" : x.toFixed(d));

const labels = [...new Set(arts.flatMap((a) => a.d.benches.map((b) => b.name)))];

console.log(`# Bench comparison  (node ${arts[0]?.d.node}, profile ${arts[0]?.d.powerProfile})`);
for (const a of arts)
  console.log(`  ${a.name.padEnd(14)} ${a.d.gitSha?.slice(0, 9) ?? "?"}${a.d.gitDirty ? "+dirty" : ""}  ${a.d.o1jsVersion ? "o1js " + a.d.o1jsVersion : ""}  rows=${JSON.stringify(a.d.circuitRows ?? "—")}`);

for (const label of labels) {
  console.log(`\n## ${label}`);
  console.log("| stack | wall mean (s) | stddev (s) | reclaim/trial (GB) | gc pause % | rustShare |");
  console.log("|---|---|---|---|---|---|");
  const rows = arts.map((a) => ({ name: a.name, b: findBench(a.d, label) })).filter((r) => r.b);
  for (const r of rows) {
    const s = r.b.stats;
    console.log(
      `| ${r.name} | ${fmt(s.meanMs / 1000)} | ${fmt(s.stddevMs / 1000)} | ` +
        `${fmt(reclaimGB(r.b), 1)} | ${fmt(pausePct(r.b), 1)} | ${r.b.ffi ? fmt(r.b.ffi.rustShare, 3) : "—"} |`
    );
  }
  if (rows.length === 2) {
    const [a, b] = rows;
    console.log(
      `\n→ **${b.name} / ${a.name} wall ratio: ${(b.b.stats.meanMs / a.b.stats.meanMs).toFixed(2)}×**`
    );
  }
}
