// o1js bench entry — the mirror of `Bench.Pickles.Main`. Selects the backend,
// builds the two groups, and drives them through the SHARED `bench-harness`
// `runBench` (the exact runner the PS suite uses), then writes the same-schema
// artifact. No hooks: o1js has no napi boundary to time (its kimchi is WASM in
// the JS heap), so the timed region is purely `work()` — identical to the PS
// side's timed region.
//
// WASM caveat → per-trial subprocesses: o1js does not release its prover-key
// wasm memory between compiles (no GC finalizer, unlike our kimchi-napi), so a
// single process accumulates ~1 GB/compile and wedges at the wasm32 4 GB
// ceiling. Under `--wasm` we therefore run EACH timed trial in a fresh child
// process (`--child`): memory is capped at one trial's worth and the OS reclaims
// it on exit. The untimed `prepare` in each child warms the JIT so the timed op
// isn't cold; the children emit the same `[bench-window]` markers, so the
// launcher's parse_gclog attaches GC per trial exactly as for the single-process
// (native) path. Native runs single-process — no ceiling, no need.
//
// Run via tools/bench_o1js.sh. O1JS_BACKEND=native|wasm selects the backend.
import { spawn } from "node:child_process";
import { readFileSync } from "node:fs";
import { runBench, stats, writeArtifact, type Bench } from "bench-harness";
import { setBackend } from "o1js";

const BACKEND = (process.env.O1JS_BACKEND ?? "wasm") as "wasm" | "native";
// Backend selection MUST precede any ZkProgram construction, so the target (and
// the programs it imports) is loaded dynamically AFTER this.
if (BACKEND === "native") setBackend("native");

const argv = process.argv.slice(2);
const childGroup = argv.includes("--child") ? argv[argv.indexOf("--child") + 1] : undefined;

const { buildGroups, analyzeRows } = await import("./target.js");

// --- child mode: run ONE timed trial of one group in this fresh process -------
// (one fresh wasm arena → bounded memory). Prints the wall ms for the parent.
if (childGroup) {
  const g = buildGroups().find((x) => x.label.toLowerCase().includes(childGroup));
  if (!g) throw new Error(`--child: no group matching '${childGroup}'`);
  const benches = await runBench([{ ...g, trials: 1 }]);
  const s = benches[0].samples[0];
  console.log(`[child-ms] ${s.ms}`);
  console.log(`[child-cpu] ${s.cpuMs ?? 0}`);
  process.exit(0);
}

console.log(`[backend] ${BACKEND}`);

function o1jsVersion(): string {
  const pkg = new URL(import.meta.resolve("o1js")).pathname.replace(/dist\/.*/, "package.json");
  return JSON.parse(readFileSync(pkg, "utf8")).version;
}

// Spawn a fresh process running ONE timed trial of `key` ("compile"|"prove");
// resolve its wall ms. The child's stdout (markers, --trace-gc, the ms line) is
// forwarded so parse_gclog sees the same stream as a single-process run.
function childTrial(key: string): Promise<{ ms: number; cpuMs: number }> {
  const self = new URL(import.meta.url).pathname;
  return new Promise((resolve, reject) => {
    const child = spawn(
      process.execPath,
      ["--trace-gc", "--expose-gc", self, "--child", key],
      { env: process.env, stdio: ["ignore", "pipe", "inherit"] }
    );
    let out = "";
    child.stdout.on("data", (d) => {
      out += d;
      process.stdout.write(d);
    });
    child.on("exit", (code) => {
      const m = out.match(/\[child-ms\] ([\d.]+)/);
      const c = out.match(/\[child-cpu\] ([\d.]+)/);
      if (code === 0 && m) resolve({ ms: Number(m[1]), cpuMs: c ? Number(c[1]) : 0 });
      else reject(new Error(`child trial '${key}' failed (exit ${code})`));
    });
  });
}

async function main() {
  const circuitRows = await analyzeRows();
  console.log("[rows]", JSON.stringify(circuitRows));

  let benches: Bench[];
  if (BACKEND === "wasm") {
    benches = [];
    for (const g of buildGroups()) {
      const key = g.label.toLowerCase().includes("compile") ? "compile" : "prove";
      const samples = [];
      for (let t = 0; t < g.trials; t++) {
        console.log(`[wasm per-trial] ${key} ${t + 1}/${g.trials} (fresh process)`);
        const r = await childTrial(key);
        samples.push({ iterations: 1, ms: r.ms, cpuMs: r.cpuMs });
      }
      benches.push({ name: g.label, samples, stats: stats(samples) });
    }
  } else {
    benches = await runBench(buildGroups());
  }

  writeArtifact({
    suite: "o1js",
    backend: BACKEND,
    o1jsVersion: o1jsVersion(),
    circuitRows,
    benches,
  });
}

main().then(
  () => process.exit(0),
  (e) => {
    console.error(e);
    process.exit(1);
  }
);
