// o1js bench entry — the mirror of `Bench.Pickles.Main`. Selects the backend,
// builds the two groups, and drives them through the SHARED `bench-harness`
// `runBench` (the exact runner the PS suite uses), then writes the same-schema
// artifact. No hooks: o1js has no napi boundary to time (its kimchi is WASM in
// the JS heap), so the timed region is purely `work()` — identical to the PS
// side's timed region.
//
// Run via `node --trace-gc dist/bench.js` (so parse_gclog.mjs can attach
// reclaim/trial). O1JS_BACKEND=native|wasm selects the kimchi backend.
import { readFileSync } from "node:fs";
import { runBench, writeArtifact } from "bench-harness";
import { setBackend } from "o1js";

const BACKEND = (process.env.O1JS_BACKEND ?? "wasm") as "wasm" | "native";
// Backend selection MUST precede any ZkProgram construction, so the target (and
// the programs it imports) is loaded dynamically AFTER this.
if (BACKEND === "native") setBackend("native");
console.log(`[backend] ${BACKEND}`);

const { buildGroups, analyzeRows } = await import("./target.js");

function o1jsVersion(): string {
  const pkg = new URL(import.meta.resolve("o1js")).pathname.replace(/dist\/.*/, "package.json");
  return JSON.parse(readFileSync(pkg, "utf8")).version;
}

async function main() {
  const circuitRows = await analyzeRows();
  console.log("[rows]", JSON.stringify(circuitRows));

  const benches = await runBench(buildGroups()); // no hooks
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
