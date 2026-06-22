#!/usr/bin/env node
// Full bench matrix: snarky-PS vs o1js × native vs wasm.
//
//   tools/bench_matrix.sh [--iters N] [--gap S] [--timeout S]
//
// Per iteration the four configs run in order (ps-native, o1js-native,
// ps-wasm, o1js-wasm), each >= GAP seconds apart so a PS<->o1js pairing
// is never a thermal artifact. Outputs one JSON artifact per iteration
// plus a combined summary.md, all under bench-results/<runid>-...
//
// Replaces the former bash orchestrator — all orchestration logic is here;
// the bash wrapper just sets up the node PATH and execs this.

import { execFileSync } from "node:child_process";
import { parseArgs } from "node:util";
import fs from "node:fs";
import path from "node:path";

const { values: flags, positionals } = parseArgs({
  options: {
    iters:   { type: "string", default: "3" },
    gap:     { type: "string", default: "60" },
    timeout: { type: "string", default: "2400" },
    help:    { type: "boolean", short: "h", default: false },
  },
  allowPositionals: true,
  strict: true,
});

if (flags.help) {
  console.log(`\
bench_matrix — run the full PS-vs-o1js bench matrix.

Usage: tools/bench_matrix.sh [--iters N] [--gap S] [--timeout S]
       tools/bench_matrix.sh [N]          (positional iters, backwards-compat)

Options:
  --iters N    Iterations per config (default 3)
  --gap S      Seconds between configs within an iteration (default 60)
  --timeout S  Per-config timeout in seconds (default 2400)
  -h, --help   Show this help

Configs (run each iteration in this order):
  ps-native, o1js-native, ps-wasm, o1js-wasm

Outputs (bench-results/<runid>-...):
  ...-{ps,o1js}-{native,wasm}-i<N>.json   one per iteration
  ...-...-i<N>.log                         raw run log (triage)
  ...-summary.md                           combined summary
`);
  process.exit(0);
}

const ITERS = parseInt(positionals[0] ?? flags.iters, 10);
const GAP = parseInt(flags.gap, 10);
const TIMEOUT = parseInt(flags.timeout, 10);
const RUNID = new Date().toISOString().replace(/T/, "-").replace(/[:.]/g, "").slice(0, 15);
const PREFIX = `bench-results/${RUNID}`;

fs.mkdirSync("bench-results", { recursive: true });

// ---- single-tenant lock: concurrent benches invalidate numbers -----------
const LOCK = "bench-results/.matrix.lock";
try {
  fs.mkdirSync(LOCK);
} catch (e) {
  if (e.code === "EEXIST") {
    const info = (() => { try { return fs.readFileSync(path.join(LOCK, "info"), "utf8"); } catch { return "unknown"; } })();
    console.error(`FATAL: another bench holds ${LOCK} (${info.trim()}). Refusing to start.`);
    console.error(`       Concurrent benches invalidate numbers and can deadlock. If stale: rm -rf '${LOCK}'.`);
    process.exit(1);
  }
  throw e;
}
fs.writeFileSync(path.join(LOCK, "info"), `pid ${process.pid} started ${new Date().toISOString()}\n`);
const unlock = () => { try { fs.rmSync(LOCK, { recursive: true, force: true }); } catch {} };
process.on("exit", unlock);
process.on("SIGINT", () => { unlock(); process.exit(130); });
process.on("SIGTERM", () => { unlock(); process.exit(143); });

// ---- system checks -------------------------------------------------------
const sh = (cmd) => { try { return execFileSync("sh", ["-c", cmd], { encoding: "utf8" }).trim(); } catch { return null; } };
const prof = sh("powerprofilesctl get 2>/dev/null") ?? "unknown";
const load1 = sh("awk '{print $1}' /proc/loadavg") ?? "?";
const busy = sh("pgrep -fc 'run\\.mjs|dist/bench\\.js'") ?? "0";

console.log(`==> matrix run ${RUNID}: ${ITERS} iters x 4 configs, gap ${GAP}s, timeout ${TIMEOUT}s/config`);
console.log(`    power=${prof}  load1=${load1}  competing-bench-procs=${busy}`);
if (prof !== "performance") console.log(`    WARNING: power profile '${prof}' != performance (see README for the sysfs fallback).`);
if (parseFloat(load1) > 2) console.log(`    WARNING: load average ${load1} is high — the box may not be idle.`);
if (parseInt(busy, 10) > 0) console.log(`    WARNING: ${busy} competing run.mjs/bench.js process(es) — STOP them.`);

// ---- configs --------------------------------------------------------------
const CONFIGS = [
  { tag: "ps-native",   cmd: ["tools/bench.sh"] },
  { tag: "o1js-native", cmd: ["tools/bench_o1js.sh", "--native"] },
  { tag: "ps-wasm",     cmd: ["tools/bench.sh", "--wasm"] },
  { tag: "o1js-wasm",   cmd: ["tools/bench_o1js.sh"] },
];

function runConfig(tag, cmd, iter) {
  const out = `${PREFIX}-${tag}-i${iter}.json`;
  const log = `${PREFIX}-${tag}-i${iter}.log`;
  const ts = new Date().toTimeString().slice(0, 8);
  console.log(`[${ts}] iter ${iter}  ${tag}  (timeout ${TIMEOUT}s)`);
  try {
    const logFd = fs.openSync(log, "w");
    execFileSync(cmd[0], cmd.slice(1), {
      env: { ...process.env, BENCH_RESULTS_FILE: out },
      stdio: ["ignore", logFd, logFd],
      timeout: TIMEOUT * 1000,
    });
    fs.closeSync(logFd);
  } catch (e) {
    if (e.killed || e.signal === "SIGTERM") {
      console.log(`          !! TIMEOUT after ${TIMEOUT}s — killing stragglers`);
      sh("pkill -9 -f 'run\\.mjs' 2>/dev/null");
      sh("pkill -9 -f 'dist/bench\\.js' 2>/dev/null");
    }
  }
  if (fs.existsSync(out)) {
    console.log(`          -> ${out}`);
  } else {
    console.log(`          !! MISSING ${out} (see ${log})`);
  }
}

function sleep(seconds) {
  // Synchronous sleep — fine for a sequential bench driver.
  execFileSync("sleep", [String(seconds)], { stdio: "ignore" });
}

// ---- main loop ------------------------------------------------------------
for (let i = 1; i <= ITERS; i++) {
  for (const { tag, cmd } of CONFIGS) {
    runConfig(tag, cmd, i);
    sleep(GAP);
  }
}

// ---- summary --------------------------------------------------------------
const artifacts = [];
for (let i = 1; i <= ITERS; i++) {
  for (const { tag } of CONFIGS) {
    const f = `${PREFIX}-${tag}-i${i}.json`;
    if (fs.existsSync(f)) artifacts.push(f);
  }
}
const summaryFile = `${PREFIX}-summary.md`;
console.log(`==> aggregating -> ${summaryFile}`);
try {
  const summary = execFileSync("node", ["tools/bench_summary.mjs", ...artifacts], { encoding: "utf8" });
  fs.writeFileSync(summaryFile, summary);
  console.log(`==> DONE`);
  console.log(`    summary:    ${summaryFile}`);
  console.log(`    artifacts:  ${PREFIX}-*-i*.json`);
  console.log(summary);
} catch (e) {
  console.error("summary generation failed:", e.message);
}
