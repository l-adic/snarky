#!/usr/bin/env node
// Aggregate many V8 .cpuprofiles into busy/GC/idle CPU per ROLE (main isolate
// vs worker isolate), so 100+ per-thread dumps collapse to a few numbers.
//
//   node prof/rollup.mjs <label> <file.cpuprofile>...
//
// Role is inferred from the filename thread id (CPU.<date>.<pid>.<thread>.<seq>):
// thread 0 = main isolate (serial JS); thread >0 = worker isolate (parallel
// prover, wasm only — native rust threads are invisible to V8).
//
// "busy" excludes the V8 (idle)/(program)/(root) pseudo-frames; (garbage
// collector) is bucketed separately. Prints a JSON line + a human summary.

import fs from "fs";

const [, , label, ...files] = process.argv;
if (!label || !files.length) {
  console.error("usage: rollup.mjs <label> <file.cpuprofile>...");
  process.exit(2);
}

const IDLE = new Set(["(idle)", "(program)", "(root)"]);
const isGC = (n) => n === "(garbage collector)";
// rayon/crossbeam idle-spin & OS waits masquerade as "running" samples in a V8
// worker cpuprofile — bucket them apart from useful compute so the rollup is honest.
const WAIT_RE = /::sleep::|Sleep|Condvar|condvar|futex|crossbeam_deque|Stealer|::steal|in_worker_cold|::park|Backoff|spin/i;
const isWait = (n) => WAIT_RE.test(n);

const acc = {
  main: { busy: 0, wait: 0, gc: 0, idle: 0, isolates: 0 },
  worker: { busy: 0, wait: 0, gc: 0, idle: 0, isolates: 0 },
};

const threadOf = (path) => {
  const m = path.match(/\.(\d+)\.(\d+)\.(\d+)\.cpuprofile$/);
  return m ? Number(m[2]) : 0; // group 2 = thread id
};

for (const f of files) {
  const prof = JSON.parse(fs.readFileSync(f, "utf8"));
  const byId = new Map(prof.nodes.map((n) => [n.id, n]));
  const role = threadOf(f) === 0 ? "main" : "worker";
  acc[role].isolates++;
  for (let i = 0; i < prof.samples.length; i++) {
    const d = prof.timeDeltas[i] > 0 ? prof.timeDeltas[i] : 0;
    const n = byId.get(prof.samples[i]);
    const fn = n?.callFrame?.functionName ?? "(root)";
    if (isGC(fn)) acc[role].gc += d;
    else if (IDLE.has(fn)) acc[role].idle += d;
    else if (isWait(fn)) acc[role].wait += d;
    else acc[role].busy += d;
  }
}

const ms = (u) => +(u / 1000).toFixed(0);
const roll = (a) => ({ usefulMs: ms(a.busy), waitMs: ms(a.wait), gcMs: ms(a.gc), idleMs: ms(a.idle), isolates: a.isolates });
const out = { label, main: roll(acc.main), worker: roll(acc.worker) };
// "useful" = compute excluding spin/wait/idle. parallelism = useful worker / useful main.
out.parallelUsefulToSerial = out.main.usefulMs ? +(out.worker.usefulMs / out.main.usefulMs).toFixed(2) : null;

console.error(
  `${label.padEnd(16)} serial main: useful ${String(out.main.usefulMs).padStart(6)}ms gc ${String(out.main.gcMs).padStart(5)}ms` +
    `  |  ${String(out.worker.isolates).padStart(2)} workers: useful ${String(out.worker.usefulMs).padStart(7)}ms  wait/spin ${String(out.worker.waitMs).padStart(8)}ms` +
    `  |  useful parallel/serial = ${out.parallelUsefulToSerial ?? "—"}x`
);
console.log(JSON.stringify(out));
