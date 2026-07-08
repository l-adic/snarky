#!/usr/bin/env node
// Sample the CPU concurrency (cores in use) of a command's whole process tree
// over time — from /proc on linux, from `ps` on macOS — works for native AND
// wasm (sees Rust/rayon threads and per-trial child processes, which V8
// cpuprofiles cannot account for).
//
//   node tools/profile/cpu_timeline.mjs <out.json> <label> -- <cmd> [args...]
//
// Every INTERVAL ms it sums utime+stime across the root pid and all descendants
// and records instantaneous cores = Δticks / CLK_TCK / Δwall. It also tees the
// child's stdout and captures `[bench-window] start|end <uptimeMs> <label>`
// markers (single-process runs) so phases can be shaded downstream.
//
// Output JSON: { label, intervalMs, clkTck, samples:[{t,cores}], markers:[...] }

import fs from "fs";
import { spawn, execSync } from "node:child_process";

const IS_DARWIN = process.platform === "darwin";

const args = process.argv.slice(2);
const dashdash = args.indexOf("--");
if (dashdash < 0 || dashdash < 2) {
  console.error("usage: cpu_timeline.mjs <out.json> <label> -- <cmd> [args...]");
  process.exit(2);
}
const [outPath, label] = args.slice(0, dashdash);
const [cmd, ...cmdArgs] = args.slice(dashdash + 1);

const INTERVAL = Number(process.env.SAMPLE_MS || 50);
const CLK_TCK = 100; // getconf CLK_TCK on linux

const PAGE = 4096; // resident pages -> bytes (statm field 2)
// read /proc/<pid>/stat -> {ppid, ticks}. comm (field 2) may contain spaces and
// parens, so split on the LAST ')'.
function readStat(pid) {
  try {
    const s = fs.readFileSync(`/proc/${pid}/stat`, "utf8");
    const rparen = s.lastIndexOf(")");
    const rest = s.slice(rparen + 2).split(" "); // fields from #3 (state) onward
    const ppid = Number(rest[1]); // field 4
    const utime = Number(rest[11]); // field 14
    const stime = Number(rest[12]); // field 15
    let rss = 0;
    try { rss = Number(fs.readFileSync(`/proc/${pid}/statm`, "utf8").split(" ")[1]) * PAGE; } catch {}
    return { ppid, ticks: utime + stime, rss };
  } catch {
    return null;
  }
}

// macOS has no /proc: one `ps` snapshot gives every process's cumulative CPU
// time (already summed over its threads — so a multithreaded napi/rayon process
// reports all its cores here) + ppid + RSS. Parse to the SAME shape as the linux
// path: ticks in CLK_TCK units, rss in bytes. cputime is `[[DD-]HH:]MM:SS.ss`.
function parseCpuSeconds(s) {
  let days = 0;
  if (s.includes("-")) { const [d, rest] = s.split("-"); days = Number(d); s = rest; }
  const p = s.split(":").map(Number);
  let sec = p.at(-1) + (p.length >= 2 ? p.at(-2) * 60 : 0) + (p.length >= 3 ? p.at(-3) * 3600 : 0);
  return days * 86400 + sec;
}
function treeStatsDarwin(root) {
  let out;
  try { out = execSync("ps -Ao pid=,ppid=,cputime=,rss=", { encoding: "utf8", maxBuffer: 1 << 26 }); }
  catch { return { ticks: 0, rss: 0 }; }
  const stat = new Map(), kids = new Map();
  for (const line of out.split("\n")) {
    const m = line.trim().match(/^(\d+)\s+(\d+)\s+(\S+)\s+(\d+)$/);
    if (!m) continue;
    const pid = +m[1], ppid = +m[2];
    stat.set(pid, { ppid, ticks: parseCpuSeconds(m[3]) * CLK_TCK, rss: +m[4] * 1024 });
    if (!kids.has(ppid)) kids.set(ppid, []);
    kids.get(ppid).push(pid);
  }
  const want = new Set([root]), stack = [root];
  while (stack.length) { const p = stack.pop(); for (const c of kids.get(p) || []) if (!want.has(c)) { want.add(c); stack.push(c); } }
  let ticks = 0, rss = 0;
  for (const p of want) { const s = stat.get(p); if (s) { ticks += s.ticks; rss += s.rss; } }
  return { ticks, rss };
}

// sum ticks + RSS over root pid + all descendants
function treeStatsLinux(root) {
  let pids;
  try { pids = fs.readdirSync("/proc").filter((d) => /^\d+$/.test(d)).map(Number); }
  catch { return { ticks: 0, rss: 0 }; }
  const stat = new Map();
  for (const p of pids) { const s = readStat(p); if (s) stat.set(p, s); }
  // descendants of root via ppid chain
  const kids = new Map();
  for (const [p, s] of stat) { if (!kids.has(s.ppid)) kids.set(s.ppid, []); kids.get(s.ppid).push(p); }
  const want = new Set([root]);
  const stack = [root];
  while (stack.length) { const p = stack.pop(); for (const c of kids.get(p) || []) if (!want.has(c)) { want.add(c); stack.push(c); } }
  let ticks = 0, rss = 0;
  for (const p of want) { const s = stat.get(p); if (s) { ticks += s.ticks; rss += s.rss; } }
  return { ticks, rss };
}

const treeStats = IS_DARWIN ? treeStatsDarwin : treeStatsLinux;

const samples = []; // {t, cores, rssMB}
const markers = []; // {kind, uptimeMs, label}
const MARK = /^\[bench-window\] (start|end) (\d+) ?(.*)$/;

const child = spawn(cmd, cmdArgs, { stdio: ["inherit", "pipe", "inherit"] });
const t0 = process.hrtime.bigint();
const nowMs = () => Number(process.hrtime.bigint() - t0) / 1e6;

let buf = "";
child.stdout.on("data", (d) => {
  process.stdout.write(d);
  buf += d;
  let nl;
  while ((nl = buf.indexOf("\n")) >= 0) {
    const line = buf.slice(0, nl); buf = buf.slice(nl + 1);
    const m = line.match(MARK);
    if (m) markers.push({ kind: m[1], uptimeMs: Number(m[2]), label: m[3], t: nowMs() });
  }
});

let prevTicks = treeStats(child.pid).ticks;
let prevT = nowMs();
const timer = setInterval(() => {
  const t = nowMs();
  const { ticks, rss } = treeStats(child.pid);
  const dt = (t - prevT) / 1000;
  if (dt > 0) samples.push({
    t: +t.toFixed(0),
    cores: +(((ticks - prevTicks) / CLK_TCK) / dt).toFixed(2),
    rssMB: +(rss / 1048576).toFixed(1),
  });
  prevTicks = ticks; prevT = t;
}, INTERVAL);

child.on("exit", (code) => {
  clearInterval(timer);
  fs.writeFileSync(outPath, JSON.stringify({ label, intervalMs: INTERVAL, clkTck: CLK_TCK, samples, markers }, null, 0));
  console.error(`\n[cpu_timeline] ${label}: ${samples.length} samples over ${(samples.at(-1)?.t / 1000).toFixed(1)}s -> ${outPath}  (child exit ${code})`);
  process.exit(code ?? 0);
});
