#!/usr/bin/env node
// Reusable parallelism bar chart from bench matrix artifacts (NOT cpuprofiles —
// see tools/profile/README.md: cpuprofile time is wall-presence, not CPU).
//
//   node tools/profile/chart.mjs <out.svg> <bench-results/<runid>-*.json>...
//
// Reads the per-config artifacts (…-{ps,o1js}-{native,wasm}-i<N>.json), averages
// cpuMs/ms per bench across all matching files, and plots avg cores (cpu/wall)
// per config for each bench, grouped compile vs prove. Config + backend are
// inferred from the filename, so this works on any matrix run.

import fs from "fs";

const [, , outPath, ...files] = process.argv;
if (!outPath || !files.length) {
  console.error("usage: chart.mjs <out.svg> <artifact.json>...");
  process.exit(2);
}

// stack/backend from filename: ...-{ps|o1js}-{native|wasm}-i<N>.json
const cfgOf = (p) => {
  const m = p.match(/-(ps|o1js)-(native|wasm)-/);
  if (!m) return null;
  return { stack: m[1] === "ps" ? "PS" : "o1js", backend: m[2], key: `${m[1] === "ps" ? "PS" : "o1js"}/${m[2]}` };
};
// group bench name into compile vs prove
const benchGroup = (name) => (/compile/i.test(name) ? "compile" : /prove/i.test(name) ? "prove" : null);

// accumulate sums per (config, group)
const agg = new Map(); // key "config|group" -> {ms, cpuMs, n}
for (const f of files) {
  const cfg = cfgOf(f);
  if (!cfg) continue;
  const d = JSON.parse(fs.readFileSync(f, "utf8"));
  for (const b of d.benches || []) {
    const g = benchGroup(b.name);
    if (!g) continue;
    for (const s of b.samples || []) {
      if (!s.cpuMs) continue; // need cpu time to compute cores
      const k = `${cfg.key}|${g}`;
      const a = agg.get(k) || { ms: 0, cpuMs: 0, n: 0, stack: cfg.stack };
      a.ms += s.ms; a.cpuMs += s.cpuMs; a.n++;
      agg.set(k, a);
    }
  }
}

const ORDER = ["PS/native", "o1js/native", "PS/wasm", "o1js/wasm"];
const groups = ["compile", "prove"];
const rowsFor = (g) =>
  ORDER.map((key) => {
    const a = agg.get(`${key}|${g}`);
    if (!a || !a.n) return null;
    const wall = a.ms / a.n / 1000, cpu = a.cpuMs / a.n / 1000;
    return { c: key, stack: a.stack, wall: +wall.toFixed(2), cores: +(cpu / wall).toFixed(1) };
  }).filter(Boolean);

const data = { compile: rowsFor("compile"), prove: rowsFor("prove") };
const allCores = [...data.compile, ...data.prove].map((r) => r.cores);
const maxC = Math.max(2, Math.ceil(Math.max(...allCores) + 1));

const W = 900, H = 460, padL = 60, padB = 70, padT = 60, gap = 40;
const col = (r) => (r.stack === "PS" ? "#2a7de1" : "#e07b39");
const esc = (s) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;");
function panel(title, rows, x0) {
  const pw = (W - 2 * padL - gap) / 2, ph = H - padT - padB, bw = pw / (rows.length * 1.6);
  let s = `<text x="${x0 + pw / 2}" y="${padT - 18}" text-anchor="middle" font-size="14" font-weight="bold">${title}</text>`;
  for (let i = 0; i <= maxC; i += 2) { const y = padT + ph - (i / maxC) * ph;
    s += `<line x1="${x0}" y1="${y}" x2="${x0 + pw}" y2="${y}" stroke="#ddd"/><text x="${x0 - 6}" y="${y + 3}" text-anchor="end" font-size="9" fill="#888">${i}</text>`; }
  rows.forEach((r, i) => { const bx = x0 + (i + 0.3) * (pw / rows.length); const bh = (r.cores / maxC) * ph; const by = padT + ph - bh;
    s += `<rect x="${bx}" y="${by}" width="${bw}" height="${bh}" fill="${col(r)}"/>`;
    s += `<text x="${bx + bw / 2}" y="${by - 4}" text-anchor="middle" font-size="11" font-weight="bold">${r.cores}</text>`;
    s += `<text x="${bx + bw / 2}" y="${padT + ph + 14}" text-anchor="middle" font-size="9.5">${esc(r.c)}</text>`;
    s += `<text x="${bx + bw / 2}" y="${padT + ph + 27}" text-anchor="middle" font-size="8.5" fill="#666">${r.wall}s wall</text>`; });
  return s;
}
const svg = `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}" font-family="sans-serif">
<rect width="100%" height="100%" fill="#fff"/>
<text x="${W / 2}" y="24" text-anchor="middle" font-size="16" font-weight="bold">Average cores used (cpu/wall) — higher = more parallel</text>
<text x="14" y="${padT + (H - padT - padB) / 2}" transform="rotate(-90 14 ${padT + (H - padT - padB) / 2})" text-anchor="middle" font-size="11" fill="#555">avg cores</text>
${panel("compile", data.compile, padL)}
${panel("recursive prove", data.prove, padL + (W - 2 * padL - gap) / 2 + gap)}
<text x="${W - 12}" y="${H - 8}" text-anchor="end" font-size="9" fill="#999">blue = PureScript · orange = o1js · wall-time labels below bars</text>
</svg>`;
fs.writeFileSync(outPath, svg);
console.log(`wrote ${outPath} (compile: ${data.compile.length} cfgs, prove: ${data.prove.length} cfgs)`);
