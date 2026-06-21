#!/usr/bin/env node
// Merge N V8 .cpuprofiles into ONE flamegraph SVG by folding stacks.
// Used to collapse a worker pool (19 rayon isolates) into a single
// proportional view of where the parallel prover spends time.
//
//   node prof/flamemerge.mjs <out.svg> "Title" <file.cpuprofile>...
//
// Proportions across the pool are meaningful; absolute ms is wall-presence
// (see rollup.mjs) so the title says "proportional". Sleep/spin frames are
// kept (they ARE where worker wall goes) but are easy to spot and ignore.

import fs from "fs";

const [, , outPath, title, ...files] = process.argv;
if (!outPath || !files.length) {
  console.error('usage: flamemerge.mjs <out.svg> "Title" <file.cpuprofile>...');
  process.exit(2);
}

const MOD_RE = /output(?:-es)?\/([^/]+)\/(index|foreign)\.js/;
const WASM_RE = /([a-z_]+(?:_wasm|_napi)\.wasm)-[0-9a-f]+/;
const labelOf = (cf) => {
  const fn = (cf.functionName || "(anonymous)").replace(/\[[0-9a-f]{8,}\]/g, "").replace(/::h[0-9a-f]+$/, "");
  const url = cf.url || "";
  const m = url.match(MOD_RE);
  if (m) return `${m[2] === "foreign" ? `${m[1]}/foreign` : m[1]} ${fn}`;
  const w = url.match(WASM_RE);
  if (w) return `${w[1]} ${fn}`;
  return fn;
};

// fold: stack-path (array of labels) -> summed self micros, built as a tree
const root = { label: "(all workers)", self: 0, incl: 0, children: new Map() };
const skip = new Set(["(root)", "(program)"]);

for (const f of files) {
  const prof = JSON.parse(fs.readFileSync(f, "utf8"));
  const byId = new Map(prof.nodes.map((n) => [n.id, n]));
  // parent map
  const parent = new Map();
  for (const n of prof.nodes) for (const c of n.children || []) parent.set(c, n.id);
  // self time per node
  const self = new Map();
  for (let i = 0; i < prof.samples.length; i++) {
    const d = prof.timeDeltas[i] > 0 ? prof.timeDeltas[i] : 0;
    self.set(prof.samples[i], (self.get(prof.samples[i]) || 0) + d);
  }
  // for each node with self time, walk to root, build label path, add to tree
  for (const [id, t] of self) {
    if (!t) continue;
    const path = [];
    let cur = id;
    while (cur != null) {
      const n = byId.get(cur);
      const lbl = labelOf(n.callFrame);
      if (!skip.has(n.callFrame.functionName)) path.push(lbl);
      cur = parent.get(cur);
    }
    path.reverse();
    let node = root;
    root.incl += t;
    for (const lbl of path) {
      let ch = node.children.get(lbl);
      if (!ch) { ch = { label: lbl, self: 0, incl: 0, children: new Map() }; node.children.set(lbl, ch); }
      ch.incl += t;
      node = ch;
    }
    node.self += t;
  }
}

// layout
const W = 1800, ROW = 16, MINPX = Number(process.env.FLAME_MINPX || 0.3);
const frames = [];
let maxDepth = 0;
const place = (node, x0, depth) => {
  const w = (node.incl / root.incl) * W;
  if (w < MINPX) return;
  frames.push({ x: x0, w, depth, label: node.label, micros: node.incl, self: node.self });
  if (depth > maxDepth) maxDepth = depth;
  const kids = [...node.children.values()].sort((a, b) => b.incl - a.incl);
  let cx = x0;
  for (const c of kids) { place(c, cx, depth + 1); cx += (c.incl / root.incl) * W; }
};
place(root, 0, 0);

const color = (s) => { let h = 0; for (let i = 0; i < s.length; i++) h = (h * 31 + s.charCodeAt(i)) & 0xffff;
  return `rgb(${205 + (h % 50)},${50 + ((h >> 4) % 160)},${30 + ((h >> 8) % 55)})`; };
const esc = (s) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
const pct = (u) => ((u / root.incl) * 100).toFixed(1);
const H = (maxDepth + 1) * ROW + 40;

let rects = "";
for (const f of frames) {
  const y = H - 24 - (f.depth + 1) * ROW;
  const txt = f.w > 28 ? `<text x="${(f.x + 3).toFixed(1)}" y="${(y + ROW - 4).toFixed(0)}" font-size="10" font-family="monospace">${esc(f.label.length > Math.floor(f.w / 6) ? f.label.slice(0, Math.floor(f.w / 6)) + "…" : f.label)}</text>` : "";
  rects += `<g><rect x="${f.x.toFixed(2)}" y="${y}" width="${Math.max(f.w - 0.5, 0.5).toFixed(2)}" height="${ROW - 1}" fill="${color(f.label)}" stroke="#fff" stroke-width="0.3"><title>${esc(f.label)}\n${pct(f.micros)}% of pool wall-presence</title></rect>${txt}</g>\n`;
}
const svg = `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}" viewBox="0 0 ${W} ${H}" font-family="monospace">
<rect width="100%" height="100%" fill="#fafafa"/>
<text x="8" y="18" font-size="14" font-weight="bold">${esc(title)}</text>
<text x="8" y="32" font-size="10" fill="#555">${files.length} worker isolates folded · width = proportion of pool wall-presence (NOT CPU — see rollup) · sleep/spin frames included</text>
<g>${rects}</g></svg>
`;
fs.writeFileSync(outPath, svg);
console.log(`wrote ${outPath} (${frames.length} frames, depth ${maxDepth})`);
