#!/usr/bin/env node
// Self-contained V8 .cpuprofile -> flamegraph SVG (zero deps).
//
//   node prof/flamegraph.mjs <in.cpuprofile> <out.svg> ["Title"]
//
// Renders the cpuprofile call tree as a classic flamegraph: root at the
// bottom, callees stacked above, frame width proportional to inclusive
// (self+descendants) time. Hover shows full frame + ms + %. Click a frame
// to zoom; click the root strip to reset.

import fs from "fs";

const [, , inPath, outPath, titleArg] = process.argv;
if (!inPath || !outPath) {
  console.error("usage: flamegraph.mjs <in.cpuprofile> <out.svg> [title]");
  process.exit(2);
}

const prof = JSON.parse(fs.readFileSync(inPath, "utf8"));

// ---- frame labels (mirror analyze_cpuprofile.mjs's module heuristic) -------
const MOD_RE = /output(?:-es)?\/([^/]+)\/(index|foreign)\.js/;
const moduleOf = (url) => {
  if (!url) return "";
  const m = url.match(MOD_RE);
  if (m) return m[2] === "foreign" ? `${m[1]}/foreign` : m[1];
  const parts = url.split("/");
  return parts.slice(-2).join("/");
};
const labelOf = (cf) => {
  const fn = cf.functionName || "(anonymous)";
  const mod = moduleOf(cf.url);
  return mod ? `${mod} ${fn}` : fn;
};

// ---- per-node self time from samples/timeDeltas -----------------------------
const byId = new Map();
for (const n of prof.nodes) byId.set(n.id, n);
const self = new Map();
for (const n of prof.nodes) self.set(n.id, 0);
const samples = prof.samples;
const deltas = prof.timeDeltas; // microseconds, deltas[i] precedes samples[i]
for (let i = 0; i < samples.length; i++) {
  const id = samples[i];
  const d = deltas[i] > 0 ? deltas[i] : 0;
  self.set(id, (self.get(id) || 0) + d);
}

// ---- build inclusive time bottom-up via the node tree ----------------------
const incl = new Map();
const computeIncl = (id) => {
  if (incl.has(id)) return incl.get(id);
  const n = byId.get(id);
  let t = self.get(id) || 0;
  for (const c of n.children || []) t += computeIncl(c);
  incl.set(id, t);
  return t;
};
const root = prof.nodes[0];
const totalMicros = computeIncl(root.id);

// ---- layout: assign x,width (fraction) + depth, prune sub-pixel frames -----
const W = 1800;
const ROW = 16;
const MINPX = Number(process.env.FLAME_MINPX || 0.3); // skip frames narrower than this many px
const frames = []; // {x,w,depth,label,micros,id}
let maxDepth = 0;

const place = (id, x0, depth) => {
  const t = incl.get(id);
  const w = (t / totalMicros) * W;
  if (w < MINPX) return;
  const n = byId.get(id);
  frames.push({ x: x0, w, depth, label: labelOf(n.callFrame), micros: t, self: self.get(id) || 0 });
  if (depth > maxDepth) maxDepth = depth;
  // children ordered by inclusive time desc for stable, readable layout
  const kids = (n.children || []).slice().sort((a, b) => incl.get(b) - incl.get(a));
  let cx = x0;
  for (const c of kids) {
    const cw = (incl.get(c) / totalMicros) * W;
    place(c, cx, depth + 1);
    cx += cw;
  }
};
place(root.id, 0, 0);

// ---- color: stable hash -> warm flame palette ------------------------------
const color = (s) => {
  let h = 0;
  for (let i = 0; i < s.length; i++) h = (h * 31 + s.charCodeAt(i)) & 0xffff;
  const r = 205 + (h % 50);
  const g = 50 + ((h >> 4) % 160);
  const b = 30 + ((h >> 8) % 55);
  return `rgb(${r},${g},${b})`;
};
const esc = (s) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
const ms = (u) => (u / 1000).toFixed(1);
const pct = (u) => ((u / totalMicros) * 100).toFixed(1);

const H = (maxDepth + 1) * ROW + 40;
const title = titleArg || inPath.split("/").pop();

let rects = "";
for (const f of frames) {
  const y = H - 24 - (f.depth + 1) * ROW;
  const showText = f.w > 28;
  const txt = showText
    ? `<text x="${(f.x + 3).toFixed(1)}" y="${(y + ROW - 4).toFixed(0)}" font-size="10" font-family="monospace" fill="#000" clip-path="inset(0)">${esc(f.label.length > Math.floor(f.w / 6) ? f.label.slice(0, Math.floor(f.w / 6)) + "…" : f.label)}</text>`
    : "";
  rects +=
    `<g><rect x="${f.x.toFixed(2)}" y="${y}" width="${Math.max(f.w - 0.5, 0.5).toFixed(2)}" height="${ROW - 1}" fill="${color(f.label)}" stroke="#fff" stroke-width="0.3" data-x="${f.x.toFixed(2)}" data-w="${f.w.toFixed(2)}">` +
    `<title>${esc(f.label)}\n${ms(f.micros)} ms  (${pct(f.micros)}% incl, self ${ms(f.self)} ms)</title></rect>${txt}</g>\n`;
}

const svg = `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}" viewBox="0 0 ${W} ${H}" font-family="monospace">
<rect width="100%" height="100%" fill="#fafafa"/>
<text x="8" y="18" font-size="14" font-weight="bold">${esc(title)}</text>
<text x="8" y="32" font-size="10" fill="#555">total ${ms(totalMicros)} ms main-thread JS  ·  ${frames.length} frames  ·  width = inclusive time  ·  hover for detail, click to zoom</text>
<g id="frames">
${rects}</g>
<script type="text/javascript"><![CDATA[
var W=${W}; var g=document.getElementById('frames');
g.addEventListener('click',function(e){
  var r=e.target.closest('rect'); if(!r){return;}
  var zx=parseFloat(r.getAttribute('data-x')), zw=parseFloat(r.getAttribute('data-w'));
  if(zw<=0){return;}
  var rects=g.querySelectorAll('rect'), texts=g.querySelectorAll('text');
  for(var i=0;i<rects.length;i++){
    var x=parseFloat(rects[i].getAttribute('data-x')), w=parseFloat(rects[i].getAttribute('data-w'));
    var nx=(x-zx)/zw*W, nw=w/zw*W;
    rects[i].setAttribute('x',nx); rects[i].setAttribute('width',Math.max(nw-0.5,0));
    var t=rects[i].parentNode.querySelector('text');
    if(t){ t.setAttribute('x',nx+3); t.style.display = nw>28?'':'none'; }
  }
});
]]></script>
</svg>
`;

fs.writeFileSync(outPath, svg);
console.log(`wrote ${outPath}  (${frames.length} frames, depth ${maxDepth}, ${ms(totalMicros)} ms total)`);
