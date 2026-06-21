#!/usr/bin/env node
// Render cores-in-use vs time as a line chart from cpu_timeline.mjs JSON(s).
// Overlays multiple configs on shared axes so you can see how concurrency rises
// and falls through a run (serial witness-gen valleys vs parallel FFT/MSM peaks).
//
//   node tools/profile/timeline_chart.mjs <out.svg> "Title" <timeline.json>...
//
// Each input is one line. Config label + color are inferred from the JSON label.

import fs from "fs";

const [, , outPath, title, ...files] = process.argv;
if (!outPath || !files.length) {
  console.error('usage: timeline_chart.mjs <out.svg> "Title" <timeline.json>...');
  process.exit(2);
}

const series = files.map((f) => {
  const d = JSON.parse(fs.readFileSync(f, "utf8"));
  return { label: d.label, samples: d.samples, markers: d.markers || [] };
});

// Phase windows come from the [bench-window] markers, timestamped at read-time
// by cpu_timeline (the launchers are line-buffered so markers arrive live and on
// the sampler clock — including o1js's per-trial children). TRIM=<substr>
// restricts to the matching timed windows (rebased to 0, dropping untimed
// prepare/compile); SHADE=1 shades each timed trial.
const TRIM = process.env.TRIM;
const SHADE = process.env.SHADE === "1";
for (const s of series) {
  const starts = s.markers.filter((m) => m.kind === "start" && (!TRIM || (m.label || "").toLowerCase().includes(TRIM)));
  const ends = s.markers.filter((m) => m.kind === "end" && (!TRIM || (m.label || "").toLowerCase().includes(TRIM)));
  s.windows = starts.map((m, i) => ({ s: m.t, e: ends[i]?.t ?? m.t })).filter((w) => w.e > w.s);
  if (TRIM && s.windows.length) {
    const lead = 500, tail = 500;
    const lo = Math.max(0, s.windows[0].s - lead);
    const hi = s.windows.at(-1).e + tail;
    s.samples = s.samples.filter((p) => p.t >= lo && p.t <= hi).map((p) => ({ t: p.t - lo, cores: p.cores }));
    s.windows = s.windows.map((w) => ({ s: Math.max(0, w.s - lo), e: w.e - lo }));
  }
}

// 4 distinct solid colors (PS = blues, o1js = oranges; native = dark, wasm = light).
const PALETTE = {
  "PS/native": "#1c5fb8", "PS/wasm": "#5aa9f0",
  "o1js/native": "#c2570f", "o1js/wasm": "#f0a050",
};
const styleOf = (label) => {
  const stack = /o1js/i.test(label) ? "o1js" : "PS";
  const backend = /wasm/i.test(label) ? "wasm" : "native";
  const key = `${stack}/${backend}`;
  return { stroke: PALETTE[key] || "#666", key, stack, backend };
};

// centered moving-average smoothing over SMOOTH_MS of wall time (0 = raw).
const SMOOTH_MS = Number(process.env.SMOOTH_MS ?? 300);
const smooth = (samples) => {
  if (!SMOOTH_MS) return samples;
  return samples.map((p, i) => {
    let a = 0, n = 0;
    for (let j = i; j >= 0 && p.t - samples[j].t <= SMOOTH_MS / 2; j--) { a += samples[j].cores; n++; }
    for (let j = i + 1; j < samples.length && samples[j].t - p.t <= SMOOTH_MS / 2; j++) { a += samples[j].cores; n++; }
    return { t: p.t, cores: a / n };
  });
};

const W = 1100, H = 520, padL = 56, padR = 20, padT = 56, padB = 56;
const plotW = W - padL - padR, plotH = H - padT - padB;
const maxT = Math.max(...series.flatMap((s) => s.samples.map((p) => p.t)), 1);
const maxC = Math.max(20, Math.ceil(Math.max(...series.flatMap((s) => s.samples.map((p) => p.cores))) + 1));
const x = (t) => padL + (t / maxT) * plotW;
const y = (c) => padT + plotH - (c / maxC) * plotH;
const esc = (s) => String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;");

let g = "";
// gridlines + y labels (cores)
for (let c = 0; c <= maxC; c += 2) {
  g += `<line x1="${padL}" y1="${y(c).toFixed(1)}" x2="${W - padR}" y2="${y(c).toFixed(1)}" stroke="#eee"/>`;
  g += `<text x="${padL - 6}" y="${(y(c) + 3).toFixed(1)}" text-anchor="end" font-size="10" fill="#888">${c}</text>`;
}
// x labels (seconds)
for (let s = 0; s <= maxT / 1000; s += Math.max(1, Math.round(maxT / 1000 / 10))) {
  g += `<line x1="${x(s * 1000).toFixed(1)}" y1="${padT}" x2="${x(s * 1000).toFixed(1)}" y2="${padT + plotH}" stroke="#f4f4f4"/>`;
  g += `<text x="${x(s * 1000).toFixed(1)}" y="${padT + plotH + 16}" text-anchor="middle" font-size="10" fill="#888">${s}s</text>`;
}
// nproc reference line if known via env
if (process.env.NPROC) {
  const np = Number(process.env.NPROC);
  g += `<line x1="${padL}" y1="${y(np).toFixed(1)}" x2="${W - padR}" y2="${y(np).toFixed(1)}" stroke="#bbb" stroke-dasharray="2,3"/>`;
  g += `<text x="${W - padR - 4}" y="${(y(np) - 4).toFixed(1)}" text-anchor="end" font-size="9" fill="#999">${np} cores (machine)</text>`;
}

// shade trial windows (per-config panels)
if (SHADE) for (const s of series) for (const w of s.windows || []) {
  g += `<rect x="${x(w.s).toFixed(1)}" y="${padT}" width="${(x(w.e) - x(w.s)).toFixed(1)}" height="${plotH}" fill="#2a7de1" opacity="0.10"/>`;
}

const single = series.length === 1;
for (const s of series) {
  const st = styleOf(s.label);
  const sm = smooth(s.samples);
  const line = sm.map((p) => `${x(p.t).toFixed(1)},${y(p.cores).toFixed(1)}`).join(" ");
  if (single) { // area fill for per-config panels
    const area = `${x(0).toFixed(1)},${y(0).toFixed(1)} ${line} ${x(sm.at(-1).t).toFixed(1)},${y(0).toFixed(1)}`;
    g += `<polygon points="${area}" fill="${st.stroke}" opacity="0.12"/>`;
  }
  g += `<polyline points="${line}" fill="none" stroke="${st.stroke}" stroke-width="${single ? 1.6 : 1.5}" opacity="0.92"/>`;
}

// legend
let lx = padL + 8, ly = padT + 12;
for (const s of series) {
  const st = styleOf(s.label);
  g += `<line x1="${lx}" y1="${ly}" x2="${lx + 22}" y2="${ly}" stroke="${st.stroke}" stroke-width="2.5"/>`;
  g += `<text x="${lx + 28}" y="${ly + 3}" font-size="11" fill="#333">${esc(s.label)}</text>`;
  ly += 16;
}

const svg = `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}" font-family="sans-serif">
<rect width="100%" height="100%" fill="#fff"/>
<text x="${W / 2}" y="26" text-anchor="middle" font-size="16" font-weight="bold">${esc(title)}</text>
<text x="16" y="${padT + plotH / 2}" transform="rotate(-90 16 ${padT + plotH / 2})" text-anchor="middle" font-size="11" fill="#555">cores in use (Δcpu/Δwall)</text>
<text x="${padL + plotW / 2}" y="${H - 8}" text-anchor="middle" font-size="11" fill="#555">wall time</text>
${g}
</svg>`;
fs.writeFileSync(outPath, svg);
console.log(`wrote ${outPath} (${series.length} series, ${maxT / 1000 | 0}s, peak ~${maxC} cores axis)`);
