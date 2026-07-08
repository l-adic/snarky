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

// METRIC=cores (default) | rss. Each sample is normalized to {t, v}.
const METRIC = (process.env.METRIC || "cores").toLowerCase();
const FIELD = METRIC === "rss" ? "rssMB" : "cores";
const series = files.map((f) => {
  const d = JSON.parse(fs.readFileSync(f, "utf8"));
  return {
    label: d.label,
    samples: (d.samples || []).map((p) => ({ t: p.t, v: METRIC === "rss" ? (p.rssMB ?? 0) : (p.cores ?? 0) })),
    markers: d.markers || [],
    intervalMs: d.intervalMs || 50,
  };
});

// Phase windows come from the [bench-window] markers, timestamped at read-time
// by cpu_timeline (launchers are line-buffered so markers arrive live and on the
// sampler clock — including o1js's per-trial children). TRIM=<substr> selects the
// matching timed windows (e.g. "prove"). AVERAGE=1 collapses a config's N trials
// into ONE representative curve: each trial is aligned to its own start and the
// cores are averaged across trials onto a common time grid (linear interp).
const TRIM = process.env.TRIM;
const AVERAGE = process.env.AVERAGE === "1";
const SHADE = process.env.SHADE === "1" && !AVERAGE;

const interp = (samples, t) => { // linear interp of value at time t over a trial's rebased samples
  if (!samples.length) return null;
  if (t <= samples[0].t) return samples[0].v;
  if (t >= samples.at(-1).t) return samples.at(-1).v;
  let lo = 0, hi = samples.length - 1;
  while (hi - lo > 1) { const m = (lo + hi) >> 1; if (samples[m].t <= t) lo = m; else hi = m; }
  const a = samples[lo], b = samples[hi];
  return a.v + (b.v - a.v) * ((t - a.t) / (b.t - a.t || 1));
};

for (const s of series) {
  const starts = s.markers.filter((m) => m.kind === "start" && (!TRIM || (m.label || "").toLowerCase().includes(TRIM)));
  const ends = s.markers.filter((m) => m.kind === "end" && (!TRIM || (m.label || "").toLowerCase().includes(TRIM)));
  const windows = starts.map((m, i) => ({ s: m.t, e: ends[i]?.t ?? m.t })).filter((w) => w.e > w.s);
  s.windows = windows;
  if (!windows.length) continue;

  if (AVERAGE) {
    // per-trial curves, rebased to 0
    const trials = windows.map((w) => s.samples.filter((p) => p.t >= w.s && p.t <= w.e).map((p) => ({ t: p.t - w.s, v: p.v })));
    const maxDur = Math.max(...trials.map((tr) => tr.at(-1)?.t ?? 0));
    const dt = s.intervalMs;
    const avg = [];
    for (let t = 0; t <= maxDur; t += dt) {
      const vals = [];
      for (const tr of trials) {
        if (!tr.length || t > tr.at(-1).t) continue; // skip trials that already ended
        const v = interp(tr, t);
        if (v != null) vals.push(v);
      }
      if (vals.length) avg.push({ t, v: vals.reduce((a, b) => a + b, 0) / vals.length });
    }
    s.samples = avg;
    s.windows = [];
  } else if (TRIM) {
    const lead = 500, tail = 500;
    const lo = Math.max(0, windows[0].s - lead), hi = windows.at(-1).e + tail;
    s.samples = s.samples.filter((p) => p.t >= lo && p.t <= hi).map((p) => ({ t: p.t - lo, v: p.v }));
    s.windows = windows.map((w) => ({ s: Math.max(0, w.s - lo), e: w.e - lo }));
  }
}

// Color by stack: PS = blue, o1js·witness = red, o1js·witnessFields = green.
const styleOf = (label) => {
  const stack = /o1js/i.test(label) ? "o1js" : "PS";
  const backend = /wasm/i.test(label) ? "wasm" : "native";
  const wf = /witnessfields|\bwf\b/i.test(label);
  const stroke = stack === "o1js" ? (wf ? "#2ca02c" : "#d62728") : "#2a7de1";
  return { stroke, stack, backend };
};

// centered moving-average smoothing over SMOOTH_MS of wall time (0 = raw).
const SMOOTH_MS = Number(process.env.SMOOTH_MS ?? 300);
const smooth = (samples) => {
  if (!SMOOTH_MS) return samples;
  return samples.map((p, i) => {
    let a = 0, n = 0;
    for (let j = i; j >= 0 && p.t - samples[j].t <= SMOOTH_MS / 2; j--) { a += samples[j].v; n++; }
    for (let j = i + 1; j < samples.length && samples[j].t - p.t <= SMOOTH_MS / 2; j++) { a += samples[j].v; n++; }
    return { t: p.t, v: a / n };
  });
};

const W = 1100, H = 520, padL = 60, padR = 20, padT = 56, padB = 56;
const plotW = W - padL - padR, plotH = H - padT - padB;
const maxT = Math.max(...series.flatMap((s) => s.samples.map((p) => p.t)), 1);
const dataMax = Math.max(...series.flatMap((s) => s.samples.map((p) => p.v)), 1);
// y axis: cores → 0..max(20, data); rss → 0..(data in GB, rounded up)
const RSS = METRIC === "rss";
// cores axis tops out just past the machine's core count (NPROC) or the data,
// whichever is larger — so the reference line sits near the top on any machine.
const coresCap = process.env.NPROC ? Number(process.env.NPROC) + 1 : 20;
const maxY = RSS ? Math.ceil(dataMax / 1024 * 1.1) * 1024 : Math.max(coresCap, Math.ceil(dataMax + 1));
const yStep = RSS ? 1024 : 2; // 1 GB ticks for rss, 2-core ticks for cores
const yLabel = (val) => (RSS ? (val / 1024).toFixed(0) : String(val));
const x = (t) => padL + (t / maxT) * plotW;
const y = (v) => padT + plotH - (v / maxY) * plotH;
const esc = (s) => String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;");

let g = "";
// gridlines + y labels
for (let v = 0; v <= maxY; v += yStep) {
  g += `<line x1="${padL}" y1="${y(v).toFixed(1)}" x2="${W - padR}" y2="${y(v).toFixed(1)}" stroke="#eee"/>`;
  g += `<text x="${padL - 6}" y="${(y(v) + 3).toFixed(1)}" text-anchor="end" font-size="10" fill="#888">${yLabel(v)}</text>`;
}
// x labels (seconds)
for (let s = 0; s <= maxT / 1000; s += Math.max(1, Math.round(maxT / 1000 / 10))) {
  g += `<line x1="${x(s * 1000).toFixed(1)}" y1="${padT}" x2="${x(s * 1000).toFixed(1)}" y2="${padT + plotH}" stroke="#f4f4f4"/>`;
  g += `<text x="${x(s * 1000).toFixed(1)}" y="${padT + plotH + 16}" text-anchor="middle" font-size="10" fill="#888">${s}s</text>`;
}
// reference line: cores → machine nproc (env NPROC)
if (!RSS && process.env.NPROC) {
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
  if (!sm.length) continue;
  const line = sm.map((p) => `${x(p.t).toFixed(1)},${y(p.v).toFixed(1)}`).join(" ");
  if (single) { // area fill for single-line charts
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
<text x="16" y="${padT + plotH / 2}" transform="rotate(-90 16 ${padT + plotH / 2})" text-anchor="middle" font-size="11" fill="#555">${RSS ? "resident memory (GB, whole process tree)" : "cores in use (Δcpu/Δwall)"}</text>
<text x="${padL + plotW / 2}" y="${H - 8}" text-anchor="middle" font-size="11" fill="#555">wall time</text>
${g}
</svg>`;
fs.writeFileSync(outPath, svg);
console.log(`wrote ${outPath} (${series.length} series, ${maxT / 1000 | 0}s, ${METRIC}, axis 0..${RSS ? (maxY / 1024).toFixed(0) + "GB" : maxY})`);
