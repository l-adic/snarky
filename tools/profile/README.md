# tools/profile — profiling visualizations for the bench matrix

Reusable, zero-dependency tooling to answer, for PS vs o1js × native vs wasm:
**how parallel is each stack, and how much memory does it use, over the course
of a prove?** plus a drill-down (where does the time go in the code?).

Committed visualizations live in [`bench/profiles/`](../../bench/profiles/) as
PNGs. Everything else (SVGs, raw `.cpuprofile`s) is large/regenerable and stays
local in `prof/` (gitignored).

## The committed visuals: cores & memory timelines

Sampled from **`/proc`** (the whole process tree, every 50 ms) while the bench
runs — so they see native Rust threads, wasm rayon workers, AND o1js's per-trial
child processes, none of which a V8 `.cpuprofile` can account for. Four charts,
PS = blue, o1js = red:

- `cores-{native,wasm}-prove.png` — cores in use (`Δcpu/Δwall`) over one prove,
  **averaged across the 3 trials**. Shows the parallelism profile: serial valleys
  (witness-gen) vs parallel peaks (FFT/MSM).
- `rss-{native,wasm}-prove.png` — resident memory over the prove region (all 3
  trials), showing peak + whether memory accumulates or is reclaimed.

### Tools

- **`cpu_timeline.mjs <out.json> <label> -- <cmd...>`** — spawn a command, sample
  its process tree's cores + RSS over time, capture `[bench-window]` markers for
  phase segmentation. (Launchers are line-buffered so markers arrive live and on
  the sampler clock — including o1js's children.)
- **`timeline_chart.mjs <out.svg> "title" <timeline.json>...`** — line chart from
  one or more timelines. `METRIC=cores|rss`, `TRIM=prove` (restrict to timed
  windows), `AVERAGE=1` (collapse N trials into one aligned curve), `SMOOTH_MS`
  (default 300), `NPROC` (machine cores reference line).

### Recipe

```sh
export PATH="$HOME/.nvm/versions/node/v23.11.1/bin:$PATH"   # same node as the matrix
TL=prof/timeline; mkdir -p "$TL"
S="node tools/profile/cpu_timeline.mjs"
# Run ALONE on an idle machine — this IS the bench.
$S "$TL/ps-native-prove.json"   PS/native   -- tools/bench.sh --only prove
$S "$TL/ps-wasm-prove.json"     PS/wasm     -- tools/bench.sh --wasm --only prove
$S "$TL/o1js-native-prove.json" o1js/native -- tools/bench_o1js.sh --native --only prove
$S "$TL/o1js-wasm-prove.json"   o1js/wasm   -- tools/bench_o1js.sh --only prove

C=tools/profile/timeline_chart.mjs
TRIM=prove AVERAGE=1 METRIC=cores NPROC=20 node $C prof/cores-native-prove.svg "Cores during prove — native" "$TL"/{ps,o1js}-native-prove.json
TRIM=prove AVERAGE=1 METRIC=cores NPROC=20 node $C prof/cores-wasm-prove.svg   "Cores during prove — wasm"   "$TL"/{ps,o1js}-wasm-prove.json
TRIM=prove METRIC=rss NPROC=20 node $C prof/rss-native-prove.svg "Resident memory during prove — native" "$TL"/{ps,o1js}-native-prove.json
TRIM=prove METRIC=rss NPROC=20 node $C prof/rss-wasm-prove.svg   "Resident memory during prove — wasm"   "$TL"/{ps,o1js}-wasm-prove.json

# rasterize SVG -> PNG into bench/profiles/ (no system rasterizer needed)
npm install --prefix /tmp/raster @resvg/resvg-js
for f in prof/{cores,rss}-*.svg; do node -e 'import("/tmp/raster/node_modules/@resvg/resvg-js/index.js").then(({Resvg})=>{const fs=require("fs"),p=require("path"),a=process.argv[1];fs.writeFileSync("bench/profiles/"+p.basename(a).replace(/\.svg$/,".png"),new Resvg(fs.readFileSync(a,"utf8"),{background:"#fff",fitTo:{mode:"width",value:2400}}).render().asPng())}).catch(e=>{throw e})' "$f"; done
```

## Drill-down: flamegraphs (not committed — regenerable interactive SVGs)

The timelines say *how much* parallelism/memory; flamegraphs say *where in the
code*. A flamegraph is only useful interactively (click-to-zoom), so we keep the
tooling but do **not** commit static PNGs — generate the SVG and open it in a
browser when you need to dig in.

- **`flamegraph.mjs <in.cpuprofile> <out.svg> [title]`** — single-profile
  flamegraph; resolves PureScript module names and demangles wasm Rust symbols.
- **`flamemerge.mjs <out.svg> "title" <file...>`** — fold N profiles into one
  (collapse a rayon worker pool). `FLAME_MINPX` raises the prune threshold.
- **`rollup.mjs <label> <file...>`** — per-role busy/wait-spin/gc/idle split.

To capture cpuprofiles: `tools/bench.sh [--wasm] --cpu-prof --only <phase>`; for
o1js-wasm the prover runs in per-trial children, so inject via
`NODE_OPTIONS="--cpu-prof --cpu-prof-dir=$PWD/prof/raw"` to reach them.

**The rule for cpuprofiles:** a V8 `.cpuprofile`'s `timeDeltas` are wall time of
the sampled thread, **not CPU time** — you cannot sum across threads to get CPU
(20 wasm isolates alive ~95 s each sum to ~1800 s vs ~180 s real), and rayon
workers count `sleep::Sleep` spin as "running". So cpuprofiles are for
code-location attribution only; all CPU/memory **quantities** come from `/proc`
(the timelines above, and the matrix `cpu`/`cores` columns).
