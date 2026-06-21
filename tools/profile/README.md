# tools/profile — CPU profiling & flamegraphs for the bench matrix

Reusable, zero-dependency tooling to turn `--cpu-prof` output from the bench
launchers into flamegraphs and a parallelism chart, for answering "where does
the time go, and how parallel is each stack" (PS vs o1js, native vs wasm).

Committed visualizations live in [`bench/profiles/`](../../bench/profiles/).
Raw `.cpuprofile` dumps are large and local-only (`prof/` is gitignored).

## The one rule that governs all of this

**A V8 `.cpuprofile`'s `timeDeltas` are wall time of the sampled thread, not CPU
time.** Two consequences, both of which bite if ignored:

1. You **cannot sum cpuprofile time across threads** to get CPU. A wasm prover
   runs ~20 isolates alive ~95 s each → ~1800 s of "presence" while the OS
   counted ~180 s of actual CPU (a ~10× overcount).
2. rayon workers count `sleep::Sleep::sleep` **spin** as "running" samples
   (~50% of a worker's presence).

So the division of labor is strict:

| question | source |
|---|---|
| **how much CPU / how parallel** (numbers) | `/proc` cpu+cores → the bench `*-summary.md` and `chart.mjs` |
| **where serial JS goes** (one thread) | a main-isolate flamegraph (`flamegraph.mjs`) |
| **where the parallel prover goes** (proportional) | merged worker flamegraph (`flamemerge.mjs`) |

cpuprofiles = code-location attribution only. Every *quantity* comes from the
matrix `/proc` numbers, never from summing profiles.

## Tools

- **`flamegraph.mjs <in.cpuprofile> <out.svg> [title]`** — single-profile
  flamegraph (root at bottom, width = inclusive time). Hover = ms/%/self; click
  a frame to zoom (works in a browser). Resolves PureScript module names and
  demangles wasm Rust symbols.
- **`flamemerge.mjs <out.svg> "title" <file.cpuprofile>...`** — fold N profiles
  into one tree. Use to collapse a worker pool (e.g. 19 rayon isolates) into a
  single proportional view. Width = share of pool wall-presence (NOT CPU);
  sleep/spin frames are kept but easy to spot.
- **`rollup.mjs <label> <file.cpuprofile>...`** — per-role (main vs worker)
  split of busy / wait-spin / gc / idle. Sanity tool; remember the across-thread
  totals are wall-presence, not CPU.
- **`chart.mjs <out.svg> <bench-results/<runid>-*.json>...`** — avg-cores
  (cpu/wall) bar chart per config, compile vs prove, read straight from matrix
  artifacts. The authoritative parallelism picture.

## End-to-end recipe

```sh
export PATH="$HOME/.nvm/versions/node/v23.11.1/bin:$PATH"   # same node as the matrix

# 1. Profile each config. Profiles land in prof/ (gitignored).
#    o1js-wasm runs the prover in per-trial CHILD processes, so inject --cpu-prof
#    via NODE_OPTIONS to reach the prover child (the launcher flag only hits the parent).
rm -f prof/CPU.*.cpuprofile
tools/bench.sh --cpu-prof                                   # PS native
tools/bench.sh --wasm --cpu-prof                            # PS wasm  (main + ~20 worker isolates)
tools/bench_o1js.sh --native --cpu-prof                     # o1js native
NODE_OPTIONS="--cpu-prof --cpu-prof-dir=$PWD/prof/o1js-wasm-raw" tools/bench_o1js.sh   # o1js wasm

# 2. Identify isolates. Filename = CPU.<date>.<pid>.<thread>.<seq>.cpuprofile
#    thread 0 = main isolate (serial JS); threads >0 = worker isolates (wasm only).
#    For o1js-wasm pick a PROVE child (later/larger pids; 20 isolates each).

# SVGs are generated into prof/ (scratch, gitignored). Only the rasterized PNGs
# are committed to bench/profiles/ (SVGs are large & regenerable — see step 6).

# 3. Serial flamegraph (main isolate) per config:
node tools/profile/flamegraph.mjs <main.cpuprofile> prof/<cfg>.flame.svg "<cfg> — main isolate JS"

# 4. Merged worker flamegraph (wasm only), folding threads 1..N of one process.
#    Worker merges are huge; FLAME_MINPX raises the prune threshold to shrink them:
FLAME_MINPX=1.0 node tools/profile/flamemerge.mjs prof/<cfg>-workers.flame.svg "<cfg> — workers merged" prof/CPU.*.<pid>.[1-9].*.cpuprofile prof/CPU.*.<pid>.1[0-9].*.cpuprofile

# 5. Parallelism chart from the matrix run:
node tools/profile/chart.mjs prof/parallelism.svg bench-results/<runid>-*-i*.json

# 6. Rasterize SVG -> PNG into bench/profiles/ (committed). No system rasterizer needed:
npm install --prefix /tmp/raster @resvg/resvg-js
node -e 'import("/tmp/raster/node_modules/@resvg/resvg-js/index.js").then(({Resvg})=>{const fs=require("fs"),p=require("path");for(const a of process.argv.slice(1)){const svg=fs.readFileSync(a,"utf8");fs.writeFileSync("bench/profiles/"+p.basename(a).replace(/\.svg$/,".png"),new Resvg(svg,{background:"#fff",fitTo:{mode:"width",value:2400}}).render().asPng());}})' prof/*.svg
```

Commit the PNGs in `bench/profiles/`; the SVGs (interactive, click-to-zoom) and
raw `.cpuprofile`s stay local in `prof/` (gitignored). Open an SVG in a browser
when you need to actually explore deep frames.
