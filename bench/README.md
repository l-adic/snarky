# Benchmark suite — snarky-PS vs o1js (native & wasm)

An apples-to-apples benchmark of this repo's PureScript pickles stack (`snarky`)
against [o1js](https://github.com/o1-labs/o1js), on the **identical workload**
driven through the **identical runner**:

- **Same runner.** Both stacks bind one shared JS library, `bench/harness`
  (`bench-harness`) — the PS side via an FFI module (`Bench.Harness`), the o1js
  side via its `index.d.ts`. They resolve the *same* `index.js`, so "the harness
  is the same" is literal, not by convention.
- **Same workload.** An NRR base program + an N=2 recursive tree program, step
  domain **2^16** on both sides (`packages/pickles-bench` ↔ `bench/o1js/src/programs.ts`).
- **Same node, same trial count (3), same `prepare`(untimed) / `work`(timed) split.**

## The four configs

| config | command | backend that runs |
|---|---|---|
| PS native | `tools/bench.sh` | kimchi-napi (`.node`, native rust) |
| PS wasm | `tools/bench.sh --wasm` | kimchi-napi `wasm32-wasip1-threads` (rayon) |
| o1js native | `tools/bench_o1js.sh --native` | `@o1js/native` (napi rust) |
| o1js wasm | `tools/bench_o1js.sh` | o1js default `plonk_wasm` (wasm-bindgen) |

Each run writes one JSON artifact to `bench-results/`.

## Quick start

After the one-time [Setup](#setup-one-time) below, on an idle box:

```sh
powerprofilesctl set performance        # or the sysfs route — see Setup
tools/bench_matrix.sh 5                  # 5 iterations × 4 configs
```

This runs the configs each iteration in order `ps-native → o1js-native →
ps-wasm → o1js-wasm`, **60 s apart** so every PS↔o1js pairing is at the same
thermal state, and writes under `bench-results/<runid>-…`:

- `…-{ps,o1js}-{native,wasm}-i<N>.json` — one artifact **per iteration**.
- `…-{...}-i<N>.log` — the raw run log for each (triage).
- **`…-summary.md`** — the combined, aggregated summary (also printed at the end).

Wall time ≈ `iters × 4 × (run + 60 s)`; native is ~1–3 min/run, o1js-wasm
~8–12 min/run, so **5 iterations is several hours**. Start with
`tools/bench_matrix.sh 2` to validate the pipeline.

To run one config by hand, or re-aggregate artifacts:

```sh
BENCH_RESULTS_FILE=bench-results/my-ps-native.json tools/bench.sh
node tools/bench_summary.mjs bench-results/<runid>-*-i*.json > summary.md
node tools/bench_table.mjs   bench-results/a.json bench-results/b.json  # one row per artifact
```

---

## What we measure

Every metric below comes from the **shared `runBench`** (so PS and o1js are
instrumented identically) plus `parse_gclog.mjs`, into the artifact. Set
`BENCH_RSS=1` for the per-trial RSS lines.

| metric | what it is | units | symmetric? |
|---|---|---|---|
| **wall** | elapsed time of the timed `work()`, per trial → `mean ± stddev`, `min–max` across iterations | s | ✅ — the headline |
| **cpu time** | process-wide CPU time per trial (`process.cpuUsage()`, user+system) — sums the prover's worker/rayon threads | s | ✅ |
| **cores** | `cpu / wall` ≈ average cores used during the trial — exposes parallelism wall alone hides | × | ✅ |
| **reclaim/trial** | bytes reclaimed (Σ before−after over scavenges) inside each timed window | GB | ✅ native; ⚠ wasm (see below) |
| **gc pause** | total GC pause as % of the timed window; plus scavenge/major-GC counts and avg scavenge ms | %, counts | ✅ |
| **rss** | per-trial post-gc baseline + peak resident memory (`BENCH_RSS=1`, console only — not in the artifact) | GB | ✅ |
| **rustShare** | fraction of wall spent across the kimchi-napi boundary (Rust vs JS split) | 0–1 | ❌ **PS only** |
| **circuitRows** | rows per method — the parity evidence (must match the domain) | count | o1js (PS domain is implicit) |
| **metadata** | `node`, `nodeFlags`, `powerProfile`, `loadavg1`, `gitSha`/`dirty` | — | ✅ |

Two flags add extra (PS-only / both): `--cpu-prof` (V8 CPU profile →
`analyze_cpuprofile.mjs`, on either launcher) and the kimchi-napi FFI timers
that produce `rustShare` (PS only).

**The one asymmetry — `rustShare`.** It times the kimchi-napi boundary, which
only PS crosses observably. o1js's kimchi is WASM *inside the JS heap* (wasm
mode) — there's no boundary to time — so o1js's Rust-vs-JS split is **not
measured** (any decomposition of o1js's numbers is *inferred*, not observed).

**wasm reclaim is a lower bound (both stacks).** The prover runs on worker
isolates / wasm linear memory, invisible to main-isolate `--trace-gc`; wasm
reclaim captures only main-thread (witness-gen) churn. **Compare wasm reclaim
only wasm-to-wasm, never wasm-to-native.** Wall and CPU time are unaffected.

---

## Results

_From matrix run `20260621-132137` (`bench-results/20260621-132137-summary.md`)._

- machine: `Intel Core i5-13500 (20 threads)`  ·  node: `v23.11.1`  ·  iterations: `5`
- o1js `2.15.0`  ·  rows: PS tree.step `53,960` / o1js tree.step `32,772` (both domain 2^16)

### Compile — NRR + tree, step domain 2^16

| config | wall mean (s) | stddev (s) | cpu mean (s) | cores | reclaim/trial (GB) | rustShare |
|---|---|---|---|---|---|---|
| PS native   | 5.96  | 0.13 | 36.74  | 6.2 | 13.6  | 0.558 |
| o1js native | 15.61 | 0.06 | 40.54  | 2.6 | 15.0  | — |
| PS wasm     | 15.11 | 0.09 | 125.92 | 8.3 | 23.0† | 0.828 |
| o1js wasm   | 18.11 | 0.09 | 98.14  | 5.4 | 70.9† | — |

- **native:** o1js / PS = `2.62×`
- **wasm:** o1js / PS = `1.20×`

### Prove — b1 recursive merge

| config | wall mean (s) | stddev (s) | cpu mean (s) | cores | reclaim/trial (GB) | rustShare |
|---|---|---|---|---|---|---|
| PS native   | 6.29  | 0.15 | 62.07  | 9.9  | 7.7  | 0.577 |
| o1js native | 10.42 | 0.04 | 57.42  | 5.5  | 9.1  | — |
| PS wasm     | 13.67 | 0.04 | 187.64 | 13.7 | 7.6† | 0.800 |
| o1js wasm   | 15.92 | 0.03 | 157.65 | 9.9  | 27.6† | — |

- **native:** o1js / PS = `1.66×`
- **wasm:** o1js / PS = `1.16×`

† wasm reclaim is a main-isolate lower bound (see [What we measure](#what-we-measure)).

### Notes / interpretation

- **PS is faster in every cell** — wall-time wins of 2.62× / 1.20× (compile,
  native / wasm) and 1.66× / 1.16× (prove). Stddevs are ≤0.15 s everywhere, so
  the ordering is not noise.
- **PS extracts more parallelism.** The `cores` column (cpu/wall) is higher for
  PS in all four configs — prove native 9.9 vs 5.5, prove wasm 13.7 vs 9.9. PS
  pushes more work across the kimchi-napi boundary into the rayon-parallel Rust
  prover (`rustShare` 0.56–0.83), where o1js keeps more on a single JS thread
  (js_of_ocaml). See [Profiling & flamegraphs](#profiling--flamegraphs).
- **wasm costs ~2–2.5× vs native** for both stacks (PS prove 6.3→13.7 s, o1js
  prove 10.4→15.9 s), and the gap between stacks narrows under wasm.

---

## Setup (one-time)

From the repo root, on branch `bench-shared-harness`:

```sh
git checkout bench-shared-harness

# Root deps + native kimchi-napi binding + workspace symlinks
# (also links node_modules/bench-harness → bench/harness).
npm install

# wasm kimchi-napi binding (needed for --wasm)
npm run build:wasm -w kimchi-napi

# SRS files + pickles linearization codegen
make fetch-srs
make gen-linearization

# o1js bench package: o1js 2.15.0 + @o1js/native 2.15.0 + bench-harness
cd bench/o1js && npm install && cd ../..
```

**Prerequisites:**

- **Node v23.11.1** via `nvm` (`nvm install 23.11.1`). Both launchers hard-code
  `$HOME/.nvm/versions/node/v23.11.1/bin` so **both stacks use the same JS
  runtime** — essential for a fair comparison. If your node lives elsewhere, edit
  the `PATH` line at the top of `tools/bench.sh` **and** `tools/bench_o1js.sh` to
  the same node for both; they warn loudly if the pinned node is missing.
- **Rust** stable toolchain (builds the native + wasm bindings).
- **Pin the CPU to `performance`** — a `balanced`/`power-saver` box throttles ~3×.
  `powerprofilesctl set performance`, or the `intel_pstate`/sysfs route:
  `sudo cpupower frequency-set -g performance` /
  `echo performance | sudo tee /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor`.
  Can't change it? Fine — the artifact records `powerProfile`; just don't compare
  across profiles. The matrix warns (doesn't block) if it can't confirm it.
- **An idle, single-tenant machine** — a competing Mina node or a second bench
  *will* deadlock the run and corrupt numbers. `bench_matrix.sh` takes a lockfile
  and warns on high load, but can't stop unrelated load. Enough RAM too
  (o1js-wasm peaks ~5–8 GB RSS).

Sanity-check both backends load before the long run:

```sh
( cd packages/pickles-bench && npx spago build ) && echo PS-ok
( cd bench/o1js && npm run build && O1JS_BACKEND=native npm run rows && O1JS_BACKEND=wasm npm run rows )
```
`rows` should print `tree.step rows = 32772 (domain 2^16)` for both backends.

---

## Methodology & caveats

- **Wall is the headline and fully valid.** `runBench` times `await work()`
  end-to-end on the main thread; which thread the prover runs on doesn't matter.
- **`rustShare` is PS-only; o1js's split is inferred, not measured** (above). Any
  "o1js is X% crypto / Y% framework" statement is a model, not an observation —
  to measure it directly you'd wrap o1js-native's napi boundary the way we wrap
  ours.
- **Parity is on the domain, not the constraint count.** `tree.step` is domain
  **2^16** on both, but the row counts differ (PS ~53,960 vs o1js ~32,772) — so
  the FFT (domain-bound) matches while the constraint/commitment work (row-bound)
  does not. Worth keeping in mind when reading the crypto numbers. The summary
  prints rows so this stays visible.
- **The cross-stack table is reporting only**, never a regression gate. The gate
  is `packages/pickles-bench/compare.mjs`, same-stack only.
- **Noisy prove numbers** (esp. wasm) are expected — that's why we take multiple
  iterations; the summary reports across-iteration stddev.

---

## Profiling — cores & memory over time

The matrix says *how much*; these timelines show *how* each stack spends a prove
— its parallelism profile and its memory profile — sampled from `/proc` (the
whole process tree, so native Rust threads, wasm rayon workers, and o1js's
per-trial child processes are all counted). Tooling + recipe:
[`tools/profile/`](../tools/profile/README.md). Committed visualizations (PNG),
PS = blue, o1js = red:

- **`cores-{native,wasm}-prove.png`** — cores in use (`Δcpu/Δwall`) over one
  prove, averaged across the 3 trials. Parallel peaks (FFT/MSM) vs serial valleys
  (witness-gen); PS holds higher plateaus and spends less time pinned at 1 core.
- **`rss-{native,wasm}-prove.png`** — resident memory across the 3 prove trials.
  Note the wasm chart: PS plateaus (one process, memory reclaimed via a
  FinalizationRegistry) while o1js sawtooths (a fresh process per trial, reclaimed
  on exit — the per-trial-subprocess design).

Flamegraphs (where time goes *in the code*) are intentionally **not committed** —
a flamegraph is only useful interactively (click-to-zoom), so the tooling stays
in `tools/profile/` to regenerate the SVG on demand. The cpuprofile rule: a V8
`.cpuprofile`'s `timeDeltas` are wall time of the sampled thread, not CPU — so
all CPU/memory **quantities** come from `/proc` (these timelines + the matrix
`cpu`/`cores`), never from summing profiles.

---

## Troubleshooting

- **o1js wasm is slow (per-trial fresh processes — by design):** under `--wasm`
  the o1js bench runs **each timed trial in its own node process** (`bench.ts`
  does this automatically), so one o1js-wasm run spawns 6 child processes and
  re-pays the untimed SRS+compile setup each time → ~8–12 min/run.
  *Why:* o1js doesn't release its prover-key wasm memory between compiles
  (`forceRecompile` re-synthesizes without freeing; `forceGc` can't touch wasm
  linear memory), so a single process climbs ~1 GB/compile and a worker
  eventually crosses the wasm32 **4 GB instance ceiling**, OOMs, and the main
  thread deadlocks awaiting the dead worker. A fresh process per trial caps
  memory at one trial's worth (OS reclaims on exit); the timed numbers are
  unaffected (setup/warmup is untimed `prepare`, which also warms the JIT).
  Watch the difference with `BENCH_RSS=1`: single-process o1js climbs
  `2.2 → 3.9 → 4.6 → 5.3 GB` and never plateaus; our kimchi-napi wasm plateaus
  ~2.2 GB (it returns prover memory via a FinalizationRegistry on the harness's
  gc-yield-gc). **Native o1js and PS are single-process** — no ceiling, no
  spawning. If o1js-wasm *still* wedges: confirm it's wedged (not slow) by
  sampling `utime+stime` (fields 14+15) of `/proc/<pid>/stat` over a few
  seconds — a 0 delta means deadlocked, kill it.
- **A config hangs the whole matrix:** it shouldn't — each config runs under
  `timeout` (`BENCH_TIMEOUT`, default 2400 s); on timeout it marks the config
  MISSING, kills stragglers, and continues.
- **`node: command not found` / wrong version:** the launchers expect node at the
  v23.11.1 nvm path; install it or edit the `PATH` line in both launchers (they
  warn loudly and echo the node actually used).
- **`KIMCHI_BACKEND=wasm` fails to load:** you didn't run
  `npm run build:wasm -w kimchi-napi`, or the build is stale.
- **o1js `setBackend('native')` throws:** `@o1js/native@2.15.0` isn't installed
  in `bench/o1js` (`cd bench/o1js && npm install`).
- **`tsc` fails `TS7016` on `bench-harness`:** make sure `bench/harness/index.d.ts`
  is present (it's committed despite the repo-wide `*.d.ts` ignore, via a
  `!bench/harness/index.d.ts` exception).
- **Refused to start / `.matrix.lock`:** another bench holds the lock. If it's
  stale, `rm -rf bench-results/.matrix.lock`.
