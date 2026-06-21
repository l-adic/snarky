# Bench suite — snarky-PS vs o1js (native & wasm)

An apples-to-apples benchmark of this repo's PureScript pickles stack (`snarky`)
against [o1js](https://github.com/o1-labs/o1js), on the **identical workload**
driven through the **identical runner**.

- **Same runner:** both stacks bind one shared JS library, `bench/harness`
  (`bench-harness`) — the PS side via an FFI module (`Bench.Harness`), the o1js
  side via its `index.d.ts`. They resolve the *same* `index.js`, so "the harness
  is the same" is literal, not by convention.
- **Same workload:** an NRR base program + an N=2 recursive tree program, step
  domain **2^16** on both sides (`packages/pickles-bench` ↔ `bench/o1js/src/programs.ts`).
- **Same node**, **same trial count (3)**, **same prepare(untimed)/work(timed)**
  split.

## The matrix (4 configs)

| config | command | backend that runs |
|---|---|---|
| PS native | `tools/bench.sh` | kimchi-napi (`.node`, native rust) |
| PS wasm | `tools/bench.sh --wasm` | kimchi-napi `wasm32-wasip1-threads` (rayon) |
| o1js native | `tools/bench_o1js.sh --native` | `@o1js/native` (napi rust) |
| o1js wasm | `tools/bench_o1js.sh` | o1js default `plonk_wasm` (wasm-bindgen) |

Each run produces one JSON artifact in `bench-results/` (per-trial samples,
mean/stddev, GC reclaim per trial, and — PS only — a Rust/JS `rustShare` split).

---

## 1. Prerequisites

- **Node v23.11.1**, installed via `nvm` (the launchers hard-code the path
  `$HOME/.nvm/versions/node/v23.11.1/bin`, so both stacks use the *same* JS
  runtime — essential for a fair comparison):
  ```sh
  nvm install 23.11.1
  ```
  If your node lives elsewhere, edit the `export PATH=…` line at the top of
  `tools/bench.sh` **and** `tools/bench_o1js.sh` to point at the same node for
  both. Do **not** run the two stacks on different node versions.
- **Rust** stable toolchain (builds the native + wasm kimchi-napi bindings).
- A way to pin the CPU to **`performance`** (a `balanced`/`power-saver` box
  throttles ~3× and ruins wall numbers). `powerprofilesctl set performance` if
  it's installed; otherwise the **`intel_pstate`/sysfs** route —
  `sudo cpupower frequency-set -g performance`, or
  `echo performance | sudo tee /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor`.
  If you can't change it, that's OK — the artifact records `powerProfile`, so
  note it; just don't compare across different profiles. The matrix warns (it
  doesn't block) if it can't confirm `performance`.
- A machine that's **idle / single-tenant** during the run (this is the big one
  — a competing Mina node or a second bench *will* deadlock the run and corrupt
  numbers). `bench_matrix.sh` takes a lockfile and warns on high load / other
  bench processes, but it can't stop unrelated load — make sure nothing else is
  running. Enough RAM too (o1js-wasm peaks ~5–8 GB RSS).

## 2. One-time setup (build everything)

From the repo root, on branch `bench-shared-harness`:

```sh
git checkout bench-shared-harness

# Root deps + the native kimchi-napi binding + workspace symlinks
# (this also links node_modules/bench-harness → bench/harness).
npm install

# The wasm kimchi-napi binding (needed for `--wasm`)
npm run build:wasm -w kimchi-napi

# SRS files (needed by pickles) and the pickles linearization codegen
make fetch-srs
make gen-linearization

# The o1js bench package: o1js 2.15.0 + @o1js/native 2.15.0 + bench-harness
cd bench/o1js && npm install && cd ../..
```

Sanity-check each backend loads before the long run:

```sh
# PS bench builds (purs-backend-es) — what the launcher does. Run from the bench
# workspace; `spago sources` emits paths relative to it, so don't run purs from
# the repo root.
( cd packages/pickles-bench && npx spago build ) && echo PS-ok
# o1js circuit analysis, native + wasm (no prove — seconds)
( cd bench/o1js && npm run build && O1JS_BACKEND=native npm run rows && O1JS_BACKEND=wasm npm run rows )
```
`rows` should print `tree.step rows = 32772 (domain 2^16)` for both backends.

## 3. Run the full matrix

```sh
# Pin the CPU first.
powerprofilesctl set performance

# N iterations of all 4 configs (default 3). Each iteration runs the configs
# in order ps-native → o1js-native → ps-wasm → o1js-wasm, 60s apart, so every
# PS↔o1js pairing is at the same thermal state.
tools/bench_matrix.sh 5
```

This writes, under `bench-results/<runid>-…`:
- `…-{ps,o1js}-{native,wasm}-i<N>.json` — **one artifact per iteration** (the
  per-iteration results you asked to keep).
- `…-{...}-i<N>.log` — the raw run log for each (kept for triage).
- **`…-summary.md`** — the combined summary (also printed at the end).

Wall time ≈ `iters × 4 × (run + 60s)`. With native ~1–3 min/run and o1js-wasm
~10–20 min/run, **5 iterations is several hours** — fine on a dedicated box;
start with `tools/bench_matrix.sh 2` to validate the pipeline first.

### Running one config manually (optional)

```sh
BENCH_RESULTS_FILE=bench-results/my-ps-native.json   tools/bench.sh
BENCH_RESULTS_FILE=bench-results/my-o1js-native.json tools/bench_o1js.sh --native
# (PS wasm renames its artifact to wasm-<name>.json — see bench_matrix.sh.)
```

Combine any set of artifacts into a summary yourself:
```sh
node tools/bench_summary.mjs bench-results/<runid>-*-i*.json > summary.md
# or a one-row-per-artifact table:
node tools/bench_table.mjs bench-results/a.json bench-results/b.json
```

## 4. Reading the results — methodology & honest caveats

- **Wall time is the headline and is fully valid.** `runBench` times
  `await work()` end-to-end on the main thread; it doesn't matter which thread
  the prover runs on.
- **Both stacks run the prover on worker threads** (kimchi-napi's async pool /
  rayon; o1js's wasm/native workers). So:
  - **Native reclaim/trial is trustworthy** and comparable PS↔o1js.
  - **wasm reclaim/trial is a main-isolate *lower bound*** — the prover's
    memory lives in worker isolates / wasm linear memory, invisible to
    `--trace-gc`. It captures only main-thread (witness-gen) JS churn. Compare
    wasm reclaim **only wasm-to-wasm**, never wasm-to-native.
- **`rustShare` is PS-only** (it times the kimchi-napi boundary). o1js has no
  equivalent here, so its column is `—`.
- **Parity evidence:** `tree.step` domain is **2^16 on both stacks**. The row
  *counts* differ (PS ~53,960 vs o1js ~32,772) because gate accounting differs;
  the FFT **domain** governs the work, and it matches. The summary prints rows.
- **The cross-stack table is reporting only**, never a regression gate. The gate
  is `packages/pickles-bench/compare.mjs`, and it only ever compares same-stack
  runs.

## 5. Troubleshooting

- **o1js wasm OOM / slow:** wasm has a 4 GB linear-memory ceiling per worker and
  is 2–2.5× slower than native; expect long runs and high RSS. If it OOMs,
  reduce concurrency or run wasm configs separately.
- **o1js wasm is slow (per-trial fresh processes — by design):** under `--wasm`
  the o1js bench runs **each timed trial in its own node process** (`bench.ts`
  does this automatically), so a single o1js-wasm run spawns 6 child processes
  and re-pays the untimed SRS+compile setup each time → expect ~8–12 min/run.
  *Why:* o1js doesn't release its prover-key wasm memory between compiles
  (`forceRecompile` re-synthesizes without freeing; `forceGc` can't touch wasm
  linear memory), so a single process climbs ~1 GB/compile and a worker
  eventually crosses the wasm32 **4 GB instance ceiling**, OOMs, and the main
  thread deadlocks awaiting the dead worker. A fresh process per trial caps
  memory at one trial's worth (OS reclaims on exit). The timed numbers are
  unaffected — setup/warmup is untimed `prepare` on both sides, and each child's
  prepare warms the JIT. (Watch the difference with `BENCH_RSS=1`: single-process
  o1js climbs `2.2 → 3.9 → 4.6 → 5.3 GB` and never plateaus; our kimchi-napi wasm
  plateaus ~2.2 GB because it returns prover memory via a FinalizationRegistry on
  the harness's gc-yield-gc. **Native o1js and PS are single-process** — no
  ceiling, no per-trial spawning.) If o1js-wasm STILL wedges on the bench box,
  confirm it's wedged (not slow) by sampling `utime+stime` (fields 14+15) of
  `/proc/<pid>/stat` over a few seconds — 0 delta = deadlocked.
- **`node: command not found` / wrong version:** the launchers expect node at
  the v23.11.1 nvm path; install it or edit the `PATH` line in both launchers.
- **`KIMCHI_BACKEND=wasm` fails to load:** you didn't run
  `npm run build:wasm -w kimchi-napi`, or the build is stale.
- **o1js `setBackend('native')` throws:** `@o1js/native@2.15.0` isn't installed
  in `bench/o1js` (`cd bench/o1js && npm install`).
- **Noisy prove numbers** (esp. wasm): expected; that's exactly why we take
  multiple iterations. The summary reports across-iteration stddev so you can
  see it.
