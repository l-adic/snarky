# o1js-bench

Apples-to-apples benchmark of [o1js](https://github.com/o1-labs/o1js)
against this repo's `pickles-bench` workload. All stacks drive the
same proof system (kimchi/pickles on Pasta curves), giving a THREE-WAY
comparison:

| Stack | Kimchi backend | What the pairing measures |
|---|---|---|
| snarky-PS (`tools/bench.sh`) | native (napi-rs) | — |
| o1js wasm (`tools/bench_o1js.sh`) | js_of_ocaml + WASM | what production o1js users experience today |
| o1js native (`tools/bench_o1js.sh --native`) | native (napi-rs, `@o1js/native`, `setBackend('native')`) | the TIGHTEST pairing: same boundary style both sides, so the delta is the JS framework layer itself |

o1js docs (o1js.dev/native-prover): native is opt-in, 2-2.5x faster
proving than WASM, no 4 GB WASM memory cap.

A standalone TypeScript package: it deliberately does NOT live under
`packages/` (that's the PureScript workspace).

## Workload parity

Mirrors `Bench.Pickles.Common`:

| PS suite | o1js mirror |
|---|---|
| NRR rule (0 prevs, output 0) | `Nrr.base` |
| Tree rule: prevs `[NRR, Self]`, conditional verify on Self (base sentinel `-1`), output `prev + 1` | `Tree.step` with `verifyIf` + `Proof.dummy` |
| 2^16 filler `mul_ zero zero` ⇒ 53,960 rows ⇒ step domain 2^16 | `FILLER_ITERS` witnessed-zero muls — **needs tuning** (`npm run rows`) until `tree.step` lands in domain 2^16 |
| compile group: NRR + tree compile, 3 trials, warm SRS | warmup compile, then 3 `forceRecompile` trials |
| prove group: b1 merge prove, b0 untimed | 6 timed `Tree.step(nrr, b0)` trials |

Row counts ship in every artifact (`circuitRows`) — matching domains
is the apples-to-apples evidence; report them next to every number.

## Measurement parity

Same pipeline as `tools/bench.sh`: `node --trace-gc`, identical
`[bench-window]` markers, GC reclaim/trial attached by the PS suite's
`parse_gclog.mjs`, same artifact schema (plus `suite: "o1js"`,
`o1jsVersion`, `circuitRows`) into `bench-results/`.

Instrument-by-instrument parity with the PS suite:

| PS instrument | o1js side |
|---|---|
| `[bench-window]` markers -> parse_gclog reclaim | identical markers, same parser |
| Per-trial GC observer + `--- Benchmarking Report ---` lines | mirrored (`PerformanceObserver('gc')`) |
| `--cpu-prof` whole-process profile via launcher flag | mirrored (`tools/bench_o1js.sh --cpu-prof`); NEITHER suite has in-process profiler start/stops |
| kimchi-napi FFI wrappers (`rustShare`) + FfiTimer (`[prove split]`) | impossible: o1js's kimchi is WASM inside the JS heap — no boundary to wrap |

Audited window-content parity (what's inside each timed region):

| hazard | PS suite | o1js side |
|---|---|---|
| SRS build + lagrange warmup | `mkBenchSrs` once in Main, untimed | untimed warmup compile populates the process-global in-memory `srsStore`; lagrange sticks to the SRS object (separate `srsCache`, NOT the compile `cache` option) |
| prover-key creation | eager, inside the compile window | eager (`lazyMode` defaults to false), inside the compile window |
| disk cache I/O in compile trials | none | `cache: Cache.None` — the default FileSystemDefault cache wrote ~650 MB of prover keys per timed trial (measured: +5s/trial and most of the trial-to-trial jitter) |
| prove window | one `treeProver` call (witness gen + step + wrap prove, prevs resident) | one `Tree.step(nrr, b0)` (same three phases, same resident prevs) |
| wrap domains | NRR default 2^13; tree `Just 14` | NRR default `maxProofsToWrapDomain[0]`=N0=2^13; tree default `[2]`=N1=2^14 — identical |
| step domain | 2^16 | 2^16, proven by the `Proof.dummy` exact-domain contract |
| residual asymmetry | FFI-tracking wrappers + FfiTimer around every napi call (~800 wrapped calls/prove trial) | none — slightly favors o1js |

Structural caveat for reclaim comparisons, WASM MODE ONLY: the wasm
backend runs provers on worker threads, whose isolates are invisible
to both main-thread `--trace-gc` and the GC observer — treat wasm-mode
reclaim as a lower bound. The native backend uses native OS threads
with a noop JS thread pool (see its `native-backend.js`), so its JS
work stays on the main isolate and reclaim is directly comparable to
the PS suite's.

## Running

```sh
tools/bench_o1js.sh        # from the repo root: install, build, bench
cd o1js-bench && npm run rows   # tuning helper: rows per method
```

Fairness checklist (same as the PS suite): performance power profile,
nothing else running, warm caches, same node binary; record everything
the artifact records.

## Status

Scaffold. Before first real numbers:
1. `npm install` and fix any o1js 2.15 API drift in `programs.ts`
   (`verifyIf`, `Proof.dummy`, `analyzeMethods` shapes).
2. Tune `FILLER_ITERS` via `npm run rows` to hit domain 2^16.
3. One calibration run; sanity-check reclaim attribution windows.
