# Benchmark suite — snarky-PS vs o1js (native & wasm)

An apples-to-apples benchmark of this repo's PureScript pickles stack against
o1js, on the same recursive proof workload (NRR base + N=2 tree merge, step
domain 2^16) driven through a shared JS bench runner (`bench/harness`). The
programs are defined in `packages/pickles-bench/src/Common.purs` and
`bench/o1js/src/programs.ts`.

## Quick start

```sh
tools/bench_matrix.sh --iters 5        # N iterations × 4 configs
```

To run one config by hand:

```sh
tools/bench.sh --only prove            # PS native, prove only
tools/bench_o1js.sh --native --only prove
tools/bench.sh --help                  # full usage
tools/bench_o1js.sh --help
```

## Results

_Intel Core i5-13500 (20 threads), node v23.11.1, 5 iterations._

o1js-wasm runs each timed trial in a fresh process: o1js doesn't free its wasm
prover memory between trials, so a single process hits the wasm32 4 GB ceiling
and deadlocks. This only slows the o1js-wasm *run* (it re-pays setup per trial);
the timed numbers are unaffected.

### Compile — NRR + tree, step domain 2^16

| config | wall mean (s) | stddev (s) | cpu mean (s) | cores |
|---|---|---|---|---|
| PS native   | 5.96  | 0.13 | 36.74  | 6.2 |
| o1js native | 15.61 | 0.06 | 40.54  | 2.6 |
| PS wasm     | 15.11 | 0.09 | 125.92 | 8.3 |
| o1js wasm   | 18.11 | 0.09 | 98.14  | 5.4 |

o1js is 2.62× slower than PS native, 1.20× slower wasm.

<p align="center">
<img src="profiles/cores-native-compile.png" width="700" alt="cores during compile — native" /><br/>
<sub>Cores in use during compile (native). PS (blue) sustains higher parallelism; o1js (red) spends more time single-threaded.</sub>
</p>

<p align="center">
<img src="profiles/cores-wasm-compile.png" width="700" alt="cores during compile — wasm" /><br/>
<sub>Cores in use during compile (wasm).</sub>
</p>

<p align="center">
<img src="profiles/rss-native-compile.png" width="700" alt="RSS during compile — native" /><br/>
<sub>Resident memory during compile (native).</sub>
</p>

<p align="center">
<img src="profiles/rss-wasm-compile.png" width="700" alt="RSS during compile — wasm" /><br/>
<sub>Resident memory during compile (wasm).</sub>
</p>

### Prove — b1 recursive merge

| config | wall mean (s) | stddev (s) | cpu mean (s) | cores |
|---|---|---|---|---|
| PS native   | 6.29  | 0.15 | 62.07  | 9.9  |
| o1js native | 10.42 | 0.04 | 57.42  | 5.5  |
| PS wasm     | 13.67 | 0.04 | 187.64 | 13.7 |
| o1js wasm   | 15.92 | 0.03 | 157.65 | 9.9  |

o1js is 1.66× slower than PS native, 1.16× slower wasm.

<p align="center">
<img src="profiles/cores-native-prove.png" width="700" alt="cores during prove — native" /><br/>
<sub>Cores in use during prove (native, trial-averaged).</sub>
</p>

<p align="center">
<img src="profiles/cores-wasm-prove.png" width="700" alt="cores during prove — wasm" /><br/>
<sub>Cores in use during prove (wasm, trial-averaged).</sub>
</p>

<p align="center">
<img src="profiles/rss-native-prove.png" width="700" alt="RSS during prove — native" /><br/>
<sub>Resident memory during prove (native, trial-averaged).</sub>
</p>

<p align="center">
<img src="profiles/rss-wasm-prove.png" width="700" alt="RSS during prove — wasm" /><br/>
<sub>Resident memory during prove (wasm, trial-averaged).</sub>
</p>

## Setup

From the repo root:

```sh
npm install                              # root deps + native kimchi-napi
npm run build:wasm -w kimchi-napi        # wasm binding (for --wasm)
make fetch-srs && make gen-linearization # SRS + pickles codegen
cd bench/o1js && npm install && cd ../.. # o1js deps
```

Profiling tooling: [`tools/profile/`](../tools/profile/README.md).
