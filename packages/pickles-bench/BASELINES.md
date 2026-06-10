# pickles-bench baseline — current MTL/transformer stack

- date: 2026-05-30T17:23Z
- git HEAD: `ee4239c2` (+ uncommitted additive `MonadTrans (StepProverT…)`, perf-neutral for benched paths)
- node v23.11.1, `node --trace-gc packages/pickles-bench/run.mjs` (both groups)
- raw log: `baseline-current-stack-2026-05-30.log` (30,756 lines; full --trace-gc)
- workload unit: N=2 tree, step domain log2 = 16 (one recursive prove / one full NRR+tree compile)

## Compile group (3 iters)
- **avg 32.17 s / compile** (count=3)
- Rust FFI ≈ 9.0 s (~28%)  → JS-side ≈ 23 s (~72%)
- Rust hotspots: `fp/fq_plonk_index_create` (~5.2 s), `fp/fq_plonk_gate_vector_add` (~1.35 s over 74.8k calls), `b_poly_commitment` (~1.7 s)

## Prove group — b1 recursive prove (compile + b0 untimed) — THE hot path
- **mean 43.82 s / prove** (3 timed trials, stddev 205 ms = 1.1% — very stable)
- **Split: JS-side ≈ 35.5 s (~81%)  |  Rust FFI ≈ 8.3 s (~19%)**  (from `[prove split]` lines)
- Rust hotspot: `fp/fq_plonk_proof_create` (~8.2 s of the ~8.3 s Rust) — i.e. essentially ALL Rust time is the final proof creation; everything else in the prove is JS.
- **Allocation (ground truth = Σ(before−after) over Scavenges, windowed per prove):**
  - **≈ 40 GB reclaimed per prove** (39.9–40.7 GB across 6 windows), ≈ **0.9 GB/s** churn
  - ≈ 2,470 Scavenges + 5 Mark-Compacts per prove
  - (FfiTimer's own "Total Garbage Collected: 0.00 MB" counter is the known-broken inspector counter — ignore it; trace-gc is authoritative)
- whole-run total: 480 GB reclaimed across 30,460 GCs

## Implication for the Run-rewrite question
The prove hot path is **~81% JS and already allocation-bound** (~40 GB churned per 44 s prove). `purescript-run` is a free monad: it allocates a `Free`/`VariantF` node per bind — i.e. it *increases* per-bind allocation, the exact axis already saturated here. A wholesale Run port of the witness-gen core would very likely push prove time **up**, opposite the direction the project wants (the standing perf idea is mutable-state-over-`Effect` to *cut* the 40 GB).
- Conclusion: Run is contraindicated for the arithmetic/witness hot loop. It remains a good fit for the low-frequency **advice/request layer** only (a hybrid), but that hybrid's complexity must be weighed against just solving the advice-orphan problem with the transparent-stack + mtl-instances approach (no hot-path cost).
