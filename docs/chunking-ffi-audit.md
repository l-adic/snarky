# Chunking FFI Audit — what breaks at `num_chunks > 1`

Audit performed before threading `NumChunks` through PureScript (Phase 1
of `docs/chunking.md`). Files referenced: `packages/crypto-provider/src/kimchi/circuit.rs`,
`packages/pickles/src/Pickles/ProofFFI.purs`, `packages/crypto-provider/index.d.ts`.

## Confirmed blockers (must fix before any PS chunking work)

### 1. Per-proof eval extractors hardcode `[0]` — drop all chunks > 0

`proof.evals.{w, z, coefficients, s, *_selector}` are kimchi-side
`PointEvaluations<Vec<F>>`. The `zeta` / `zeta_omega` fields are `Vec<F>`
of length `num_chunks`. Our FFI takes `[0]` and discards the rest.

| Function (Rust) | Hardcoded site | At `n>1` |
|---|---|---|
| `proof_witness_evals` (circuit.rs:363) | `w_eval.zeta[0]`, `w_eval.zeta_omega[0]` | drops 15 cols × 2 pts × (n-1) chunks |
| `proof_z_evals` (circuit.rs:379) | `proof.evals.z.zeta[0]`, `…zeta_omega[0]` | drops 1 col × 2 pts × (n-1) |
| `proof_sigma_evals` (circuit.rs:390) | `s_eval.zeta[0]`, `s_eval.zeta_omega[0]` | drops 6 cols × 2 pts × (n-1) |
| `proof_coefficient_evals` (circuit.rs:406) | `c_eval.zeta[0]`, `c_eval.zeta_omega[0]` | drops 15 cols × 2 pts × (n-1) |
| `proof_index_evals` (circuit.rs:423) | `e.{generic,poseidon,…}_selector.zeta[0]`, `…zeta_omega[0]` | drops 6 selectors × 2 pts × (n-1) |
| `oracles` public-eval extraction (circuit.rs:549, 553) | `public_evals[0].first()`, `public_evals[1].first()` | drops public_evals chunks > 0 |

**Fix**: change return type from `Vec<F>` → `Vec<Vec<F>>` (chunk-major)
or `Vec<F>` of length `count * num_chunks * 2` (chunk-flat).

### 2. PS `ProofCommitments` hardcodes n=1 shape

`packages/pickles/src/Pickles/ProofFFI.purs:414`:

```purescript
type ProofCommitments f =
  { wComm :: Vector 15 (AffinePoint f)
  , zComm :: AffinePoint f
  , tComm :: Array (AffinePoint f)
  }
```

The Rust side (`proof_commitments` at circuit.rs:842) ALREADY iterates
`w.chunks` correctly — at `n=2` it returns 15×2=30 w_comm points and
1×2=2 z_comm points. The PS side then fails to parse:

* `wComm` should be `Vector 15 (Vector n (AffinePoint f))` or `Vector (15*n) (AffinePoint f)`
* `zComm` should be `Vector n (AffinePoint f)`
* `tComm` is already `Array` (variable length) — handles `7*n` natively

Plus `tCommVec` at ProofFFI.purs:600 hard-asserts `Vector 7` — will
crash at `n>1` even though the underlying Array is correctly sized.

## Not blockers (already chunk-aware or don't need chunking)

| Function | Status | Note |
|---|---|---|
| `proof_commitments` (Rust) | OK | iterates `w.chunks` correctly per polynomial |
| `verifier_index_sigma_comm_last` | OK | VK commitments aren't chunked; `chunks.first()` is the only chunk |
| `verifier_index_column_comms` | OK | same — VK comms have a single chunk by setup |
| `verify_opening_proof` | OK | delegates entirely to kimchi `batch_verify`, chunk-aware internally |
| `create_proof` / `create_proof_with_prev` | OK | kimchi derives chunks from `domain_size / max_poly_size`; no caller-side `num_chunks` |
| `pallas_proof_opening_{lr,delta,sg,z1,z2}` | OK | IPA opening proof is over the combined polynomial, not per-chunk |
| `pallas_proof_opening_prechallenges` | OK | IPA prechallenges; not chunked |

## Recommended fix sequence

**FFI-1** — Widen the 5 eval extractors to chunk-aware return type.
Option A (recommended): return `Vec<Vec<F>>` (outer = polynomial index,
inner = per-chunk eval at zeta then zeta_omega). Update `index.d.ts`,
PS `ProofFFI`, all PS callers in one sweep. Default at `n=1` is each
inner Vec has length 2 — current callers can keep their single-chunk
flatten until widening to PointEval (Phase 3).

**FFI-2** — Widen oracles `public_eval_zeta` / `public_eval_zeta_omega`
return shape to chunk-aware (`Vec<Vec<F>>` of `[publicEvals[0], publicEvals[1]]`).

**FFI-3** — Widen PS `ProofCommitments`:
* `wComm :: Vector 15 (Vector NumChunks (AffinePoint f))`
* `zComm :: Vector NumChunks (AffinePoint f)`
* `tComm :: Vector (7 * NumChunks) (AffinePoint f)` — replaces `tCommVec` helper
* Marshalling layer (TS `.d.ts` types) need updates if it parses these per-field.

**FFI-4** — Confirm `pallas_proof_commitments` returns chunks in the
expected order (intra-polynomial first vs inter-polynomial first). Rust
code reads as polynomial-major (all chunks of w[0], then w[1], ..., w[14],
then all chunks of z, then all chunks of t). PS callers need to match.

## Why this matters before Phase 1

Phase 1 from the original `docs/chunking.md` (thread `NumChunks` type
parameter, default 1) is structurally safe because at `n=1` the FFI's
hardcoded `[0]` happens to be the only chunk. But the moment we try to
instantiate at `n=2` (Phase 4), every prove/verify path will:

1. Crash on `Vector.toVector @15` for `wComm` (length mismatch)
2. Silently drop chunks > 0 of every eval, producing oracles based on
   only the 1st chunk → wrong sponge state → byte divergence from gate 0
3. Same for `public_evals` in oracle reconstruction

In other words, Phase 1's type widening is necessary but not sufficient.
FFI-1/2/3 above are pre-requisites that should land BEFORE Phase 1, or
the Phase 1 acceptance test (n=1 still byte-identical) provides a false
sense of security for the n>1 work that follows.

## Suggested ordering

1. **FFI-1 + FFI-2** — Rust changes; widen 5+1 functions to chunk-aware
   shapes. PS callers consume `.[0]` at the call site for now (preserves
   n=1 byte-equivalence). All existing witness diffs must still pass.
2. **FFI-3** — PS `ProofCommitments` shape widened to `Vector n`. At n=1
   `Vector 1` collapses to a single element accessed via `Vector.head`.
3. **FFI-4** (verification step) — generate a debug-only chunked
   fixture (e.g. via a test that creates a tiny chunked proof) and
   confirm the FFI output structure end-to-end before any further PS
   work.

After FFI 1-4, the original Phase 1 (`NumChunks` type-level threading)
can land cleanly without lurking shape mismatches.
