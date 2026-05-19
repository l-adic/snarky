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

## Progress tracker

The eval-extractor widening (FFI-1) is being done one function per
commit. Each commit is structurally chunk-aware in Rust but leaves the
JS shim + PS binding chunk-blind by design — at n=1 byte-equivalence
holds because the loop iterates once. The JS/PS widening is deferred
to a single coordinated commit that updates all extractors together.

### Per-extractor status

| Function | Rust widened | JS shim chunk-aware | PS binding chunk-aware | Commits |
|---|---|---|---|---|
| `proof_z_evals` | ✓ | ✓ (`chunksToPointEvals`) | ✓ (returns `NonEmptyArray (PointEval f)`) | 9dd4b29f + sweep |
| `proof_witness_evals` | ✓ | ✓ (`polyChunksToPointEvals(_, 15)`) | ✓ (returns `Vector 15 (NonEmptyArray (PointEval f))`) | c89edba1 + sweep |
| `proof_sigma_evals` | ✓ | ✓ (`polyChunksToPointEvals(_, 6)`) | ✓ (returns `Vector 6 (NonEmptyArray (PointEval f))`) | 30feb8dc + sweep |
| `proof_coefficient_evals` | ✓ | ✓ (`polyChunksToPointEvals(_, 15)`) | ✓ (returns `Vector 15 (NonEmptyArray (PointEval f))`) | c8eb8785 + sweep |
| `proof_index_evals` | ✓ | ✓ (`polyChunksToPointEvals(_, 6)`) | ✓ (returns `Vector 6 (NonEmptyArray (PointEval f))`) | 6e3799bb + sweep |
| `oracles` `public_evals[0/1]` | ✓ (chunks inline; tail offset derived) | ✓ (`unpackOracles`) | ✓ (`publicEvals :: NonEmptyArray (PointEval f)`) | oracles-sweep |

The JS+PS sweep uses `NonEmptyArray` from `Data.Array.NonEmpty` to
encode the non-emptiness invariant (kimchi always emits ≥1 chunk per
polynomial). Conversion happens in the JS shim, which validates
non-empty at the boundary and throws on violation. PS-side `firstChunk`
extracts the first chunk via `NonEmptyArray.head` (total). The newtype
representation of `NonEmptyArray a = NonEmptyArray (Array a)` ensures
zero runtime cost at the FFI boundary.

The downstream PS shape (`PlonkChecks.PointEval f` / `Linearization.FFI.PointEval f`)
is **NOT** chunk-aware — `firstChunk` discards chunks > 0 silently.
At n=1 this is byte-identical (only one chunk). At n>1 the discard
breaks every proof's combined-eval computation; the downstream
widening to `actualEvaluation`-Horner-combine is Phase 2/3 of
`docs/chunking.md`.

### How `oracles` public_evals was widened (RESOLVED)

Layout after the widening (length `14 + 2n`):
  * positions 0..8 — `alpha, beta, gamma, zeta, ft_eval0, v, u, cip, ft_eval1`
  * positions 9..9+2n-1 — interleaved `[pez[0], pezo[0], pez[1], pezo[1], ..., pez[n-1], pezo[n-1]]`
  * positions 9+2n..9+2n+4 — `fq_digest, alpha_chal, zeta_chal, v_chal, u_chal`

At n=1 length is 16 with `fq_digest` at position 11 — byte-identical
to the pre-chunking layout. JS shim derives n from total length
(`n = (length - 14) / 2`) and reads tail fields at `tailStart = 9 + 2n`.

The earlier concern that this requires offset-shifting and breaks the
JS shim was real but tractable: deriving n once and reading positions
relative to `tailStart` is a few extra lines in the JS shim. The
"append at end" alternative we considered first preserved fixed
positions 0..15 verbatim but at the cost of a weirder layout.

### Original obstacle (now resolved)

Unlike the 5 eval extractors above, the `oracles` function packs many
oracle outputs into a single flat `Vec<F>` of length 16 (alpha, beta,
gamma, zeta, ft_eval0, v, u, combined_inner_product, ft_eval1,
public_eval_zeta, public_eval_zeta_omega, digest, …4 raw chals).
`public_eval_zeta` / `public_eval_zeta_omega` are at fixed positions 9
and 10.

Widening them to multi-chunk requires either:
* Shifting every downstream field's offset (positions 11+ would move
  by `2*(n-1)`) — silently breaks every PS-side caller that indexes
  by position.
* Splitting the return type into a struct — breaks the existing flat
  `Vec<F>` API.

Neither is "drop-in n=1 byte-equivalent" — n=1 returns 16 elements
unchanged in BOTH cases above, so a regression test wouldn't catch a
shift-introducing bug until n>1.

Right approach: pair this Rust change with the JS/PS coordinated
widening (deferred items 2 and 3 below). At that point we have the
opportunity to redesign the API (e.g., a typed struct) at the same
time we propagate chunk-aware shapes to PS.

### Deferred work (must land before n>1 can run)

1. **`oracles` `public_evals` widening** — done together with the
   JS/PS coordinated widening (item 2 below), not as a Rust-only step,
   because the existing flat `Vec<F>` packing prevents a drop-in n=1
   equivalent rewrite. See "Why `oracles` public_evals can't be
   Rust-only widened" above.
2. **JS shim chunk-awareness** — update `packages/pickles/src/Pickles/ProofFFI.js`:
   * `pallas/vestaProofZEvals` — read all `2n` elements as `Array<PointEval>`
   * `pallas/vestaProofWitnessEvals` — group flat `30n` array into 15
     polynomials × n chunks each (NOT chunk-blind `pairEvals`)
   * `pallas/vestaProofSigmaEvals` — same shape (6 polynomials × n chunks)
   * `pallas/vestaProofCoefficientEvals` — same shape (15 × n)
   * `pallas/vestaProofIndexEvals` — same shape (6 selectors × n)
3. **PS binding type widening** in `packages/pickles/src/Pickles/ProofFFI.purs`:
   * Choose the chunk-aware shape — likely `PointEval (Vector n a)` per
     the `docs/chunking.md` Phase 3 plan, NOT `Array (PointEval a)`,
     because the OCaml-side type is `'a PointEvaluations` where `'a`
     becomes the chunked-vector type at n>1.
   * Cascade through all 4 PS callers of `proofZEvals`,
     `proofWitnessEvals`, etc. (Prove/Step.purs, Prove/Compile.purs).
4. **`ProofCommitments` chunk-awareness** — separate from the eval
   extractors. `ProofCommitments.wComm` / `zComm` shape widening; the
   Rust side already returns chunked w-/z-comm arrays of length
   `15n` / `n` (proof_commitments at circuit.rs:842 iterates
   `w.chunks`). PS-side type and JS-side parsing both need updates.
5. **Oracles `public_evals` widening** — Rust + JS + PS. The output is
   currently packed into the same flat vec as alpha/beta/gamma/zeta,
   so widening shifts every downstream offset.
6. **End-to-end smoke test at n=2** — use `dump_chunks2.exe` fixtures
   to drive a chunked-proof verify path through the FFI. This is the
   "FFI-4" verification step.

### Why this approach (not vertical-slice-per-function)

Per-function vertical slice (Rust + JS + PS at once) would require
deciding the chunk-aware PS shape NOW and migrating each function's
callers. The chunked `PointEval` shape isn't free to choose — it
should mirror the OCaml-side `'a PointEvaluations` parameterization
(Phase 3 of `docs/chunking.md`). Locking that in across all 5
extractors at once is cheaper than choosing it once-per-function and
maybe revising later. Hence Rust-only steps preserve optionality.

