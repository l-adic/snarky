# Follow-ups

Tracked items for future work. Each item has a tag for searchability (grep for `TODO(<tag>)` in source).

## Instrumentation cleanup

The byte-identity convergence work left a lot of debug scaffolding
sprinkled through the codebase. Things to tidy now that the core
proofs work:

- **Concentrate `unsafePerformEffect (Trace.*)` in one helper.** There
  are ~10+ sites in `pickles/src/` of the form
  `let _ = unsafePerformEffect (Trace.fieldF "lbl" val)` in pure code.
  Add `Pickles.Trace.unsafeField :: String -> f -> Unit` (and siblings
  for `int` / `string`) that perform the effect inside; call sites then
  just call the helper, concentrating the unsafety in one module.
- **Unify debug switches.** Today we have three independent knobs:
  `PICKLES_TRACE_FILE` (trace emission), `KIMCHI_WITNESS_DUMP`
  (kimchi-stubs witness dump), and `ctx.debug` (post-solve
  `verifyProverIndex` + row-label dump). Consider a top-level
  `PICKLES_DEBUG=1` that implies the last two at default-test
  configuration; trace-file stays orthogonal (it's byte-identity
  output, separate concern).
- **`ctx.debug` default from env.** Every test-setup currently hardcodes
  `debug: true`. A helper that reads `PICKLES_DEBUG` from env and
  populates the field would remove the repetition and let CI disable
  the check when not needed.
- **Env-driven row-label dump path.** Currently hardcoded
  `/tmp/ps_{step,wrap}_row_labels.txt`. A `PICKLES_ROW_LABELS_DIR` env
  var (default `/tmp/`) would let multiple test runs coexist and CI
  collect them as artifacts.
- **Strip most `Trace.*` call sites from production code.** The ~660
  trace lines in `pickles/src/` were there to pinpoint the first
  divergence from OCaml during convergence. Now that the circuits
  are stable, most of them can go. Keep a skeletal set at phase
  boundaries (FOP entry/exit, IVP entry/exit, etc.). The files most
  affected: `Pickles.IPA`, `Pickles.Verify`, `Pickles.Verify.FqSpongeTranscript`,
  `Pickles.Step.MessageHash`.
- **Squash the mina submodule WIP commits.** The submodule is at a
  `step-wrap-ml`-era branch with 10+ WIP commits mixing real fixes
  with instrumentation. Rebase into ≤3 clearly-named commits:
  (a) `pickles_trace.ml` infrastructure, (b) dump executables under
  `dump_*/`, (c) inline trace points that need to go once we're done
  with byte-identity. Then (c) can be dropped before upstreaming.

## Multi-chunk commitments — `TODO(num_chunks)`

When `num_chunks > 1` (circuits exceeding SRS polynomial degree), each polynomial commitment becomes an array of chunk points rather than a single curve point.

Affected locations:
- `StepVK` type (`VerificationKey.purs`): each field becomes `Vector numChunks (AffinePoint f)`
- `chooseKey` operations: `scalePt`, `sealPt`, `addPt` need to map over chunks
- `FqSpongeInput` (`FqSpongeTranscript.purs`): wComm/zComm/tComm need chunking
- `allBases` assembly (`Verify.purs`): totalBases scales by numChunks
- `combinePolynomials` (`IPA.purs`): needs inner loops over chunks (see OCaml `Pcs_batch.combine_split_commitments`)

Currently `num_chunks = 1` is correct for all Mina circuits. This would only matter for very large circuits exceeding the SRS degree bound.

## FOP domain as separate argument

`wrapFinalizeOtherProofCircuit` currently receives the per-proof domain merged into static params via `Record.merge` (see `Pickles.Wrap.Main:249`). Cleaner to separate static params (endo, srsLengthLog2, linearizationPoly) from per-proof domain (generator, shifts, vanishingPolynomial) as distinct arguments.

## Abstract ones_vector

The `ones_vector` logic in `WrapMain.purs` (block1) computes the `actual_proofs_verified_mask` inline. This mirrors OCaml's `Util.Wrap.ones_vector`. For the general N case (not just N1), this should be extracted as a reusable function, likely in `Pickles.Pseudo` or a utilities module. A second inline copy lives in `Pickles.Prove.Step.purs:packedBranchData` (the mask → `[F,F]`/`[F,T]`/`[T,T]` / packed-int encoding). Both should share one implementation.

## On-the-fly Lagrange commitments for x_hat — `TODO(lagrange_on_the_fly)`

Currently `publicInputCommit` (in `Pickles.PublicInputCommit`) takes a precomputed `Array (LagrangeBase f)` as part of its params record and runs an MSM over it (`scalarMuls params.curveParams input params.lagrangeComms`). The array is precomputed externally by test/orchestration code via the FFI `pallas_srs_lagrange_commitments` / `vesta_srs_lagrange_commitments`, which takes `(srs, domain_log2, count)` and returns all commitments up to `count`.

This diverges from OCaml, which does not precompute the array. In `step_verifier.incrementally_verify_proof` (`mina/src/lib/crypto/pickles/step_verifier.ml:554-568`), x_hat is computed with `lagrange_commitment ~domain srs i` called lazily per index while mapping the public input. Same in `wrap_verifier`. Under the hood, `srs.get_lagrange_basis(domain)` in kimchi/proof-systems caches the basis on the SRS object, so per-index lookups are O(1) after the first call.

**When this becomes important:** cross-system recursion. A step circuit verifying wrap proofs from multiple distinct predecessor systems needs Lagrange commitments pinned to each predecessor's wrap domain. Threading a single precomputed array stops being enough — you'd need either a collection of arrays indexed by predecessor system, or (cleaner) an SRS handle from which each verification site derives its own per-domain commitments on-the-fly.

**Change needed:**

1. **Rust-side FFI** (`packages/crypto-provider/src/kimchi/circuit.rs`): add a per-index access function alongside the existing `srs_lagrange_commitments`:
   ```rust
   pub fn srs_lagrange_commitment_at<G>(
       srs: &SRS<G>,
       domain_log2: u32,
       index: usize,
   ) -> (G::BaseField, G::BaseField) {
       let domain = D::<G::ScalarField>::new(1 << domain_log2).unwrap();
       let lgr_comm = srs.get_lagrange_basis(domain);  // cached
       let pt = lgr_comm[index].chunks.first().unwrap();
       pt.to_coordinates().unwrap()
   }
   ```
   Plus napi wrappers (`pallas_srs_lagrange_commitment_at` / `vesta_srs_lagrange_commitment_at`).

2. **PS FFI bindings**: add the new functions to wherever `vestaSrsLagrangeCommitments` / `pallasSrsLagrangeCommitments` are exposed.

3. **`Pickles.PublicInputCommit.publicInputCommit`** (`packages/pickles/src/Pickles/PublicInputCommit.purs:338-352`): change the params record to take an SRS handle + domain log2 instead of a precomputed `Array (LagrangeBase f)`. The body currently calls `scalarMuls params.curveParams input params.lagrangeComms` — this becomes something like "for each index, look up the Lagrange basis at this domain, accumulate into the MSM."

4. **`Pickles.Verify.IncrementallyVerifyProofParams`** (`packages/pickles/src/Pickles/Verify.purs:61-70`): replace `lagrangeComms :: Array (LagrangeBase f)` with whatever handle publicInputCommit ends up taking.

5. **`Pickles.Step.Main.stepMain`** and **`Pickles.Wrap.Main.wrapMain`**: update their parameter records accordingly. `StepMainSrsData` in `Pickles.Step.Main` currently holds `{ lagrangeComms, blindingH }`; would become `{ srs, domainLog2, blindingH }` or similar.

6. **Test orchestration** (`pickles-circuit-diffs`, etc.): drop the `vestaSrsLagrangeCommitments stepMainSrs 14 286` precomputation at the test call sites — just pass the SRS handle directly.

**Gotcha**: the MSM inside `publicInputCommit` runs in the Snarky monad (because it's building constraints). Per-index Lagrange lookups happen at Snarky compile time (not prove time) — they're pure constants pulled from the SRS cache. So `publicInputCommit` would need to do the lookups outside the Snarky-allocating loop (e.g., precompute into a local array at the top of the function from the SRS handle). That's not an implementation blocker, just a detail.

**Location summary**: the "point of change" is the `publicInputCommit` function in `Pickles.PublicInputCommit`. Every other change is upstream plumbing (params through `Verify.purs`, `stepMain`, `wrapMain`, test setup). The x_hat computation itself — the MSM — doesn't change conceptually; only how the Lagrange bases get sourced.
