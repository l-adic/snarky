# Plan: full chunking (`nc > 1`) for the kimchi formalization

**Status:** EXECUTING. Phase 0 DONE — `kimchi_proof_{vesta,pallas}_nc2.json` recorded
(`kimchi_proof_dump_nc2`, both accepted by the production verifier; `n = 32`,
`max_poly_size = 16`, `zk_rows = 5`, `t` = 14 chunks; the regenerated one-chunk fixture
stayed byte-identical, so the genericized circuit preserves the rng draw order).

**Phase 1 DONE (executable verifier)** — as a TRANSITIONAL parallel module
(`Kimchi/Verifier/Chunked.lean` + `KimchiFixture/Chunked.lean`), NOT the in-place
record generalization the plan sketched: the wire records are bound by `Reflect.lean`
and the capstones, so changing them in place cannot land green before Phases 2–4. The
`nc = 1` verifier and its whole soundness chain stay untouched; the chunked verifier is
adjudicated NOW (accepts both `nc = 2` fixtures AND the one-chunk fixture through
singleton-chunk decoding), and Phases 2–4 migrate the reduction/terminals onto it, after
which the `nc = 1` verifier dissolves and `Chunked` is renamed into place. Declared as a
temporary root in `roots.txt`.

The fixtures exposed TWO LATENT `zkRows = 3`/Vesta-only transcription bugs, both fixed
(they were invisible to every prior fixture; the chunked fixtures changed `zk_rows` to 5
and added the first-ever Pallas wire adjudication):

1. **zkpm window** — `Permutation.zkpm`/`Linearization.zkpmEval` transcribed
   `vanishes_on_last_n_rows` (the full `∏_{[n−zk, n)}` window), but production's
   permutation argument uses the THREE-factor
   `permutation_vanishing_polynomial = (X−ω^{n−zk})(X−ω^{n−zk+1})(X−ω^{n−1})`
   (permutation.rs:105–121); they coincide exactly at `zkRows = 3`. Ripple: recurrence
   rows are now the complement of the three roots (production's `perm_aggreg` randomizes
   exactly `z[n−zk+1]`, `z[n−zk+2]` and folds through the mask interior), so
   completeness rebuilds the accumulator with a restarted tail, `Nondegenerate`
   quantifies ALL rows, and `Index.zk_pos` strengthens to `zk_three : 3 ≤ zkRows`
   (production's `(16·nc+5)/7 ≥ 3`).
2. **Poseidon MDS** — `Gate.Poseidon` hard-coded the `fp_kimchi` MDS as generic
   integer literals; production evaluates the gate with `G::sponge_params().mds`, a
   different table per curve. The gate is now parameterized by `Mds F` (the `EndoMul`
   `endo` pattern), `Index` carries `mds` as data, the verifiers pass
   `mdsOfParams vk.frParams` (production's `Constants.mds`), and `KimchiVK.Corresponds`
   pins it. Without this fix the Pallas capstone terminals described a verifier that
   diverges from deployed Pallas kimchi.

**Phase 2 DONE (chunked reduction)** — `Kimchi/Verifier/Reduction/Chunked.lean`
(transitional parallel module, namespace `Kimchi.Verifier.Chunked`, roots
`kimchiProof_sound{,_of_openings}` in check_axioms/roots.txt): the composed soundness
at `nc · 2^σ.k = n`, extraction via `chunked_batch_soundness` DIRECTLY (the
`batch_openings_nc1` wrapper has no chunked analogue — dissolved as planned). Two
deviations/discoveries recorded:

* **44 rows, not 43** — the public row JOINS the batch. At `nc = 1` the public
  evaluations are verifier-computed (a barycentric identity, no binding needed; the row
  was rightly omitted). At `nc > 1` they are PROOF-CARRIED adversarial data whose only
  tie to the public input is the batched opening against the verifier-computed public
  commitment: the reduction takes the public commitment chunks with their
  correspondence to `-(idx.pubPoly pub)` (per-chunk unit blinder, the all-ones
  `mask_custom`) and pins the carried claims through binding. `ft_eval0`'s public slot
  reads the chunk-COMBINED carried claim (`claimedPub`), not the interpolant value —
  equality is DERIVED, not assumed.
* `chunked_batch_soundness` (and `ipa{Vesta,Pallas}_sound`) STRENGTHENED: the
  conclusion now also exposes the per-chunk claim reproduction
  (`e i c j = ⟨chunkCoeffs (q i) c, evalVector x⟩`), which the proof always had
  (`hEseg`) but did not state — the chunked reduction pins per-chunk VK-row claims
  against fixed chunk commitments and cannot re-derive them from the combined
  identity. The one bulletproof-pcs change of the arc (a pure statement
  strengthening).

The explicit witness is the ASSEMBLED reference data:
`extractTable idx.omega (fun col => assembledRow σ.k nc (aw₀ (wRow col)))`, degree
`< n` feeding `Kimchi.Protocol.sound` unchanged.

**Phase 3 DONE (chunked capstones)** — `Capstone/{StandardChunked,AlgebraicChunked}.lean`
(transitional parallel modules): the grid capstones `Chunked.kimchi{Vesta,Pallas}_sound`
at the deployed Pasta verifiers (grid nodes over the FLAT segment stream, per-node
`poseidon_fiat_shamir_*` transported through the `_eq_flat` combiners), and the AGM
corollary + residue-free algebraic quotient `Chunked.kimchiProof_sound_algebraic{,_ft}`
(eval pins at the flat segment family; `ftChunkAssembly` at `nt ≤ 7·nc` chunks;
`ft_identity_of_chunks` with the σ₆-side collapse — the `nc`-chunk σ₆ commitment
combined at `ζ^{2^σ.k}`, real algebra at `nc > 1`). Run-level corollaries move to
Phase 4 (they bind the chunked verifier's `runOracles`). GOTCHA recorded: structures
(NOT theorem binders) indexed by `Fin (∑ _ : Fin 44, nc)` send the elaborator into a
`whnf` spiral — the multiplied form `segTotal nc = 44 * nc` is definitionally stuck and
fast; `segTotal_eq_sum`/`flatSeg` bridge to the sigma-summed world of
`chunked_batch_soundness`, and every transport must be PROPOSITIONAL (never let
unification compare the two forms).

**Phase 4a DONE (chunked reflection)** — `Verifier/ReflectChunked.lean`: the run
functions (`runOracles`…`runLogical`/`flatRows`/`runInput`) and
`Chunked.kimchiVerify_reflects`. DESIGN: the verifier's 30-clause guard is now the
named `shapeBad` (behavior-neutral, fixture-re-adjudicated) and `ReflectedRun` carries
`shapeBad = false` as ONE fact + the warm acceptance — `runInput`'s columns are
`flatRows (runLogical …)` projections BY DEFINITION, so no content equalities needed;
downstream reads rows off `runLogical`'s literal structure, extracting shapes from
`shapeBad = false` on demand.

**Phase 4b DONE (standard-model run corollaries)** —
`Chunked.kimchi{Vesta,Pallas}_run_sound` in `StandardChunked.lean`: the grid capstones
instantiated at the chunked run's own `Chunked.runOracles` challenges over the run's
wire commitment chunks; quotient residue stays the one undischarged antecedent
(48 axiom roots, same allowed set).

**Phase 4b'** — `check_vk_correspond_chunked` GREEN (the chunked indexer adjudicated:
per-chunk value-MSM against the Lagrange chunk commitments, selectors per-chunk
masked), and it exposed **LATENT BUG #3** (same zk=3-blind class): production ZEROES
the σ columns on the interior mask rows `[n − zk_rows + 2, n − 1)`
(constraints.rs:538–544, "quasi-random aggregation") — an EMPTY range at `zk_rows = 3`.
The Lean `Index.sigmaPoly` still interpolates identity addresses there; the model fix
(σ zeroing in the Index wiring semantics, rippling through the permutation argument's
σ-side factors on the live interior-mask recurrence rows, `Nondegenerate`, and the
correspondence) belongs to Phase 4c. The script applies the zeroing itself and
documents the divergence.

**Phase 4c (σ-zeroing) DONE** — `Index.sigmaAddrRow` / `Permutation.sigmaCell` now
zero the committed σ cells on `[n − zkRows + 2, n − 1)`; `Nondegenerate` and the
completeness identities quantify the COMMITTED cell values; `sigmaPoly_eq_wiring`
stays definitional; copy soundness reads the unmasked region through
`sigmaCell_unmasked`. All fixture drivers green (the `zk = 3` fixtures are unaffected —
the range is empty there — and `check_vk_correspond_chunked` adjudicates the `zk = 5`
semantics).

**Phase 4d part 1 DONE (chunked FS axioms + ft opening)** —
`Capstone/ReflectionChunked.lean`: `Chunked.kimchi_fiat_shamir_{vesta,pallas}` restate
the deployed-run FS assumption at the chunked transcript (the flat segment stream via
`Chunked.runWarm`/`Chunked.runInput`; statement shape mirrors the audited `nc = 1` pair
verbatim at the chunked types — wire data only, sponge-validity claim only), and
`ft_opening_of_reflected{,_vesta,_pallas}` derive the ft opening from ONE genuine
chunked acceptance: the ft row sits at flat position `nc` (after the public row's
chunks), read off `flatRows (runLogical …)` by `flatRows_ft_read`. TRANSITIONAL: the
check_axioms ALLOWED set carries both FS pairs (6 names) until the sweep deletes the
`nc = 1` layer and restores 4.

**Phase 4d part 2 REMAINING** — the run-level `_ft` terminals: RESTATED
`kimchi_fiat_shamir_{vesta,pallas}` at the chunked transcript (trust-surface re-audit,
host-audit discipline; anchored on `Ipa.verifyFrom (runWarm) (runInput)` with the
chunked runInput), the chunked `runReindex` (44-row×nc batch + ft row + t chunks →
`runLogical` flat positions) + read lemmas, `ft_opening_of_reflected*`, both
`kimchi{V,P}_run_sound_algebraic_ft` terminals, `check_vk_correspond` generalization
(chunked indexer vs the nc=2 VK fixture incl. lagrangeBasis→public-commitment), and
THE DELETION SWEEP: the nc=1 verifier + reduction + capstones + Reflect deleted,
`Chunked` renamed into place — `nc = 1` survives nowhere as a pin (user directive).

**Phase 5 REMAINING** — roots.txt/check_axioms consolidation after the sweep, module
docstrings, docs/module-deps regeneration, memory/ledger updates.
**Branch discipline:** new branch off `main`; ALWAYS `git branch --show-current` before
committing.

## Goal

Generalize the kimchi development from the pinned `max_poly_size = n` regime (`nc = 1`,
the guard `2 ^ σ.k = n`) to the production chunked regime: domain size
`n = nc · max_poly_size`, every degree-`< n` polynomial committed in `nc` SRS-width
chunks, exactly as proof-systems implements it (`chunk_size = domain.size /
max_poly_size`, verifier.rs:145–152). Endpoint mirrors the current one: the executable
verifier accepts a production `nc = 2` fixture, and the run-level soundness roots hold at
the chunked wire.

## Where chunking lives (measured)

`grep 'σ.k' Kimchi/` hits ONLY `Kimchi/Verifier/**`. The Gate, Permutation, Quotient,
Index, and **Protocol** layers never mention the SRS — the protocol/wire split put the
PCS-free boundary exactly where chunking stops. Consequently:

- **`Kimchi/Protocol/` (Accepts, sound, Equation, Linearization): ZERO changes.**
  `Protocol.sound` consumes witness polynomials of degree `< n` and an accumulator of
  degree `< n`; how they are committed is invisible. The scalar side (`ftEval0`,
  `permScalar`, `Evals`) consumes CHUNK-COMBINED evaluations, which is exactly what the
  production verifier feeds it (`evals.combine(&powers_of_eval_points_for_chunks)`,
  verifier.rs:409) — single values per column, at `nc = 1` and `nc > 1` alike.
- **`bulletproof-pcs`: ZERO expected changes — chunking is already solved there.**
  Inventory (all landed, all general):
  - `chunked_batch_soundness` (Soundness.lean:400): ragged chunk counts
    `nc : Fin n → ℕ`, concludes per-row assembled polynomials `q i` with
    `natDegree < nc i · 2^σ.k`, per-chunk commit pins, and the combined-eval identity
    `(q i).eval (x j) = ∑ c, ((x j)^{2^k})^c · e i c j`.
  - `chunkedCombinedCommitment` / `chunkedCombinedInnerProduct` (+ `_eq_flat`
    flattening lemmas): production's segment-offset `ξ`-powers.
  - Chunk windows: `chunkCoeffs`, `chunkPoly`, `chunkPoly_eval`,
    `eval_eq_sum_chunkPoly` (the `combine` identity), `assemblePoly` (+ coeff lemma) —
    the extractor's assembly tools.
  - Wire: `ipa{Vesta,Pallas}_sound` are stated *at the declared chunk structure*; the
    flat `Ipa.verify` consumes caller-flattened segment streams (`segmentStream`,
    Bulletproof/Reflection.lean:215).
- **Everything that changes is `Kimchi/Verifier/**` + `KimchiFixture` + fixtures**
  (~3.7k lines currently: Kimchi.lean 488, Reflect 417, Reduction/{Binding 144,
  Correspond 71, Soundness 509}, Capstone/{Standard 481, Algebraic 488, Reflection
  1042}, KimchiFixture 82).

## Production reference (verifier.rs, measured against the checkout at
`mina/src/lib/crypto/proof-systems`)

1. `chunk_size = if d1 < max_poly_size then 1 else d1 / max_poly_size` (:145–152);
   `powers_of_eval_points_for_chunks = (ζ^max_poly_size, (ζω)^max_poly_size)` (:305).
2. **Evaluation combination**: every column's chunked evals are combined once,
   `evals.combine(&powers_of_eval_points_for_chunks)` (:409); the whole scalar side
   (ft_eval0, perm scalar) runs on combined values. The public term in ft_eval0 is
   `eval_polynomial(&public_evals[0], ζ^max_poly_size)` (:441–443) — the chunk-combined
   public evaluation.
3. **Public input at `nc > 1`**: the proof MUST carry chunked public evaluations
   (`self.evals.public`; else `VerifyError::MissingPublicInputEvaluation`, :332–335).
   The barycentric computation from the raw public input exists ONLY at `nc = 1`. Both
   chunk vectors are fr-absorbed via `absorb_multiple` (:391–392).
4. **Public commitment**: empty input → `PolyComm::new(vec![blinding_commitment();
   chunk_size])` (`nc` copies of `srs.h`, :845); else the MSM over the (chunked)
   Lagrange-basis commitments, all-ones-masked per chunk (:848–856).
5. **ft commitment** (:960–965): `f_comm.chunk_commitment(ζ^max)` and
   `t_comm.chunk_commitment(ζ^max)` collapse to ONE point each;
   `ft_comm = chunked_f − (ζ^n − 1)·chunked_t`. `f_comm = pScalar · sigma_comm[6]` where
   `sigma_comm[6]` is itself an `nc`-chunk `PolyComm`. The ft batch row is single-chunk
   with evals `[[ft_eval0],[ft_eval1]]` (:984–987).
6. **Batch rows** (`to_batch`, :967–1071): same 45 logical rows in the same order
   (public, ft, z, 6 selectors, 15 w, 15 coeff, 6 σ), but each row's commitment is an
   `nc`-chunk `PolyComm` (ft: 1 chunk) with per-chunk eval vectors; the IPA's
   `combined_inner_product`/`combine_commitments` walk segments with `ξ`-powers at
   segment offsets (matching `chunkedCombined*` in bulletproof-pcs).
7. `t_comm` guard: `t_comm.len() > chunk_size * 7` rejects (:260–264) — quotient chunks
   ≤ `7·nc`.
8. **fq-sponge**: `absorb_commitment` absorbs every chunk of a `PolyComm` (so at
   `nc > 1` the witness/z/t absorbs lengthen; schedule order unchanged).
9. **zk_rows is nc-dependent** (constraints.rs:774–784: lower bound
   `(2·(PERMUTS+1)·nc − 2)/PERMUTS`, docstring `(16·nc + 5)/7`). No formal-side change —
   `Index`/`KimchiVK` carry `zkRows` as data — but the `nc = 2` fixture will exercise a
   different value.

## Design decisions

- **Uniform `nc` as an explicit parameter.** All 43 batch columns have degree `< n`, so
  one chunk count serves (production agrees: `chunk_size` is global). The reduction
  layer takes `nc : ℕ` with `hnc : 0 < nc` and the SRS pin generalizes
  `hk : 2 ^ σ.k = n` → `hk : nc * 2 ^ σ.k = n`. `nc = 1` must recover statements
  interderivable with today's (the regression sanity check). Ragged generality stays in
  bulletproof-pcs where it already lives; kimchi instantiates uniformly.
- **Wire types stay array-shaped**, mirroring `PolyComm`: a committed column is
  `Array C.Point` (its chunks), an evaluation is per-chunk
  (`PointEvaluations (Array F)` — `zeta : Array F`, `zetaOmega : Array F`), and
  `KimchiProof` gains the production `public : Option (PointEvaluations (Array F))`
  (required at `nc > 1`, guard-checked).
- **The seam stays 43 logical rows, chunked** — `batchC : Fin 43 → Fin nc → G` — and
  extraction consumes `chunked_batch_soundness` DIRECTLY. Today's `batch_openings_nc1`
  is a specialization wrapper that exists only because of the pin; at general `nc` the
  bulletproof conclusion (assembled `q i`, degree `< nc·2^k = n`, chunk pins,
  combined-eval identity) is exactly what the reduction needs, so the wrapper dissolves
  rather than generalizes.
- **The explicit witness stays.** `of_openings`' conclusion becomes
  `Satisfies idx pub (extractTable idx.omega fun col => assembled-polynomial-of-chunks)`
  (via `assemblePoly`/the extracted `q`); degree `< n` feeds `Protocol.sound` unchanged.

## Phases (each lands green: build, style, 40-root axiom gate with unchanged allowed
set, deadcode, fixture drivers)

### Phase 0 — the `nc = 2` fixture (data before formalization)

`tools/fixture-dump` already threads the knob:
`new_index_for_test_with_lookups_and_custom_srs` takes
`override_srs_size : Option<usize>` (prover_index.rs:165) and `mixed_index` passes
`None`. Add a chunked variant of `kimchi_proof_dump` (same mixed circuit, same seed)
with `override_srs_size = Some(n / 2)` → `max_poly_size = n/2`, `nc = 2`; drop the
`assert_eq!(chunks.len(), 1)` flatteners and dump chunk ARRAYS for commitments and
evals, plus `evals.public` (production carries it at `nc > 1`) and `max_poly_size`
(field already dumped). Also dump the Pallas twin. Verify the production verifier
accepts before dumping (the dumper already does). CAUTION (recorded lesson): dump from
the kimchi proof types directly — o1js-style `to_repr` serialization DROPS public-eval
chunks.

Deliverables: `fixtures/kimchi_proof_vesta_nc2.json` (+ pallas), dumper source. No Lean
changes yet.

### Phase 1 — the chunked executable verifier

`Verifier/Kimchi.lean` + `KimchiFixture/Kimchi.lean` + `scripts/check_kimchi_verifier`:

- Wire records per the design decisions; `KimchiVK` unchanged except the committed
  columns become chunk arrays and `lagrangeBasis` becomes per-basis chunk arrays.
- Guards: sizes per family; `nc * 2 ^ σ.k = vk.n` with `nc := vk.n / 2 ^ σ.k` (or carry
  `nc` and check consistency); `t_comm.size ≤ 7 * nc`; `public?.isSome` iff `nc > 1`
  (transcribe :332–335 exactly).
- `fqOracles`: absorb per-chunk (`absorb_commitment` = chunk fold — the schedule
  structure is unchanged, folds lengthen).
- `frOracles`: absorb the chunked public evals via the multi-element absorb; per-column
  chunk-vector absorbs in `absorb_evaluations` order.
- `linEvals` → `combine` at `ζ^max`/`(ζω)^max` (the `eval_eq_sum_chunkPoly` fold,
  computed with `powPow2`); `publicEvals` keeps the `nc = 1` barycentric branch and
  takes the proof-carried chunks at `nc > 1`, combining for ft_eval0.
- `publicCommitment`, `fComm` collapse, `ftComm`, and the row assembly: 45 logical rows
  → flat segment stream in `to_batch` order (each column's `nc` chunks consecutive; ft
  single). The flattening order MUST match `combined_inner_product`'s segment offsets —
  cross-checked by the fixture, adjudicated like everything else in this file.
- Decoders: chunk arrays, `public` evals, both fixtures.
- `check_kimchi_verifier` runs BOTH the `nc = 1` and `nc = 2` fixtures (accept +
  corruption rejections). The old fixture passing under the generalized verifier is the
  no-regression adjudication.

### Phase 2 — the chunked reduction

`Reduction/{Correspond,Binding,Soundness}.lean`:

- `IndexComms G` → chunk-indexed (`sigma : Fin 7 → Fin nc → G`, …); `indexerOf` commits
  the index polynomials per chunk window (`commitPoly σ (chunkPoly (2^σ.k) p c)`;
  masked selectors per-chunk unit blinder — mirror production's per-chunk mask).
  `VKCorresponds` shape unchanged.
- `Binding`: per-chunk `bound_eval_of_commitPoly[Masked]`; cross-point uniqueness per
  chunk; an assembled-row lemma (`rowPoly` of chunks → `assemblePoly`, degree `< n`).
- `Soundness`: `batchC : Fin 43 → Fin nc → G`; drop `batch_openings_nc1`, consume
  `chunked_batch_soundness`; `claimedEvals` over per-chunk claims
  `E : Fin 43 → Fin nc → Fin 2 → F` producing the COMBINED record (via
  `eval_eq_sum_chunkPoly`); `claimedEvals_eq_evalsOf` per column;
  `kimchiProof_sound_of_openings` restated at chunked reference/consumer openings with
  the explicit assembled witness; `kimchiProof_sound` over chunked grids.
  `Kimchi.Protocol.sound` consumption is UNCHANGED.

### Phase 3 — the chunked capstones (Standard + Algebraic)

- `KimchiBatchAcc` grids at the chunked batch (flat segment streams of deployed
  `Ipa.verify` inputs); `kimchi{V,P}_sound` wrappers + run roots restated.
- AGM: representations per chunk (`aw₀ : Fin 43 → Fin nc → Fin (2^σ.k) → F` or the
  flattened equivalent — `eval_pins_of_opening` and `badXiOf`/`badROf` are ALREADY
  arity-generic over flat `Fin m`, so flattening is the cheap route);
  `ftChunkAssembly` is already width-parametric (7 chunks of width `2^k` → `7·nc`);
  `ft_identity_of_chunks` gains the σ₆-side chunk collapse (production :962: `f_comm`
  is chunk-collapsed too — at `nc = 1` this was the identity, now it is real).

### Phase 4 — chunked reflection + terminals

- `Reflect.lean`: `runInput` builds the flat chunked stream (45 logical rows →
  `43·nc + nc + 1` slots); `kimchiVerify_reflects` re-established; `runReindex`
  generalizes to the segment injection.
- `kimchi_fiat_shamir_{vesta,pallas}` RESTATED at the chunked transcript shape — a
  trust-surface change: re-audit the axiom statements with the same host-audit
  discipline as their introduction (independence criterion; the axiom must say only
  "the sponge's challenges behave as FS demands at this transcript shape").
- `ft_opening_of_reflected*` + the two `_ft` terminals at the chunked run;
  `KimchiVK.Corresponds` unchanged in shape (commitments now chunked through
  `KimchiVK.comms`).
- `check_vk_correspond` generalizes (chunked `indexerOf` vs the `nc = 2` VK fixture,
  value-MSM per chunk window).

### Phase 5 — gates + docs

`roots.txt` (comment updates only — root names unchanged), `check_axioms.lean`
(statements changed, same names, SAME allowed axiom set expected — the FS axioms are
restatements, not additions), module docstrings, `docs/module-deps` regeneration,
memory/ledger updates.

## Risks / open questions (resolve during execution, in this order)

1. **Fixture generation** (Phase 0): confirm `override_srs_size` produces a working
   chunked prover run on the mixed circuit (o1js-side `chunks2` work proves production
   supports `nc = 2` end-to-end; the test hook path specifically is unverified). Check
   whether `zk_rows` forces a larger domain for the mixed circuit at `nc = 2`.
2. **Segment-order fidelity** (Phase 1): the exact interleaving of chunk slots in the
   IPA input (`es` construction, verifier.rs:492–605) vs the Lean flattening — a
   one-fixture adjudication, but THE likely divergence point.
3. **`absorb_evaluations` chunk order** (Phase 1): per-column `ζ`-chunks then
   `ζω`-chunks vs interleaved — transcribe plonk_sponge.rs, adjudicate by fixture.
4. **`ft_identity_of_chunks` σ₆ collapse** (Phase 3): the new algebra is one
   `chunk_commitment` fold on the σ₆ side; the shape of the collapsed representation
   must still pin through binding (same `eval_pins` idiom, one extra combination).
5. **FS axiom restatement** (Phase 4): the axioms' hypotheses quantify over the
   transcript the deployed verifier actually runs; chunking changes the absorb stream,
   so the statements change. Keep them minimal and re-audit; expect the ALLOWED axiom
   set of `check_axioms` to keep the same four names.
6. **`KimchiProof.public` optionality**: model as `Option` + guard (faithful to
   production) vs always-present at `nc ≥ 1` (simpler). Decide at Phase 1 with the
   fixture in hand; production semantics (:332–335) is the authority.

## Non-goals

- Lookups, optional gates, recursion rows (`prev_challenges`) — orthogonal deferrals,
  unchanged.
- Ragged per-column chunk counts in kimchi (bulletproof-pcs keeps the general form;
  kimchi is uniformly chunked, as in production).
- The PureScript/Rust implementations (`packages/`) — already chunk-aware; this plan is
  `formal/` only, plus the `tools/fixture-dump` dumper variant.
