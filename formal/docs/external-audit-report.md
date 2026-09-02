# External Audit Report — the `formal/` Verification Stack

> **STATUS (superseded): the probabilistic soundness line this document is largely about was
> RETIRED.** The forking / knowledge-soundness tree in `kimchi` and `bulletproof-pcs`, and the
> `Zcash/ironwood` dependency under it, were deleted; see `soundness-line-retirement.md` for
> what went, why, and where to recover it. This file is kept as the record of an outside
> engagement — read it as history. Its open items (O-1a / O-1b), its locked-target and
> exhibit-set invariants, and its gate counts no longer describe this repository.

**Engagement:** per `formal/docs/external-audit-sow.md` (2026-07-28).
**Subject revision:** branch `kimchi-knowledge-soundness`; SoW pin `92a0fb7f` (PR #280), audited at
HEAD `2c8c57cc` (= pin + one lint commit touching `bulletproof-pcs` only; that delta is examined
in A-4 and found definitionally neutral).
**Reference:** `mina/src/lib/crypto/proof-systems` at the mina submodule pin
`3969f761846edc33b2a2fda8fd2d096d0442659e`.

**Method.** Adversarial review of the Tier 1–3 statement surface (read in full), five parallel
review streams (trust surface/CI; constants; Fiat–Shamir schedule; verifier algebra;
wire/fragment), independent re-execution of the whole gate battery, per-root axiom-closure
measurement, full fixture regeneration from the pinned proof-systems checkout, and an attack log
extending the SoW's C2 set. Proofs were not re-read (SoW §8); statements, definitions,
hypotheses, gates, and the executable verifier were. Every load-bearing claim in this report was
verified against the source by the report's author, not accepted from a summary.

---

## 0. Executive summary

The development's structural claims hold up: the tree contains **zero `axiom` declarations**,
zero `sorry`, and no metaprogramming, `unsafe`, `opaque`, `partial`, `@[extern]`, or
`@[implemented_by]` surface anywhere in library code; the endpoints are genuine measure-theoretic
knowledge-soundness statements with the right quantifier structure and a data-valued extractor;
the anti-vacuity exhibits the SoW names all exist, are axiom-clean, and do what they are said to
do; the gate battery reproduces green on a clean run; and regenerating every fixture from the
pinned proof-systems checkout reproduces the committed artifacts **byte-for-byte**. The statement
work is, on the axes the SoW asks about, careful and largely self-aware.

Two findings, however, are Critical by the SoW's own calibration — *the executable verifier
semantically diverges from the deployed algorithm inside the modeled fragment* — and one of them
is not new to the project:

1. **The EndoMul gate's constraint list is a different permutation of production's, with one
   sign flipped** (finding V-1). Production orders `[bool b1..b4, window-1 (s1,xr,yr), window-2
   (s3,xs,ys), (16n+8b1+4b2+2b3+b4 − n′), inv]` (`endosclmul.rs:524–549`); Lean orders
   `[window-1, window-2, inv, bool b1..b4, n′ − (16n+…)]` (`Gate/EndoMul.lean:132–156`). Since
   `alphaCombo` weights position *k* by `α^k` exactly as production's `combine_constraints` does,
   the two constant terms differ whenever `emul_selector(ζ) ≠ 0` — i.e. `kimchiVerify` rejects
   essentially every honest production proof of an EndoMul-bearing circuit. **This is the
   project's own prior-audit finding C2, verified 2026-07-24 and still open — and it appears
   nowhere in the SoW's §7 self-declared gap list.** It is masked by every fixture (all five
   accepted-proof fixtures and the linearization fixture have `emul_selector ≡ 0`; so does
   `mul_selector`, leaving VarBaseMul's alignment on review evidence alone).
2. **The Fiat–Shamir absorb of the point at infinity encodes one zero where production encodes
   two** (finding V-2): `sponge.rs:335–339` absorbs `[0]` then `[0]`; `FqSponge.lean` `absorbG`
   absorbs `[0]`. Zero absorbs do not change state *values* but do advance the duplex position,
   so any absorb following an identity point diverges — and identity points are inside the
   modeled wire language and freely choosable by a game adversary. Honest proofs are unaffected
   (negligible probability); the fix is one line. The sponge-trace fixtures structurally cannot
   see it: every generated `absorb_g_inf` shape either ends there or is followed by a squeeze,
   which permutes identically from either position.

Three further findings are High:

3. **Four gates that the SoW presents as part of the battery are wired into no automation**
   (A-1): `check_locked_target.sh`, `check_sorry_census.sh`, `check_extractor_computes.sh`, and
   `check_ironwood_generic.sh` appear in no workflow, Makefile target, or hook — verified by
   direct search of `.github/workflows/*.yml` and `Makefile`, and they were never present in
   `lean.yml`'s history. All four *pass* when run manually (this audit ran them), so the claims
   they protect are true today; what is absent is the enforcement. The statement freeze, the
   sorry census, and the only behavioural anti-vacuity check are honour-system between reviews.
4. **The modeled-fragment boundary is absent from every surface where the results are presented**
   (C-1). No endpoint docstring, module preamble, or `Forking/*` preamble mentions lookups,
   optional gates, recursion, or — the one most likely to mislead — the SRS regime: `hkn :
   nc·2^k = n` excludes production's sub-SRS configuration (`max_poly_size > n`), which is the
   *default* o1js/Mina setup. A reader of the endpoint alone would not learn that Mina/pickles
   proofs are outside the fragment on four independent axes.
5. **`htpos` excludes a production-accepted proof shape** (B-1). Production checks only
   `t_comm.len() ≤ 7·chunk_size`; an empty quotient commitment is processed by both verifiers,
   yet `htpos : ∀ basis O, 0 < tComm.size` disqualifies any adversary that ever emits one. No
   exhibit prices that attack shape; it is excluded by hypothesis, undocumented at the endpoints.
   (This extends the project's own M4 from the run-soundness roots up to Tier 1.)

One finding runs the other way — the only place the development **understates** itself:

6. **The extractor-cost limitation is claimed but not established** (E-1, §4.8). Two docstrings
   argue from `Complete`'s `2^128`-long order lists to an astronomical honest `R`. That inference
   skips the extractor's early exit: a table on which the adversary loses costs exactly **one**
   run, and the exhaustive scan fires only on winning tables — so `ReductionEfficient`, which
   averages over tables, constrains the classical expected-forking quantity, not the worst case.
   Ironwood proves a conditional bound of exactly the needed kind (`ExpectedRuns.lean`:
   `E[runs] ≤ (6/δ)^k` under a good-challenge density floor) that **neither package imports**, on
   a different averaging axis. The honest status is that the extractor's cost is *unproved*, not
   known-large; closing it would make ε derivable from a generic-group bound rather than assumed
   — i.e. would recover concrete security.

On the two remaining charter dimensions the news is good. The **statements are well-formed**:
∀-quantified over families *and* over complete fork tapes (stronger than tape-averaging), the
measure is the uniform product over setup scalars × challenge table with no conditioning and no
quantifier inversion, `ExtractsWitness` demands satisfaction of the circuit the key corresponds
to at the claimed public input, and the extractor is a fixed data-valued function whose semantics
sit outside it — so an unfinished proof could only ever have enlarged the failure set. The
**anti-vacuity story is real**: the honest family wins on every table (so the bound is about the
extractor, not about an empty win set), the deferred-δ counterexample is exhibited and locked,
and commitment binding is *refuted* at the sampled basis, which is why no binding hypothesis can
appear. The random-oracle idealisation enters at exactly one place — `FSFaithful`'s eight read
equations — and is carried by no axiom. δ is honestly labelled a residual rather than a
reduction, and the development says so at every consumer.

---

## 1. Reproduction transcript (deliverable 6)

Lean toolchain pinned `v4.30.0`, warm `.lake` workspace. A from-scratch Mathlib build was not
repeated; `lake exe shake`/`runLinter`/kernel-replay were reviewed statically rather than re-run.

| Step | Result |
|---|---|
| `lake build` (workspace) | ✓ (two `info`-level `ring` fallbacks at `Gate/Semantics/EndoMul.lean:505` — a try-then-fallback proof; one `unusedSectionVars` warning at `Bulletproof/Forking/Game.lean:282`) |
| kimchi / bulletproof-pcs / pasta / snarky axiom gates | ✓ **39 / 28 / 13 / 5** roots — exactly the SoW's counts |
| `check_locked_target.sh` *(not in CI)* | ✓ all seven pinned blocks intact |
| `check_shape_literals.sh` | ✓ 42 files |
| `check_sorry_census.sh` *(not in CI)* | ✓ tree sorry-free |
| `check-style.sh` | ✓ |
| `scripts/deadcode.sh` | ✓ "no dead code" |
| `check_extractor_computes.sh`, `check_ironwood_generic.sh` *(neither in CI)* | ✓ extractor **computes** on the fixture; ironwood's generic layer instantiates at `Fin (2^128)`; `Wins` IS `fsWinsFull` at `m = 0` by `Iff.rfl` |
| sponge vectors, fq-sponge + group_map, perm, index ×3, linearization, kimchi verifier, VK correspondence | ✓ all ten drivers |
| **Fixture regeneration (C3):** `rustup run 1.92 cargo build --release`, all eight dumpers re-run against the pinned submodule, recursive diff vs `formal/*/fixtures` | ✓ **byte-identical** (only the committed `.gitignore` and the two documented gitignored `*_debug.json` sidecars differ) |
| Closure measurement (`#print axioms`) | endpoints = 3 standard + 3 CompElliptic `native_decide` certificates per curve; `kimchiVerify_eq_verifyWith`, `wins_iff_kimchiVerify`, `honestKimchiFamily_wins`, `exists_ne_zero_kernel_scalarBasis` = exactly the 3 standard axioms |

The C3 subject-identity requirement holds syntactically: the drivers call
`kimchiVerify C σ cvk cp pub` (`check_kimchi_verifier.lean:56`) — the same constant
`kimchiVerify_eq_verifyWith` pins to the game's verifier. No fork between the theorem's subject
and the check's subject.

---

## 2. Work stream A — structure and trust surface

### 2.1 What each gate enforces, and where it can be dodged

| Gate | In CI? | Enforces | Bypass / gap |
|---|---|---|---|
| `kimchi/scripts/check_axioms.lean` | yes (`lean.yml:67–70`) | `collectAxioms` over 39 roots; hard-fails on a disallowed axiom **and** on a root missing from the environment | audits 39 names, not the 171-line `roots.txt`; statements consumed by nothing are in no closure (A-2); `allowed` editable in-PR |
| bulletproof-pcs / pasta / snarky axiom gates | yes | 28 / 13 / 5 roots; snarky's allowlist is the three standard axioms with no `ofReduceBool` | same class |
| poseidon axiom gate | **absent** | — | SoW's "axioms ×5" is four (A-5) |
| `scripts/deadcode.sh` | yes (`:117–120`) | dead = 0, hard fail, over the union of five `roots.txt`; unknown name ⇒ failure; script-surface roots must appear textually under `scripts/` | `Snarky.*` excluded (as §7.7 declares); declarations authored under non-project namespaces are invisible; auxiliary-name heuristic exempts by name shape; script anchoring matches the **last** name component against a corpus that includes never-executed files |
| `check_locked_target.sh` | **NO** | seven statement blocks rendered by anchor-regex and diffed vs `locked_target.expected`, plus three grep guards (extractor not `noncomputable`; two exhibits exist) | never runs (A-1); textual by design (§7.8); pins the **IPA** rung only — the kimchi endpoints, `ExtractsWitness`, `Wins` and kimchi's `relationFinder` have no pin (A-3) |
| `check_sorry_census.sh` | **NO** | pins the sorry set both directions; currently empty | never runs; scope excludes `KimchiFixture/`, `BulletproofFixture.lean`, and all `scripts/` — i.e. the parser/driver code the artifact checks run |
| `check_extractor_computes.sh` | **NO** | the only *behavioural* gate: `#eval`s the extractor and byte-compares — the check `Classical.choice` cannot fake | never runs |
| `check_ironwood_generic.sh` | **NO** | compiles the upstream-instantiation seam | never runs |
| `check-style.sh`, `check_shape_literals.sh` | yes | formatting; regex scan for bare structural dimensions (file-count floor > 30 guards against a vacuous rename) | shape gate is a style control, not a constants control — `Fin <| 7`, a `let`, or an alias evades it |
| `runLinter` ×8, `shake` | yes | env linters per root (nolints baseline is 2 entries — not a dumping ground); import hygiene | not trust gates |
| `scripts/kernel-replay.sh` | yes, **push-to-main only** | lean4checker replays 8 library roots (Mathlib/CompElliptic/ironwood not replayed) | skipped on every PR; replays *declarations*, so it does not recompute the axiom census (A-6) |
| ten fixture drivers | yes | each ends `#eval main` and `throw`s on mismatch ⇒ nonzero exit | fixtures are committed JSON; CI checks out `submodules: false` and never regenerates, so one PR can move model and fixture together (A-7) |

No `continue-on-error`, no `|| true`, no non-failing step exists in `lean.yml`: every wired gate
fails hard. Path filters restrict PR runs to `formal/**` **targeting `main`**, so a stacked PR
onto a feature branch runs no Lean gate at all; and `setup-lean` runs `lake update mathlib` at CI
time rather than building from the committed manifest.

### 2.2 Positive results

* **Zero `axiom` declarations** anywhere in the five packages (declaration-form search; all 40
  `axiom` token hits are prose). Zero `sorry`/`admit`. No `set_option`, `unsafe`, `opaque`,
  `partial def`, `@[extern]`, `@[implemented_by]` in library code, and no `macro`/`elab`/
  `syntax`/`run_cmd`/`initialize` — there is no metaprogramming surface through which an axiom
  could enter.
* Exactly **two** `native_decide` sites in the workspace, both at `pasta/Pasta/Endo.lean:191–198`,
  both explicitly allowlisted.
* **Definitional single-sourcing confirmed** at the layer that matters: gate `Holds` predicates
  exist only under `kimchi/Kimchi/Gate/`; `Kimchi.Index.Satisfies` dispatches to those same
  predicates; `Kimchi.Gate.Satisfies` is the separate generic-row model, not a fork.

### 2.3 Findings (stream A)

* **A-1 (High) — four gates run nowhere.** `check_locked_target.sh`, `check_sorry_census.sh`,
  `check_extractor_computes.sh`, `check_ironwood_generic.sh` are invoked by no workflow, no
  Makefile target, no hook; their only runner is the manual `formal/scripts/checkpoint.sh`. SoW
  §4/A7 and §9 present them as part of the battery. All four pass when run; the enforcement, not
  the property, is what is missing.
* **A-2 (High) — the axiom gates do not cover the Tier-2/3 surface.** A declaration nothing
  consumes cannot be in any root's closure, and these are consumed by nothing:
  `kimchiVerify_eq_verifyWith`, `Bridge.wins_iff_kimchiVerify`, `honestKimchiFamily_failure_set`,
  `exists_ne_zero_kernel_scalarBasis`, the seven "REVISIT" AGM lemmas, and
  `verifyWith_of_deferred_delta`. Combined with `lake build` treating `sorry` as a warning and
  the census not running (A-1), a `sorry` or stray axiom in the *faithfulness layer or any named
  anti-vacuity exhibit* would pass the entire wired battery. This audit measured those closures
  by hand and they are clean today — but nothing keeps them so.
* **A-3 (Medium) — the lock protects the rung, not the endpoint.** All seven pinned blocks live
  in `Bulletproof/Forking/*`. `vesta/pallas_kimchi_knowledge_sound`, `ExtractsWitness`,
  `KimchiFamily.Wins`, and kimchi's `relationFinder` are unpinned — and kimchi's `relationFinder`
  *is* `noncomputable`, the very property the IPA guard forbids for `deployedExtract` (defensibly
  so: the key gate reads Lagrange-interpolated windows, and the computability that CI checks is
  the IPA extractor underneath — but the asymmetry is undocumented).
* **A-4 (Low, process) — locked bytes changed inside a lint commit.** `2c8c57cc` renamed
  `fam.Coins` → `Coins C k` in four locked blocks and regenerated the `.expected` in the same
  commit. Verified definitionally neutral (the old `abbrev` took a dead family parameter; same
  right-hand side). The episode illustrates §7.8's declared limit: same-PR regeneration is
  invisible to the gate — and, per A-1, the gate would not have run either way. Recommend lock
  regenerations be isolated commits quoting the statement diff.
* **A-5 (Low) — "axioms ×5" is four.** `poseidon/scripts/` has no axiom gate; the Poseidon
  sponge — the object the whole ROM idealisation concerns — is audited only where a
  kimchi/bulletproof root happens to reach it.
* **A-6 (Medium) — kernel replay is not a check on the axiom census, and skips PRs.** For
  *imported* declarations `collectAxioms` reads a per-module table serialized into the `.olean`,
  not the bodies; lean4checker validates proofs but does not recompute that table. It also runs
  only on push-to-main, so PRs merge before any replay.
* **A-7 (Medium) — fixture provenance is unpinned in CI.** No manifest ties a fixture to a
  proof-systems revision, and CI checks out `submodules: false`, so CI can never detect
  fixture-side accommodation. This audit closed the gap by regenerating (byte-identical, §1) —
  which is precisely why C3 is worth repeating on every proof-systems bump.
* **A-8 (Medium) — `native_decide` trust is discriminated by a forgeable name prefix.**
  `isTrustedNativeDecide` accepts any axiom whose name contains `native_decide` and begins with
  `CompElliptic.` (or the two `Pasta.*_lam_nsmul_Gpt.` anchors). Under Lean v4.30 the emitted name
  is `<enclosing decl>._native.native_decide.ax_N`, so a tree-local `native_decide` inside
  `namespace CompElliptic …` would be accepted as an upstream certificate — and this tree already
  authors declarations in `CompElliptic.CurveForms.ShortWeierstrass` and
  `CompElliptic.Fields.Pasta` (`pasta/Pasta/Basic.lean:26–75`, `pasta/Pasta/CompElliptic.lean:15–21`).
  Upstream itself matches on axiom *tier*, not name, and calls the name "toolchain-dependent".
* **A-9 (Low, corrects SoW §1/§A2) — `Lean.ofReduceBool` is not the inherited token.** In v4.30
  it is deprecated and `native_decide` no longer produces it; closures carry per-declaration
  `…_native.native_decide.ax_N` axioms (measured — see §1). The `Lean.ofReduceBool` allowlist
  entries are vestigial. Not a hole (`Lean.trustCompiler` enters via opaque `reduceBool` and is on
  no allowlist), but the SoW's characterisation of the compiler-trust surface names a constant no
  current closure contains, and the real inherited set is broader than "primality and point-count
  certificates" (confirming internal M8: sqrt-order and eigen-anchor certificates also appear).
* **A-10 (Low) — `formal/CLAUDE.md` documents a deleted axiom boundary.** Its "axiom boundary"
  section describes `Cycle/Axioms.lean`, `CMCurve`, and free axioms `pallas_order_smul`,
  `pallas_eigen`, `lam`, with an expected `#print axioms` output containing them. There is no
  `Kimchi/Cycle/` directory and `Pasta.pallas_eigen` is a *theorem* (`pasta/Pasta/Endo.lean:246`).
  The maintainer-facing guide contradicts the zero-axioms claim in the direction of legitimising
  free axioms. (Confirms internal M9.)
* **A-11 (Low) — stale comment in the kimchi allowlist** describes "the declared Fiat–Shamir
  assumption … one per Pasta curve" inside a list body containing no such entries; the
  bulletproof twin correctly records the deletion.

### 2.4 A6 — constants and conventions

Thirty constants were re-derived independently (modular arithmetic; the `endos()` selection was
reproduced with full elliptic-curve arithmetic). **Everything checks out.** Highlights:

* **Moduli / curves / orientation — confirmed.** `p` and `q` agree across CompElliptic and
  mina-curves in hex, decimal, and limb form; both curves are `y² = x³ + 5`; Pallas base = `Fp` =
  Vesta scalar, Pallas group order = `q` — the 2-cycle orientation matches everywhere it is used.
* **The endo trap — confirmed clear.** All four constants re-derived: `pallasEndo = 5^((p−1)/3)`,
  `vestaEndo = 5^((q−1)/3)` (base-field cube roots), and both λ's reproduced through `endos()`'s
  square-selection branch with real EC arithmetic (both curves take the square). Critically, the
  two *roles* are correctly separated even though the two constants per field differ only by a
  squaring: challenge expansion uses `endos::<G>().1` (scalar-field endo_r) at exactly the sites
  `verifier.rs` does, and the gate/linearization coefficient uses the other curve's `endo_q`, as
  pinned by `Corresponds` (`cvk.endo = idx.endoBase`) and confirmed numerically in the fixtures.
* **128-bit squeeze and `endoExpand` — confirmed bit-for-bit**: 2×64-bit limbs, LSB packing, 64
  windows MSB→LSB, init `(2,2)`, the same bit-to-sign and bit-to-register routing, final `a·λ+b`;
  β/γ unexpanded on both sides; the forking layer's integer mirror is bridged by a definitional
  theorem rather than a second transcription.
* **Layout — confirmed**: 15/7/6/7 → `tailRowCount = 43`, plus public and ft = the 45 deployed
  logical rows in `to_batch` order; σ₇ linearized rather than batched; `t ≤ 7·nc`.
* **zk_rows — confirmed**: `(16·nc+5)/7` gives 3/5/19 at nc = 1/2/8, matching the fixtures; the
  three-factor `zkpm` (including its `ω^(n−1)` quirk) is transcribed verbatim with the
  `zkRows = 3` coincidence documented.
* **α layout — confirmed**: one shared gate pool `α⁰..α²⁰` (registered once at
  `VarbaseMul::CONSTRAINTS = 21`), permutation at `α²¹,α²²,α²³`, in all configurations.
* **Shifted scalars — confirmed and clarified**: on the verifier path `Pasta.Shifted` is used
  exactly once, for the `shift_scalar` absorb of the combined inner product, at bit size **255**
  (Type 1 for Vesta since `p < q`, Type 2 for Pallas), matching `commitment.rs` branch-for-branch.
  **`2^254` is not on the verifier path** — it appears only as `pastaFieldBits − 1` in the
  scaleFast2 gate-layer range.

Findings: **A-12 (Low)** `Kimchi/Columns.lean:12–14` claims "each derived constant carries an
`rfl` theorem machine-checking its derivation" — no such theorems exist anywhere in the tree; the
values are correct, the claimed kernel check is absent (add four one-line `example`s or delete the
sentence). **A-13 (Low)** `Verifier/Wire.lean:107–110` says production recomputes `endo` as
`endos::<G>()`; it is `G::other_curve_endo() = endos::<OtherG>().0`. The *bindings* are all
correct — but a wrong comment at the historical trap site is a future-transposition hazard.
**A-14 (Info)** the SvdW `sqrt` sign choices are fixture-pinned rather than derived, so an
arkworks sqrt-convention change on a bump would flip the derived `U` base and be caught only by
fixtures. **A-15 (Info)** the PS-dump driver synthesizes `shifts i = 5^i`, which are *not*
production's Blake2b-sampled shifts — sound for that driver's purpose, worth a comment.

---

## 3. Work stream B — well-formedness of the top-level statements

### 3.1 B1 — the executable verifier as the deployed algorithm

This is where the audit's two Critical findings sit. Everything else in B1 checks out.

**Transcript schedule (30 events, both sides).** The full ordered table was constructed
event-by-event. Confirmed: fq-sponge init and per-curve parameters; digest absorb; public
commitment (negated-input MSM per chunk + `h` via all-ones `mask_custom`, empty input ⇒ `nc`
copies of `σ.h`); the 15 witness commitments; the lookup events correctly *absent* (all guarded
by `lookup_index = None`); β and γ as 128-bit casts **without** endo; `z_comm`; α and ζ as
prechallenge + endo; the `t_comm ≤ 7·nc` guard; the digest taken on a **clone** with
zero-on-overflow while the original stays warm; fr-sponge init and the empty-recursion constant
absorb; `ft_eval1`; the public evals at both points in both regimes; `absorb_evaluations`' exact
row order and ζ/ζω interleaving; v and u as endo-expanded fr squeezes; the **warm** handoff; the
`shift_scalar(cip)` absorb with the Type1/Type2 encodings; `U = group_map(challenge_fq(warm))`;
the per-round `absorb L, absorb R, squeeze` loop; δ; and the Schnorr `c`. The game's oracle-table
reads correspond **1:1** to exactly these 6 + k + 1 challenge squeezes, with the digest, the
fr-constant, and the `U`-base squeeze correctly modeled as deterministic transcript functions
rather than table reads — matching production, where they are derivations, not fresh challenges.

**Algebra.** Confirmed: the chunk-combination exponent base is the SRS width `2^{σ.k}` at both
points (not `ζⁿ`); the two combination layers nest correctly (combined evals feed only the scalar
side; the batch consumes raw per-chunk claims, rows outer / chunks inner, one polyscale power per
segment); the ft row is the only group-side collapse and folds *all* `t` chunks (56 at nc = 8) to
one segment, exactly as `chunk_commitment` does; the barycentric public-eval formula and the
carried path match the production-reachable regimes exactly; `ft_eval0` matches term-by-term
including the α²²/α²³ pole pairing and the 6-vs-7 factor truncations; `f_comm` is the single
`perm_scalar · σ_comm[6]` term (production *asserts* `index_terms` is empty, so this is sound);
the batch row order — recursion, public, ft, z, six selectors, 15 witness, 15 coefficient, 6 σ —
is identical, which matters because polyscale powers index it; `b(X) = Π(1 + u_i X^{2^{k−1−i}})`
with the first challenge on the highest power and the closed-form coefficients matching `Fin.rev`;
and the final Schnorr/`sg` equations match term-by-term, signs included.

**V-1 (Critical) — the EndoMul constraint list.** Verified directly by this audit:

| position | Production (`endosclmul.rs:524–549`) | Lean (`Gate/EndoMul.lean:132–156`) |
|---|---|---|
| 0–3 | `boolean(b1)…boolean(b4)` | window-1 `s1`, `xr`, `yr`; window-2 `s3` |
| 4–6 | window-1 `s1`, `xr`, `yr` | window-2 `xs`, `ys`; distinct-point `inv` |
| 7–10 | window-2 `s3`, `xs`, `ys`; `(16n+8b1+4b2+2b3+b4) − n′` | `boolean(b1)…boolean(b4)` |
| 11 | distinct-point `inv` | `n′ − (16n+8b1+4b2+2b3+b4)` |

The twelve expressions agree pairwise as ring elements, but positional α-weighting is used on
both sides (`combine_constraints` = `Σ α^k·c_k`, `expr.rs:1622–1628`; `alphaCombo`,
`Linearization.lean:61–62`), and the scalar-register constraint is additionally negated. So the
EndoMul summand of the constant term — and hence `ftEval0`, the combined inner product, the
`shift_scalar` absorb, the derived `U` base, and the final check — differ from production on
every proof whose circuit contains an EndoMul row. `kimchiVerify` therefore rejects honest
production proofs there. Internal validity is untouched (gate `Holds` is ∀-over-the-list, hence
order-insensitive; the Lean linearization↔aggregate identity uses one order throughout), so no
Lean theorem is false — what fails is B1's fidelity claim and, with it, C3's "governs the
verifier that accepts real proofs" on the EndoMul-active part of the fragment. **Known:** this is
the project's own statement-audit finding C2 (verified author-direct, 2026-07-24) and it is still
open; the SoW's §7 list does not mention it. Remediation is mechanical — reorder to
`[bool×4, window-1, window-2, D − n′, inv]` and un-negate — plus one fixture with a live
`emul_selector`, since **every** committed fixture has `emul_selector ≡ 0` *and*
`mul_selector ≡ 0`, leaving VarBaseMul's (reviewed-correct) alignment unwitnessed too.

**V-2 (Critical by the SoW's calibration; honest-path-benign) — the infinity absorb.** Verified
directly: production absorbs a fake point as **two** zeros (`sponge.rs:335–339`); Lean's `absorbG`
absorbs **one** (`FqSponge.lean`, `if P = 0 then absorbFq spec s [0]`), and its docstring claims
parity "both cases". Zero absorbs leave state values unchanged but advance the duplex position, so
every downstream challenge diverges whenever an absorbed commitment is the identity — reachable
inside the modeled wire language (the `(0,0)` sentinel parses) and freely choosable by a game
adversary; unreachable for honest proofs except with negligible probability. One-line fix: absorb
`[P.x, P.y]` unconditionally (the zero sentinel *is* `(0,0)`, so the branchless form reproduces
production in both cases). **The sponge fixtures cannot catch this**: every generated
`absorb_g_inf` shape either terminates there or is followed by a squeeze, and a squeeze permutes
identically from either absorb position — so the driver passes vacuously. A shape
`[absorb_g_inf, absorb_*, challenge]` would distinguish them.

**V-3 (Low) — undeclared behaviour at the two excluded ζ points.** At
ζ ∈ {1, ω^(n−zkRows)} production panics (`.expect("negligible probability")`,
`verifier.rs:459–460`) while the Lean executable takes `ZMod`'s junk division (`x/0 = 0`) and
proceeds. The soundness layer handles this deliberately — `zetaBoundaryBad` excludes exactly these
two points and `szBudget` charges the `+2` — so no theorem is affected; but the executable's
divergence is not in `Verifier/Kimchi.lean`'s declared-deviation list. (The analogous `pubDot`
case *agrees*: arkworks `batch_inversion` skips zeros, as `ZMod` does.)

**V-4 (Info) — deterministic conjunction vs randomized MSM.** Production checks one
rng-weighted MSM (`r₁·A + r₂·B = 0`, fresh `thread_rng`); Lean checks the two bracket equations as
a conjunction. Lean-accept ⇒ production-accept with probability 1; the direction is conservative
for soundness and is the standard modelling choice, but it is a real algorithm-vs-algorithm
difference worth one sentence in the declared list. Production's multi-proof `batch_verify` is
likewise outside the fragment (Lean does one proof = `batch_verify` on a singleton).

### 3.2 B2/B3 — the adversary model and the AGM obligations

Every `KimchiFamily` field classified (i) adversary data, (ii) AGM obligation, or (iii)
restriction:

* **(i)** `cvk`, `pub`, `digest`, `adversary`. Standard. `digest` is a free transcript label —
  harmless in-game (the bound is ∀-families) and self-policing in the bridge, since a diverging
  label makes `FSFaithful` unsatisfiable rather than silently applying (worth a docstring line).
* **(ii)** `aRef`/`ρRef`/`hrep`, `aT`/`ρT`/`hTC` — SRS-basis representations of the flat stream
  and the quotient chunks. Notably the *verifying key's* rows are **not** assumed honestly
  represented: a dishonest key-row representation is converted into a returned discrete-log
  relation by the extractor's key gate (`vkBreak`/`ftBreak`). That design removes what would
  otherwise be a hidden hypothesis, and is a genuine strength.
* **(ii, load-bearing)** `hrepPrefix`/`hTPrefix`: a row's declared representation is a function of
  the run's transcript node at that row's absorbing squeeze (`absorbedBy`: key and witness rows at
  β, the `z` row at α, quotient chunks at ζ). *No less* than the fork needs — on two tables
  agreeing at a node, everything absorbed by then has a stable representation, so reprogramming
  later cells cannot retroactively change earlier ones. *No more*, with one honest caveat worth
  documenting: a family whose representations depend on answers to **off-run** oracle cells (while
  emitting the same commitments) is excluded. That is the emission-time reading of AGM-in-the-ROM
  and is the right formalization; the endpoint docstring names it as the class narrowing.
* **(iii)** `Q`/`queryBound` (standard structural bound), `hnc`, `hn`, `hpub` (production enforces
  the same equality), `hvk` (the standard honest-key hypothesis — content audited below),
  `hkn : nc·2^k = n` (**a real scope restriction**, → C-1), and `htpos` (→ B-1).

`hvk`'s content (`Correspond.lean:120–134`): the committed chunk columns are the circuit's own
chunked-indexer output, plus `omega`, `zkRows`, `shifts`, `endo = idx.endoBase`, the Poseidon MDS,
and the Lagrange chunk commitments over exactly the public region. Satisfied by production keys
(`check_vk_correspond` ✓). Minimal and necessary — knowledge soundness is stated *per circuit*.

### 3.3 B4 — quantifiers and the probability space

Endpoint shape (`KnowledgeSoundness.lean:4361–4373`): ∀ `B`, ∀ family, ∀ **complete** fork tape,
∀ `R ε δ`, hardness → efficiency → a bound on
`μ_uniform{(s,O) | Wins(augOfSetup(scalarBasis B s), O) ∧ ¬ExtractsWitness…}`.

* **No ∃-coins.** The tape is universally quantified — stronger than the literature's
  expectation-over-tapes. `Complete` is a pure enumeration property of the tape (every node's
  order list contains every prechallenge, recursively), adversary- and family-independent, so it
  cannot smuggle a success assumption. Satisfiable by construction; no witness term exists in
  either tree (D-2).
* **The measure** is `PMF.uniformOfFintype` on the finite product of setup scalars and the *whole*
  oracle table, read through `toOuterMeasure` — the standard finite-uniform framing, on a set with
  no measurability side conditions.
* **No conditioning, no per-run reading, no quantifier inversion.** `hHard` is gated by
  `ReductionEfficient` (capstone form) and `reductionEfficient_exists` proves ∃R without
  inspecting the counter — so the gate records *which* reductions hardness is assumed against and
  asserts nothing about efficiency. The file says exactly this.

### 3.4 B5 — the extraction predicate

`ExtractsWitness` = "`attempt` returned `PSum.inl a`, **and** `Satisfies fam.idx (pubView fam.idx
(fam.pub basis)) (runWTab … a)`". The payload is data; all semantics sit in the measured event, so
an open proof anywhere in the chain could only enlarge the failure set — the design rule the SoW
asks to confirm, confirmed at the definition. `Satisfies` is the arithmetization-layer
satisfaction of the circuit `hvk` ties to the presented key, at the claimed public input, and it
bottoms out in the single-sourced gate `Holds` predicates. **Well-formed**: "knowledge" here is
possession of a satisfying witness table for the right circuit at the right public input.

### 3.5 B6 — the error bound, term by term

| Summand | Audit |
|---|---|
| `(Q+k+1)·3/2¹²⁸` | Presence/query loss of the three-way fork over the 128-bit prechallenge alphabet; ironwood's counting layer instantiated at `Fin (2^128)` (gate-verified). Shape confirmed. |
| `(2ᵏ+1)·ε` | `Fintype.card (SetupIndex (2^k)) = 2^k + 1` — the number of **setup slots** the DL challenge can be planted in; genuine fixed-slot reduction to textbook DL. **The SoW §B6 gloss "the DL charge across the fork's arity" is wrong** (D-3). |
| `δ` | The residual: the derived-base event's own measure, per `derivedUDL_iff_residual_measure`. Honestly documented at every consumer. Sound as stated; not estimable by reduction (§5). |
| `(Q+1)·szBudget/2¹²⁸` | Arithmetic audited: `szBudget = 2·7(n−zk) + n·(21+3−1) + 9n + 2 + 2(m−1) + 1` with `m = nc+1+43·nc`, matching each per-set cardinality lemma. Counting is done on the **prechallenge** domain with per-squeeze expansion maps proved injective (`natCast` below the modulus for β/γ; `expandPre_*_injective` elsewhere), which is what makes "bad set of size c ⇒ ≤ c prechallenges" valid. The `(Q+1)` adaptive factor is justified against ironwood's own precedent. Confirmed. |

### 3.6 B9 — the faithfulness layer and the ROM boundary

`kimchiVerify_eq_verifyWith` pins the deployed verifier to the generic one at **named** reads —
the existential trap the SoW warns about is absent, and the file documents why the existential
form was rejected. `FSFaithful` is **eight read equations and nothing else**; no base equation
hides in the bundle, because the game's base slot and the deployed verifier's are the *same term*
(`KimchiFamily.warmBase`), closed by `rfl` — the earlier cold-base ninth field is gone, and
Bridge.lean records that it was "a modelling hypothesis, false in general".
`wins_iff_kimchiVerify` composes them pointwise. All three close under exactly the three standard
axioms (measured). **The random-oracle idealisation therefore enters here and only here, carried
by no axiom** — confirmed. The two honest deviations from "the table is the sponge" are the `sg`
slot (declared, priced by `Q`) and the fact that `U` is *not* idealised at all but stays the
concrete warm Poseidon squeeze.

### 3.7 Findings (stream B)

* **B-1 (High) — `htpos` excludes a production-accepted shape.** Production enforces only
  `t_comm.len() ≤ 7·chunk_size` (empty is legal; `chunk_commitment` folds it to zero); the Lean
  checked record carries the same one-sided bound; `kimchiVerify` has no emptiness guard. Yet
  `htpos` disqualifies any adversary that ever emits an empty quotient, so the endpoints say
  nothing about that attack shape and the docstrings do not carry the restriction. Extends
  internal M4 to Tier 1. Fix: enforce non-emptiness at the wire boundary as a declared
  strengthening, discharge the degenerate `t := 0` case, or carry the restriction into every
  presentation.
* **B-2 (Medium) — endpoint docstrings misstate the axiom closure.** Both claim "`#print axioms`
  … gives exactly `propext`, `Classical.choice` and `Quot.sound`". Measured: three additional
  CompElliptic `native_decide` certificate axioms per curve. The *trust story* is confirmed; the
  word "exactly" is false. (Adjacent claims — no `sorryAx`, no Fiat–Shamir axiom — are true.)
* **B-3 (Medium) — stale warm/cold caveat on a Tier-2 statement.** `KnowledgeSoundness.lean:345–349`
  says the game evaluates the generic verifier at a **cold**-sponge base and that warm/cold
  agreement "is not proved here". Both are false of the current development: `Wins` feeds
  `fam.warmBase` (line 963) and Bridge.lean proves the slots are the same term. A reader auditing
  the ROM boundary from this docstring would model the game wrongly. (Independently flagged by two
  streams.)
* **B-4 (Medium) — a promised exhibit does not exist.** Honest.lean's section
  "Non-vacuity of the family itself" (lines 1544–1569) says "This section closes the loop: it
  exhibits an index, and with it a family, unconditionally on each curve", names `vestaOmega`/
  `pallasOmega` and a fourth-root construction — and the section body (`section Trivial` …
  `end Trivial`) is **empty**; those names exist nowhere in the tree. The neighbouring docstring
  correctly states the witness is missing. Consequence for C6: the honest-family layer has no
  per-curve corollary — by the house doctrine, exactly the shape that has hidden unsatisfiable
  side conditions before. Nothing suggests `publicCount = 0` is unsatisfiable (the prose's own
  sketch is convincing), but the loop is open and the prose says it is closed.
* **B-5 (Info)** — document `fam.digest`'s self-policing; **B-6 (Info)** — document
  `hrepPrefix`'s off-run-cell exclusion.

---

## 4. Work stream C — anti-vacuity and applicability

### 4.1 C1 — hypothesis satisfiability

| Hypothesis | Evidence | Verdict |
|---|---|---|
| `Index` | `check_index_fixture.sh` builds three production indices by decision procedure and checks `Satisfies` on production witnesses | satisfiable at production circuits ✓ (no Lean term — declared §7.5; sharpened by B-4) |
| `hvk`/`Corresponds` | `check_vk_correspond.sh`, production keys, nc ∈ {1,2} | ✓; unwitnessed at nc = 8 (C-3) |
| family inhabitation | `honestKimchiFamily` + `honestKimchiFamily_wins` (axiom-clean, measured) | constructive **given** a `publicCount = 0` index — the B-4 gap |
| `coins.Complete` | definition read; pure tape enumeration | satisfiable by construction; no witness term (D-2) |
| `ReductionEfficient` | `reductionEfficient_exists` (sup over bases, counter not inspected) | ✓ for every family; explicitly not an efficiency claim. **But the accompanying prose about how large the honest `R` must be is not supported by the code — see §4.8 / E-1** |
| `DiscreteLogRelationHardFor` | an implication; trivially satisfiable at `ε = δ = 1`; internally consistent | not self-contradictory ✓; ε targets the standard textbook-DL game, δ is the declared residual |
| per-curve arithmetic (`hsmul`, `hinj`, `hne`) | discharged at both curves inside the endpoint proofs | ✓ |

### 4.2 C2 — the attack log (deliverable 3)

| # | Attack | Outcome |
|---|---|---|
| 1 | Always-`none` extractor | **Blocked.** `honestKimchiFamily_wins` (closure measured clean) wins at every table and basis with a live blinder; `honestKimchiFamily_failure_set` reduces the measured event to `¬ExtractsWitness` there, so the acceptance conjunct carries none of the bound. Residue: the B-4 index witness. |
| 2 | Deferred-δ adversary | **Blocked structurally.** The Schnorr node carries `δ`, so the read happens at a node that already fixes it; `verifyWith_of_deferred_delta` exhibits the accepting cheat (`lr = 0⃗, z1 = z2 = 0, δ := −c·(combined + cip·U)`) that would make the game *false* without commit-then-challenge. Locked byte-for-byte. |
| 3 | Assume commitment binding | **Refuted outright.** `exists_ne_zero_kernel_scalarBasis` (closure clean): at the sampled basis every generator is a multiple of `B`, so a nonzero kernel vector exists — any endpoint carrying binding would be vacuous. Breaks are *returned*, not assumed away. |
| 4 | Grind the un-absorbed `sg` slot | **Priced, not free.** `wireWins_pinTable` + `pinTable_factors` factor the *game's* reads through the sg-free domain; `sg_determined_of_verifyWith` pins the accepting `sg` to earlier reads; each probe is a query priced by `Q`. Scope honestly limited to the game's reads. |
| 5 | Plant challenges via the sampled basis | **Blocked.** No family field receives the scalars `s` (leak-freedom by typing); `uRepresentationOfBreak` makes a break's `U` component computed data; the `u` slot is dead on both sides. |
| 6 | Base-override games | **Blocked** by the `*_U_irrelevant` pair; the override point is the warm base the deployed verifier uses. |
| 7 | **Empty quotient (`t_comm = []`)** | **Escapes scope** rather than being blocked → B-1. |
| 8 | **Out-of-fragment eval fields on an in-fragment VK** | **Escapes the wire language**: production absorbs and accepts them → C-2. |
| 9 | **Representation chosen after the challenge** | **Blocked** by `hrepPrefix` — such a family cannot be formed. The AGM narrowing doing its declared work. |
| 10 | **Digest-label collision** | Harmless in-game; the bridge self-polices (B-5). |
| 11 | **Sub-SRS keys** (`max_poly_size > n`, the deployed default) | **Escapes scope** via `hkn`, declared two layers down → C-1. |
| 12 | **Dishonest Lagrange data** | **Blocked**: `Corresponds` pins the public-region Lagrange chunks; within the family, a dishonest public-row *representation* becomes a returned DL relation. |
| 13 | **Wrong `endo`/`omega`/`shifts`/`zkRows`** | **Blocked**: all four are `Corresponds` pins. |
| 14 | **Ragged short `t_comm`** (1 ≤ size < 7·nc) | Inside the family class; the ft-assembly machinery covers it. No gap. |
| 15 | **Public-arity games** | **Blocked** by `hpub` + the size guard + the Lagrange pin; the guard fails closed. |
| 16 | **Identity-point commitment** | **Escapes faithfulness** → V-2: the model's transcript is not the deployed transcript on that sublanguage. |
| 17 | **EndoMul-bearing circuit** | **Escapes faithfulness** → V-1: the Lean verifier's accepted set is not production's there. |

Every degeneracy attempt lands on a named blocker **except** #7, #8, #11 (scope boundaries, two of
them undeclared at the presentation surface) and #16, #17 (the two faithfulness divergences).

### 4.3 C3 — end-to-end artifact run

Performed in full (§1): byte-identical regeneration, all ten drivers green, and the theorem's
subject is literally the drivers' subject. Note the one caveat this creates: the drivers'
green status is *compatible* with V-1, because no fixture activates the EndoMul or VarBaseMul
selector — regeneration reproduces the same blind spot. The C3 recommendation is therefore to
extend `fixture-dump` with a circuit exercising both gates.

### 4.4 C4/C5 — wire-protocol identity and the modeled fragment

The complete field-by-field table over `ProverProof` + `VerifierIndex` — every field classified
faithful / narrows / widens / unmodeled-declared / unmodeled-undeclared with citations on both
sides — plus the corruption-test inventory and the precise fragment statement, are in
**Appendix W**. Highlights:

* **Faithful**: the `t_comm ≤ 7·nc` bound; the evaluation-length sweep at `chunk_size`; the
  `evals_public` tri-state (carried wins at any nc, required at nc > 1, barycentric at nc = 1)
  including the production-reachable carried-at-nc=1 branch; fixed dimensions 15/7/6/15; the
  `psm_comm → poseidonComm` rename; no legacy `shifted` field on the native wire.
* **`prev_challenges` is language-equal within the fragment**: production *rejects* non-empty at
  `vk.prev_challenges = 0`, which is exactly what the Lean model cannot represent, and the
  constant empty-recursion fr-absorb is transcribed. The SoW's silent-ignore worry does not
  materialize.
* **Declared narrowings**: `w_comm`/`z_comm` chunk pinning (declared in-file); VK-side chunk
  pinning (declaration under-enumerates → W-F4); the opening `lr` round-count pin, which is a
  narrowing still *presented* as a production check (M11 residue → W-F3).
* **Declared widenings, closed at the endpoints**: the `public` count guard substitution (closed
  by `hpub`); `digest`/`endo`/`lagrangeBasis` as model inputs (closed by family data and
  `Corresponds`).

**Findings:**

* **C-1 (High) — the boundary is absent where the results are presented.** No endpoint docstring,
  module preamble, or `Forking/*` preamble states the no-lookups / no-optional-gates /
  no-recursion / no-sub-SRS boundary; the headline reads "the deployed kimchi verifier"
  unqualified. `formal/CLAUDE.md` even lists the modeled gates without Poseidon. SoW C5's own bar
  fails at the primary surface.
* **C-2 (Medium) — the fragment must also be cut on proof shape.** For an in-fragment VK,
  production accepts proofs whose optional-gate/lookup *evaluation* fields are present: they are
  length-checked, **fr-absorbed** (hence transcript-affecting), and never rejected. Those
  production-accepted proofs have no Lean counterpart, and the required condition ("all optional
  and lookup evaluation fields `None`") is stated nowhere. (Junk lookup *commitments*, by
  contrast, are wholly ignored by production and are benign.)
* **C-3 (Medium) — in-fragment fixture gaps.** No fixture exercises a nonzero EndoMul or
  VarBaseMul selector — the blind spot that let V-1 persist under green CI — and
  `check_vk_correspond` stops at nc ∈ {1,2}, leaving `Corresponds` unwitnessed at nc = 8. The
  empty-public-input branch is likewise review-verified only.
* **C-4 (Low/Info) — decoder hygiene.** Unknown-key dropping, non-canonical numeral reduction mod
  p, `Nat.log2` truncation on a non-two-power `n`, empty-chunk rejection, and the driver-resident
  `σ.k ≤ domainLog2` guard (`runNc` returns 1 on underflow — coincidentally matching production's
  sub-SRS `chunk_size = 1`). All unreachable from `fixture-dump` output; none reaches acceptance.

### 4.5 C6 — per-curve instantiation completeness

Confirmed at the endpoints (both proved, closures measured), the IPA endpoints and both
query-loss rungs, the per-curve expansion and scalar-action lemmas, and the `PerCurve`
elaboration examples (the `hU`-lesson acceptance test, present and passing). **The one layer with
no per-curve corollary is the honest kimchi family** — blocked on B-4. By the project's own
doctrine that is the tell to close first.

### 4.6 C7 — Fiat–Shamir schedule fidelity

Schedule fidelity is **confirmed modulo V-2**: event by event, the Lean transcript is the
production schedule of `fn oracles` + `SRS::verify`, with no extra or missing squeeze, and the
table reads correspond 1:1 to the challenge squeezes. Fixture coverage splits cleanly: the sponge
traces pin *op semantics* (both `absorb_fr` encodings, limb-buffer lifecycle across every op
pair, endo expansion, SvdW vectors, both curves) but no composite order; composite order is pinned
solely by the five whole-proof fixtures (each asserted production-accepted at dump time) plus the
cold-start IPA fixtures. Steps exercised by **no** fixture: the infinity absorb (structurally
invisible — V-2), the empty-public-input branch, and the digest-overflow branch. Only the first
hides an actual divergence; all have cheap fixture remedies.

### 4.7 C8 — the setup distribution

The game samples uniform scalars against `B`, with the family seeing only the points — leak
freedom is enforced by typing, since no field of `KimchiFamily` receives `s`. The `u` slot is dead
on both the acceptance and extraction sides and is overridden per run by `fam.warmBase`, the same
term the deployed verifier squeezes from the warm state; the cold-base alternative is documented
as false and removed. This is the standard generators-as-uniform-group-elements idealisation of
the hash-derived SRS, and `ε` is priced against exactly this distribution. **Confirmed**, with the
observation that the idealisation itself is a modelling step of the same standing as the ROM table
and belongs in §7 (it is §1-implicit but §7-absent).

### 4.8 The extractor's cost — `Complete`, `ReductionEfficient`, and what is actually proved

This subsection exists because the development's own account of its extractor cost is the one
place in the audit where it **understates** its result, and because ε's concrete-security reading
(§5) depends entirely on it.

**What `Complete` does.** It is a *search-completeness* condition, not an efficiency one. In
`recursiveAlgebraicForkFrom_isSome_of_not_escape` (`Recursive.lean:1255–1290`) the extractor scans
a node's `order` list for a challenge that keeps the transcript prefix stable and lets the
sub-extraction succeed; `Complete` — every node's order list contains every prechallenge — is what
turns "a good challenge exists" into "the scan finds it", which is what makes non-escape imply
extraction. It is the derandomized substitute for "sample challenges until one works". It asserts
nothing about cost, and the escape set it enables is what the query-loss summand prices.

**The control-flow fact.** In `recursiveAlgebraicForkFrom` (`Recursive.lean:507–560`) each node
first computes `first := forkFrom (m+1) O p (child u₁)` — **same table, same run, no rewind** — and
on `first.output = none` returns immediately with `runs := first.runs`; the leaf returns
`{output := if win O p then … else none, runs := 1}`. Therefore **a table on which the adversary
does not win costs exactly one run**, and the exhaustive scan (`nextForkChallenge`,
`Recursive.lean:242–255`) fires only after `first` has already succeeded — i.e. only on winning
tables. Since `ReductionEfficient` is `∀ basis, ∑_O attemptRuns basis O coins ≤ R · card(Coins)`,
an average over oracle tables, the quantity it bounds is `P[win]·E[cost | win] + P[¬win]·1` — the
classical expected-forking quantity, in which the `1/density` scan cost is paid against the
`density` probability of ever scanning.

**Consequently the docstrings' inference does not follow.** Two places argue from `Complete`'s
`2^128`-long order lists directly to an astronomical honest `R`
(`bulletproof-pcs/Bulletproof/Forking/KnowledgeSoundness.lean:593–600` and `:804–806`). That step
skips the early exit: the order-list length bounds the *worst case*, not the table-average that
`ReductionEfficient` actually constrains. Nothing in the audit contradicts the possibility that a
modest `R` is achievable; what is missing is a theorem either way.

**The three-layer state of play.**

1. *Proved unconditionally, and the only thing `reductionEfficient_exists` can fall back on*:
   ironwood's worst case `recursiveAlgebraicFork_runs_le ≤ (2·|F| + 1)^k` (`Recursive.lean`,
   "Worst-case run bound"), ≈ `2^2064` at `k = 15` over the `2^128` alphabet, plus its summed form
   and `reductionEfficient_exponential` (`Algebraic.lean:1440`). At that budget the generic-group
   bound on ε is vacuous.
2. *Proved upstream, **unused by either package***:
   `recursiveAlgebraicFork_sum_runs_le_of_forkSpread` (`ExpectedRuns.lean:902`) — under
   `ForkSpread σ₀` (`:583–585`: at every node, on every table, at least `σ₀` challenges are good),
   `E[runs] ≤ (6·|F|/(σ₀−1))^k = (6/δ)^k` for `δ = (σ₀−1)/|F|`. Neither `Bulletproof.*` nor
   `Kimchi.*` imports that file. Two honest caveats: `ForkSpread` is a **uniform** (∀-table) density
   floor, i.e. a strong heavy-row hypothesis, not an average; and its averaging axis is the
   **tape** for a fixed oracle table, where our `ReductionEfficient` averages over **tables** for a
   fixed tape. Bridging those axes is real work, not plumbing — though the endpoints being
   ∀-tape means a consumer is free to instantiate at a favourable tape, which is the same
   probabilistic-method shape the upstream bound has.
3. *Open even upstream*: `ExpectedRuns.lean`'s own file docstring — "An unconditional polynomial
   AFK bound remains open."

**The quantitative regime, if layer 2 were plumbed.** `(6/δ)^k` at `k = 15`: `δ = 1/2` gives
`≈ 2^54` adversary calls (fine for a reduction); `δ = 2^-20` gives `≈ 2^339`, worse than solving
discrete log outright. So the exponent in `k` is real, and the result would be quantitatively
meaningful only against adversaries whose per-round good-challenge density is not tiny — which
should be said explicitly wherever the bound is quoted.

**Suggested documentation fixes.** Three edits, all prose, none touching a statement:

* `KnowledgeSoundness.lean:593–600` (the `Capstone` section docstring). Replace the inference
  "`coins.Complete` … requires every node's order list to enumerate the whole prechallenge domain,
  so any `R` satisfying `ReductionEfficient` here is astronomically bigger than the cost of solving
  discrete log outright" with what is actually known: *`Complete` is a search-completeness
  condition — it is what makes non-escape imply extraction — and it does not by itself bound the
  cost. `ReductionEfficient` averages the run count over oracle tables, and a table on which the
  adversary loses costs one run (`recursiveAlgebraicForkFrom` returns at the leaf without
  rewinding), so the quantity gated here is the expected-forking cost, not the worst case. What is
  proved is only the worst case, `(2·|F| + 1)^k`; a table-averaged bound is not proved here.
  Upstream's `ExpectedRuns.lean` proves `E[runs] ≤ (6/δ)^k` under a uniform good-challenge density
  floor, on the tape-averaged axis; porting it to this axis is open, as is any unconditional
  polynomial bound.*
* `KnowledgeSoundness.lean:804–806` (limit 3 of the `ipaVesta_knowledge_sound` docstring). Replace
  "`coins.Complete` forces order lists of size `2¹²⁸`, so the honest `R` far exceeds the cost of
  solving discrete log outright" with: *the extractor's cost is **unproved**, not known-large —
  `reductionEfficient_exists` obtains some `R` without inspecting the counter, and the only proved
  bound is ironwood's worst case `(2·|F|+1)^k`. Because ε bounds the DL advantage of this specific
  finder, a generic-group grounding of ε needs a cost bound the development does not yet have; see
  `ExpectedRuns.lean` for the conditional bound that would supply one.*
* Both kimchi endpoint docstrings (`Kimchi/Verifier/KnowledgeSoundness.lean:4334–4360` and
  `:4381–4384`) currently say nothing about extractor cost at all, while inheriting the issue
  through `hEff`. Add one sentence: *`hEff` fixes which reductions `hHard` is taken against; the
  extractor's cost is not bounded by any theorem in this development, so ε is assumed for the
  finder rather than derived from a time bound.*

Adopting these turns a claimed-but-unproved limitation into an accurately-scoped open item, and it
is a prerequisite for E-1's upgrade being legible as an upgrade.

---

## 5. Concrete-security note (B7; deliverable 4)

At deployed shape `k = 16`, `n = 2^16`, `nc = 1`, `zkRows = 3`:
`szBudget = 3,014,705 ≈ 2^21.5` (it scales as ≈ `46n`; `2^17.5` at `n = 2^12`).

| `Q` | query loss `(Q+k+1)·3/2¹²⁸` | SZ `(Q+1)·szBudget/2¹²⁸` | total unconditional |
|---|---|---|---|
| `2^64` | `2^-62.4` | `2^-42.5` | **`2^-42.5`** |
| `2^80` | `2^-46.4` | `2^-26.5` | `2^-26.5` |
| `2^100` | `2^-26.4` | `2^-6.5` | `2^-6.5` |

The SZ term dominates by ~20 bits and the bound stays below 1 up to `Q ≈ 2^106.5`. Under the
folklore heuristic `ε ≈ 2^-126`, the `(2^16+1)·ε ≈ 2^-110` term is negligible against it.

**The extractor-cost caveat, stated more precisely than the development states it.** ε bounds the
DL advantage of one specific algorithm — `fam.relationFinder coins`, which runs the forking
extractor — so grounding "ε is small" in a generic-group time bound requires knowing that
algorithm's running time. What is *proved* about it is only ironwood's worst case,
`recursiveAlgebraicFork_runs_le ≤ (2·|F| + 1)^k` (`Recursive.lean`), ≈ `2^2064` at `k = 15` over the
`2^128` prechallenge alphabet, at which the generic-group bound is vacuous. **But the
development's own gloss — that `coins.Complete` therefore makes the honest `R` astronomical — does
not follow from the code** (finding E-1): a table on which the adversary loses costs exactly
**one** run, because `recursiveAlgebraicForkFrom` descends without rewinding, the leaf returns
`none`, and every level forwards `first.runs`; the exhaustive scan runs only on winning tables.
Since `ReductionEfficient` averages over oracle tables, the quantity it bounds is
`P[win]·E[cost | win] + P[¬win]·1`, which is the classical expected-forking quantity, not the
worst case. Ironwood in fact proves a conditional version —
`recursiveAlgebraicFork_sum_runs_le_of_forkSpread` (`ExpectedRuns.lean`): under a fork-spread
hypothesis `σ₀`, `E[runs] ≤ (6·|F|/(σ₀−1))^k = (6/δ)^k` — **which neither package imports or uses**,
and whose averaging axis is the *tape* where our `ReductionEfficient` averages over *tables*.
Upstream's own file docstring records that "an unconditional polynomial AFK bound remains open".
So the honest position is: the extractor's cost is *unproved* rather than known-astronomical, the
usable regime is `δ` bounded away from `0` (at `k = 15`, `δ = 1/2` gives `≈ 2^54`; `δ = 2^-20`
gives `≈ 2^339`, worse than solving DL), and closing this would recover the concrete-security
reading of ε rather than merely improving a constant. δ has no reduction reading at all.

A consumer wanting a headline number should quote the **unconditional** row: *against
`2^64`-query ROM/AGM adversaries in the modeled fragment, acceptance without an extractable
witness has probability at most ≈ `2^-42`, plus terms priced by DL-flavored assumptions.* The
effective query ceiling is ~106 bits rather than 128 — inherent to 128-bit FS challenges at this
circuit size, and worth stating wherever bits-of-security are quoted.

**Verdict on B7: quantitatively meaningful** — the right-hand side is far below 1 in realistic
regimes and the dominant terms are assumption-free.

---

## 6. §7 accounting — confirm / correct / augment (deliverable 5)

| §7 item | Verdict |
|---|---|
| 1. ROM is a frame, not an assumption in the system | **Confirmed.** Uniform table + eight `FSFaithful` equations; no axiom carries it (closures measured). |
| 2. Endpoints are AGM-relative | **Confirmed**, with the class boundary made precise in §3.2 (emission-time locality; off-run-cell exclusion worth documenting). |
| 3. δ is a residual, not a reduction | **Confirmed**; consumer docstrings consistent. |
| 4. The `sg` slot | **Confirmed**; defence and its game's-reads-only scope exactly as declared; priced by `Q`. |
| 5. Honest family `Index`-parameterized, no Lean witness | **Corrected.** The fixture evidence inhabits `Index` at `publicCount > 0`; `honestKimchiFamily` needs the `publicCount = 0` subclass, which has *neither* a Lean term *nor* fixture evidence — and Honest.lean's own section claims to have closed the loop while being empty (B-4). |
| 6. Modeled fragment = basic gate set | **Confirmed and augmented.** The fragment is *also* cut by (a) the SRS regime `nc·2^k = n` (excluding the deployed default) and (b) proof shape (no optional-gate/lookup evaluation fields). Both belong in this list. |
| 7. `snarky` outside the dead-code audit and this engagement | **Confirmed** (own gate, 5 roots, standard axioms). |
| 8. Locked-target gate is textual | **Confirmed**, and sharpened: it is textual *and* unwired (A-1), and covers only the IPA rung (A-3). |
| 9. Deleted prior art in git history | **Confirmed**; the internal statement-audit report was reviewed and cross-referenced (see below). |

**Missing from §7 — the augmentation this audit asks be adopted:**

1. **The internal audit's open Critical C2 (EndoMul order/sign) is not declared anywhere in the
   SoW.** A verified, still-open fidelity divergence in the modeled fragment is exactly what §7
   exists to record. (V-1.)
2. The infinity-point absorb divergence (V-2).
3. The SRS-regime restriction `hkn` (excludes the deployed default configuration).
4. The proof-shape clause (optional-gate/lookup evaluation fields).
5. `htpos` — a Tier-1 hypothesis with no production counterpart (B-1).
6. The setup-distribution idealisation (hash-derived SRS ⇒ uniform multiples of `B`).
7. The gate battery's actual composition: four gates unwired, four axiom gates rather than five,
   kernel replay push-only (A-1, A-5, A-6).
8. The executable's junk-division behaviour at the two excluded ζ points, and the
   deterministic-conjunction vs randomized-MSM difference (V-3, V-4).
9. **A correction rather than an addition:** §7 inherits, from the `Capstone` and IPA-headline
   docstrings, the claim that `Complete` makes the honest extractor call bound astronomical. That
   claim is not supported by the extractor's control flow (§4.8). The accurate declaration is that
   the extractor's cost is **unproved** — worst case `(2·|F|+1)^k`, table-averaged cost unbounded
   by any theorem here, and the conditional upstream tool unused. This is the only item in the
   accounting where the project describes itself as weaker than it has shown itself to be.

Other still-open internal findings re-verified as still accurate: **M4** (extended by B-1),
**M8** (A-9), **M9** (A-10), **M10** (bad-set binder placement at Tier 4 — unchanged; the
endpoint-level SZ layer is independently node-local and unaffected), **M11** (residue = W-F3).

---

## 7. Per-claim verdict table (deliverable 2)

**WF** well-formed / **AV** anti-vacuous / **SC** scope confirmed. ✓ = yes, ✓* = yes with a named
finding, ✗ = no.

### Tier 1

| Claim | WF | AV | SC | Justification |
|---|---|---|---|---|
| `vesta_kimchi_knowledge_sound` | ✓ | ✓* | ✓* | Quantifiers, measure, extraction predicate audited; anti-vacuity rests on the honest-family exhibits with the B-4 residue; scope true but under-presented (C-1), `htpos`-narrowed (B-1), docstring closure claim false (B-2). |
| `pallas_kimchi_knowledge_sound` | ✓ | ✓* | ✓* | Mirror; per-curve arithmetic discharged. |
| `ipa{Vesta,Pallas}_knowledge_sound` | ✓ | ✓ | ✓ | Same game one level down; the "four limits" docstring is a model of honest self-description; honest exhibits exist per curve at this layer. |
| `{vesta,pallas}_failure_measure_le` | ✓ | ✓ | ✓ | Assumption-free rungs, per curve, consumed by the capstones. |

### Tier 2

| Claim | WF | AV | SC | Justification |
|---|---|---|---|---|
| `kimchiVerify_eq_verifyWith` | ✓ | ✓ | **✗** | Named-reads form is right and the closure is clean — but its subject `kimchiVerify` diverges from the deployed algorithm on EndoMul rows (V-1) and on identity-point absorbs (V-2); docstring caveat stale (B-3). |
| `FSFaithful` + `wins_iff_kimchiVerify` | ✓ | ✓ | ✓ | Eight read equations, nothing else; base agreement by `rfl`; ROM enters here only. Scope is inherited from the verifier it bridges to (hence V-1/V-2 above, not here). |
| `Bulletproof.verify_reflects` + IPA sponge-source exhibits | ✓ | ✓ | ✓* | Cold/warm record correct and consistent with the kimchi warm-base design; V-2 applies to the shared sponge layer. |

### Tier 3

| Claim | WF | AV | SC | Justification |
|---|---|---|---|---|
| `honestKimchiFamily_wins` / `_failure_set` | ✓ | ✓* | ✓ | Closures standard; conditional on the missing `publicCount = 0` index (B-4). |
| IPA honest exhibits | ✓ | ✓ | ✓ | Present, per curve, unconditional at their layer. |
| `verifyWith_of_deferred_delta` | ✓ | ✓ | ✓ | The counterexample is real and locked; the reason commit-then-challenge is structural, not assumed. |
| `exists_ne_zero_kernel_scalarBasis` | ✓ | ✓ | ✓ | Binding refuted at the sampled basis; blocks any binding hypothesis in the ancestry. |
| sg-slot defence (5 results) | ✓ | ✓ | ✓ | Factorization + locality with honestly-stated scope. |
| `*_U_irrelevant`, `uRepresentationOfBreak`, `reductionEfficient_exists`, `derivedUDL_iff_residual_measure` | ✓ | ✓ | ✓ | Each does exactly its stated job; the last two are the self-limiting exhibits and both are accurate. |

### Tier 4

| Claim group | WF | AV | SC | Justification |
|---|---|---|---|---|
| Gate layer (`sound`/`complete`, `ok_iff`, per-curve entry points) | ✓ | ✓ | ✓* | Soundness concludes in Mathlib's group law, not a restatement of the constraints — the anti-pattern the SoW names is absent; completeness twins present. But the EndoMul *list order* consumed by the linearization diverges (V-1), and varBaseMul/endoMul rows are fixture-unexercised (C-3). |
| Arithmetization (`satisfies_iff_fullFamily_dvd`, permutation certificates) | ✓ | ✓ | ✓ | Single `Satisfies` chain; permutation row semantics fixture-pinned; M10 persists at this tier without affecting the endpoint-level discipline. |
| Executables (`kimchiVerify`, `Wire.*.check`, parsers, script roots) | ✓ | ✓ | **✗** | Parse layer faithful as catalogued (Appendix W) — but the verifier's EndoMul term and infinity absorb diverge (V-1, V-2), and the proof-shape clause is missing (C-2). |
| `pasta` trust base (13 roots) | ✓ | ✓ | ✓ | All theorems against CompElliptic certificates; constants independently re-derived (§2.4); certificate-scope prose needs A-9's correction. |

---

## 8. Consolidated findings register

| ID | Sev | Summary |
|---|---|---|
| **V-1** | **Critical** | EndoMul constraint list is a different permutation of production's with one sign flipped ⇒ `kimchiVerify` diverges on every EndoMul-bearing circuit. **Known internally (statement-audit C2), still open, absent from SoW §7.** |
| **V-2** | **Critical** | Infinity-point absorb encodes one zero where production encodes two ⇒ transcript divergence on identity commitments; honest path unaffected; one-line fix; fixtures structurally blind. |
| A-1 | High | Four gates (locked target, sorry census, extractor-computes, ironwood-generic) are wired into no automation. |
| A-2 | High | Axiom gates do not cover the Tier-2/3 statements — including every named faithfulness and anti-vacuity result. |
| C-1 | High | Modeled-fragment boundary (incl. the sub-SRS exclusion = deployed default) absent from every presentation surface. |
| B-1 | High | `htpos` excludes the production-accepted empty-`t_comm` shape; extends internal M4 to Tier 1. |
| A-8 | High | `native_decide` trust discriminated by a forgeable name prefix; the tree already authors declarations in the trusted namespace. |
| A-3 | Medium | Locked target pins the IPA rung only; kimchi endpoints, `Wins`, `ExtractsWitness`, `relationFinder` unpinned. |
| A-6 | Medium | Kernel replay does not recompute the axiom census and is push-to-main only. |
| A-7 | Medium | Fixture provenance unpinned in CI (this audit's regeneration closed the gap at this revision). |
| B-2 | Medium | Endpoint docstrings claim exactly-3-axiom closure; measured closure adds 3 CompElliptic certificates per curve. |
| B-3 | Medium | Stale warm/cold-base caveat contradicts the current game and Bridge.lean. |
| B-4 | Medium | Honest.lean promises a concrete-index exhibit in an empty section; §7.5's inhabitation evidence misses the needed subclass; no per-curve honest-family corollary. |
| C-2 | Medium | Production accepts fragment-VK proofs with optional-gate/lookup eval fields (transcript-affecting); undocumented proof-shape clause. |
| C-3 | Medium | Fixture gaps inside the fragment: no live EndoMul/VarBaseMul selector anywhere; `Corresponds` unwitnessed at nc = 8. |
| **E-1** | Medium | The extractor-efficiency story is **overstated as a limitation**: the docs infer an astronomical honest `R` from `Complete`'s `2^128` order lists, but losing tables cost exactly one run and the scan fires only on winning tables, so `ReductionEfficient` bounds the classical expected-forking quantity. Ironwood's conditional `ExpectedRuns.lean` bound (`(6/δ)^k` under fork spread) exists and is **unused by either package**; its averaging axis (tapes) differs from `ReductionEfficient`'s (tables). Closing this would restore ε's concrete-security reading; leaving it means the extractor's cost is unproved, not known-large. |
| A-5, A-9, A-10, A-11, A-12, A-13, A-4, V-3, W-F3, W-F4, C-4 | Low | Missing poseidon gate; vestigial `ofReduceBool` + broader inherited certificate set; `CLAUDE.md` documents a deleted axiom boundary; stale allowlist comment; `Columns.lean` claims nonexistent `rfl` theorems; `KimchiVK.endo` docstring names the wrong production derivation at the trap site; locked bytes changed in a lint commit; undeclared ζ-boundary junk division; `lr` pin presented as a production check; strengthening declaration under-enumerates; decoder hygiene. |
| V-4, A-14, A-15, B-5, B-6, D-1…D-4 | Info | Deterministic-conjunction vs randomized MSM; fixture-pinned sqrt signs; synthesized PS-driver shifts; `digest` self-policing; off-run-cell AGM note; no `Complete` witness term; SoW's `(2^k+1)` gloss; Bridge.lean §4 refers to deleted corollary statements; a surviving `unusedSectionVars` warning. |

---

## 9. Recommended order of work

1. **V-1** — reorder the EndoMul list to `[bool×4, window-1, window-2, D − n′, inv]`, un-negate the
   scalar-register constraint, and re-thread the positionally-indexed lemmas (`Holds` is
   order-insensitive, so gate soundness/completeness survive). Reconcile with which `endosclmul`
   version deployed Mina runs, per the internal audit's caveat.
2. **C-3 + V-1's mask** — add a `fixture-dump` circuit containing live EndoMul *and* VarBaseMul
   rows. That single fixture would have caught V-1 and will pin the fix; it also closes
   VarBaseMul's review-only alignment.
3. **V-2** — make `absorbG` branchless; add a sponge-trace shape
   `[absorb_g_inf, absorb_*, challenge]` so the fixture can see it.
4. **A-1** — wire the four gates into `lean.yml` (they pass today); **A-2** — extend the axiom
   gates' root lists to the Tier-2/3 statements; **A-5** — add the poseidon gate.
5. **C-1 / C-2 / B-1** — one paragraph in each endpoint docstring stating the fragment (gates, no
   recursion, no lookups, no optional gates, `nc·2^k = n`, non-empty quotient, no optional/lookup
   eval fields), and the same list into SoW §7.
6. **B-2, B-3, B-4, A-10, A-12, A-13** — documentation corrections; B-4 additionally wants the
   `publicCount = 0` index term the empty section promises.
7. **A-8** — replace the `native_decide` name-prefix test with an upstream-module or tier check.
8. **E-1** — the highest-value *upgrade* (as opposed to fix) available: plumb or restate ironwood's
   `ExpectedRuns.lean` bound onto `ReductionEfficient`'s averaging axis. Succeeding turns the
   endpoints from "knowledge soundness with an extractor of unproved cost" into a proof of
   knowledge with a stated extraction cost, and makes ε groundable in a generic-group bound. It
   also means the current docstrings understate the result, which is the rarer direction of error
   and worth correcting either way.

---

## Appendix W — wire-protocol identity and fragment delineation (C4/C5, full detail)

Verdict vocabulary: **faithful** / **narrows** (rejects production-legal data) / **widens**
(accepts production-illegal data) / **unmodeled-declared** / **unmodeled-UNdeclared**.
Lean paths relative to `formal/`; Rust relative to `mina/src/lib/crypto/proof-systems/`.

### W.1 `ProverProof` (proof.rs:144–194) vs `Wire.KimchiProof` + `KimchiProof.check`

| Production field | serde | Verify-time check | Lean field + check | Verdict |
|---|---|---|---|---|
| `commitments.w_comm: [PolyComm; 15]` | array 15; chunks `Vec<G>` unchecked | none — ragged chunks flow into the transcript and equations | `wComm : Vector (PolyComm C) wCols`; `check` pins every column to `nc` (Wire.lean:154) | **narrows — declared** (Wire.lean:146–151). Honest proofs are always `nc`-chunked; the excluded ragged adversarial proofs reach production's equations, whose rejection is "an argument, not a check" (self-declared) |
| `commitments.z_comm` | `Vec` unchecked | none | `zComm`; pinned to `nc` (Wire.lean:155) | **narrows — declared** |
| `commitments.t_comm` | `Vec` unchecked | `len > chunk_size*7 → Err IncorrectCommitmentLength` (verifier.rs:259–266) | `tComm : Array` + `tComm.size ≤ 7*nc` (Wire.lean:157) | **faithful** (exact complement; `Err` ↔ parse `none`) |
| `commitments.lookup: Option` | optional | for a lookup-free VK, **every** read is behind `lookup_index.is_some()` — never absorbed, never batched | absent | **unmodeled-declared**; presence is transcript-neutral for fragment VKs, so every production-accepted proof is acceptance-equivalent to its stripped twin. Benign |
| `proof: OpeningProof {lr, delta, z1, z2, sg}` | unchecked | **no length check anywhere**: oversized `lr` panics (ipa.rs:296, 313–319); undersized flows into the equations | `Ipa.Wire.Proof`; `check k` pins `lr.size = σ.k` (BWire.lean:324–329) | `delta/z1/z2/sg` **faithful**; `lr` pin **narrows — inadequately declared** (W-F3) |
| `evals.public: Option` | optional | length-checked when present; `Some` → use at any nc; `None ∧ chunk_size>1 → Err`; `None ∧ nc=1` → barycentric (verifier.rs:332–376) | `pubEvals : Option …` at proof level (flattening declared); `check` implements all three branches (Wire.lean:159–161); `PubEvalSrc` resolves precedence | **faithful** — all three branches, incl. carried-at-nc=1 |
| `evals.w / z / s / coefficients` | 15/–/6/15 serde-enforced | `check_proof_evals_len` at `chunk_size` (verifier.rs:678–709, called :831) | `Vector`s + `checkEvals` at `nc` (Wire.lean:128–139) | **faithful** |
| 6 basic selectors | required | length-checked; fr-absorbed | six named fields + chunk checks | **faithful** |
| 6 optional-gate selectors (`range_check0/1`, `foreign_field_add/mul`, `xor`, `rot`) | optional | length-checked when present; **fr-sponge absorbs them even for a VK without those gates** (plonk_sponge.rs:100–119); never batched; **never rejected** | absent | **unmodeled-declared** at gate level, but the proof-shape consequence is **UNdeclared** → C-2 |
| lookup evals + 5 lookup selectors | optional | same pattern (length-checked, fr-absorbed when present, batched only if `lookup_index`) | absent | **unmodeled-declared**, same C-2 caveat |
| `ft_eval1` | scalar | absorbed (:382) | `ftEval1` | **faithful** |
| `prev_challenges: Vec<RecursionChallenge>` | unchecked `Vec` | `to_batch` rejects `len ≠ vk.prev_challenges` (verifier.rs:810–815) | field absent; the constant empty-list fr-digest absorb **is** transcribed (Kimchi.lean:31–33, `frOracles`:272) | **unmodeled-declared, language-EQUAL in fragment**: at `vk.prev_challenges = 0` production *rejects* exactly the proofs Lean cannot represent. The only silent path is the JSON decoder dropping unknown keys (C-4) |

### W.2 `VerifierIndex` vs `Wire.KimchiVK` + `KimchiVK.check`

| Production field | Lean | Verdict |
|---|---|---|
| `domain` (serialized with derived values) | `domainLog2` + `omega`; derived values recomputed | **faithful** for production data (radix-2 domains are two-powers); decoder truncates a non-two-power `n` (C-4) |
| `max_poly_size` | not in the VK; pinned to `2^σ.k` by the client composition (`parseSRSAt`, `runNc`) | **faithful under the SRS pin**; the sub-SRS branch (`d1 < max_poly_size → chunk_size = 1`) is **out of scope, declared**, and excluded at the endpoints by `hkn` |
| `zk_rows` | `zkRows : ℕ` data | **faithful** (data both sides) |
| `srs` (`serde(skip)`) | separate `σ` argument | **faithful** |
| `public` (**serialized**) | absent; `to_batch`'s exact-count pin replaced by two bounds | **widens — declared**, closed at the endpoints by `hpub` |
| `prev_challenges` (**serialized**) | absent — fragment pins 0 | **unmodeled-declared** (see W.1) |
| `sigma_comm[7]`, `coefficients_comm[15]`, 6 selector comms | fixed dimensions + per-column `nc`-chunk pins | **narrows — under-declared** (W-F4): production never chunk-checks VK commitments; the in-file strengthening declaration names only `w_comm`/`z_comm`. Honest keys are uniform, so nothing real is rejected. `psm_comm → poseidonComm` rename declared and decoder-handled |
| optional gate comms | absent | **unmodeled-declared**; any `Some` alters the digest and the batch — unrepresentable, consistent with the boundary |
| `shift[7]` | `Vector _ permCols` | **faithful** |
| `permutation_vanishing_polynomial_m`, `w` (`serde(skip)`) | recomputed closed-form | **faithful** |
| `endo` (`serde(skip)`, recomputed) | wire **input**, pinned at the endpoints by `Corresponds` | **unmodeled-declared / widens executable-level, closed at endpoints** |
| `lookup_index: Option` | absent | **unmodeled-declared**; also removes the joint-combiner squeeze — consistently absent both sides for fragment keys |
| `linearization`, `powers_of_alpha` (`serde(skip)`) | basic-gate closed forms; `index_terms` empty (a production **assert**) | **faithful within fragment** |
| `VerifierIndex::digest()` (computed) | wire **input**; adversary data at the endpoints | **unmodeled-declared** deferral; strengthens the modeled adversary, so soundness transfers a fortiori |
| Lagrange basis (computed from SRS) | wire data, chunk-validated in full; public region pinned by `Corresponds` | **unmodeled-declared** model input, closed at the endpoints |

Legacy-field note: the pinned `PolyComm` is `chunks: Vec<G>` only; the `unshifted`/`shifted` split
survives solely in the OCaml FFI conversion, which asserts `shifted = None`. No legacy field is on
the native wire. **Confirmed.** The `VerifyError` enum was walked end to end: every remaining
variant (`LookupCommitmentMissing`, `IncorrectRuntimeProof`, `LookupEvalsMissing`,
`MissingEvaluation`, `MissingCommitment`, `DifferentSRS`, `SRSTooSmall`) is unreachable for
fragment keys or vacuous for a single proof.

### W.3 Corruption-test inventory (`check_kimchi_verifier.lean`)

Five fixture runs (nc=1 barycentric, nc=1 carried, nc=2 Vesta, nc=2 Pallas, nc=8 heavy). Each
asserts the unmodified proof ACCEPTS and that `evals_public` presence matches expectation, then
runs two matrices; any unexpected verdict throws.

*Verify-level (must still parse; verdict must flip to REJECT):* (1) `t_comm` chunk `7·nc−1`
`+= σ.h` — the second `ft_comm` collapse group, run at every `nc > 1` **including heavy**, guarded
by a full-quotient precondition so it is not a no-op; (2) `z` eval ζ chunk 0; (3) `t_comm` chunk 0;
(4) `ft_eval1`; (5) at nc>1, `z` eval ζ chunk 1, `z` eval ζω chunk 0, `w[0]` eval ζ chunk 1;
(6) carried-only public eval ζ chunk 0, explicitly skipped with a notice at barycentric nc=1.
Items 2–6 are skipped under heavy; item 1 keeps that run non-vacuous.

*Parse rejections (`check` must return `none`):* (7) ragged `z` eval chunk vector — also driven
through `verifyWire` to exercise the `none → false` composition; (8) oversized `t_comm`;
(9) wrong opening round count; (10) ragged VK chunk vector (`sigma_comm[0]`); (11) at nc>1,
missing `evals_public`.

*Not covered here:* no verify-level VK corruption; no opening-field corruption (covered at the IPA
level); no corruption of `s`/`coefficients`/selector evals; no corrupted `public`, `digest`,
`omega`, `shifts`, `zkRows`, `endo`; no wrong-`nc` parse attempt; no raw-JSON malformation (the
matrices mutate decoded records, not bytes).

### W.4 The fragment statement (C5)

**The endpoints govern exactly:** single (unbatched) kimchi proofs over the Pasta curves — both
instantiated — for circuits representable as a `Kimchi.Index`: gate types drawn from
**{zero, generic, poseidon, completeAdd, varBaseMul, endoMul, endoScalar}**, with kimchi's
public-input gadget layout (first `publicCount` rows are `Pub`-coefficient generic gates), a
power-of-two domain of size `n`, `zkRows ≥ 3` mask rows that are gate-free and identity-wired, no
two-row gate at the mask boundary, and wiring that never crosses the mask (the last two are
model-side structural conditions slightly stronger than anything production enforces, decided on
production data by `build?`). The verifying key must be the honest chunked indexer's output for
that circuit (`Corresponds`: committed columns, `omega`, `zkRows`, `shifts`, `endo`, MDS, and the
Lagrange basis over the public region), with public arity pinned (`hpub`), `prev_challenges = 0`,
`lookup_index = None`, and every optional-gate commitment `None`. The proof must carry **no**
lookup commitments, **no** optional-gate or lookup evaluation fields, and **no** `prev_challenges`;
uniformly `nc`-chunked commitments; an opening of exactly `σ.k` rounds; a non-empty quotient
commitment (`htpos`); carried public evaluations required at `nc > 1`, carried-or-barycentric at
`nc = 1`. Chunking regimes: `nc = n / 2^σ.k` for any power of two with `2^σ.k ≤ n` (`hkn`,
`hnc`), fixtures at `nc ∈ {1, 2, 8}` with `zkRows ∈ {3, 5, 19}` — production's `nc`-dependent
values, carried as data, are inside the model. **Excluded** (production `GateType` residue):
`Lookup`, `RangeCheck0/1`, `ForeignFieldAdd/Mul`, `Xor16`, `Rot64`, the four dead Cairo types; all
lookup machinery; recursion; and the **sub-SRS regime** `max_poly_size > n` — the common
o1js/Mina configuration. Mina/pickles proofs use recursion, lookups, optional gates, and the
sub-SRS regime, and are therefore outside the fragment on four axes simultaneously.

*Inside-the-boundary check:* the joint-combiner squeeze is consistently absent both sides for
fragment keys; runtime tables are lookup-only; `zk_rows > 3` is modeled as data and
fixture-exercised at 5 and 19; chunked sigma/coefficient/selector commitments are modeled and
value-adjudicated at nc ∈ {1,2}; the empty-recursion constant fr-absorb is transcribed. The one
genuine inside-looking gap is C-2's proof-shape condition.

### W.5 Documentation coverage

*Stated at:* `Kimchi.lean:30–48` (the canonical scope block — no lookups, no recursion, digest an
input, empty `index_terms`, sub-SRS out of scope, public-count substitution); `Wire.lean:45–46`;
`Kimchi.lean:69–73`; `Idx/Basic.lean:39–40`; `docs/chunking-plan.md` non-goals;
`docs/statement-audit-report.md` D6 (historical).

*Not stated at:* the Tier-1 endpoint docstrings, the `KnowledgeSoundness.lean` module preamble,
and all five `Forking/*` preambles. `formal/CLAUDE.md` describes the library as "the kimchi custom
EC gates (AddComplete, VarBaseMul, EndoMul, EndoScalar, Generic)" — omitting Poseidon — and never
says pickles/Mina proofs are out of scope. No package READMEs exist. → **C-1**.

### W.6 Stream findings

* **W-F3 (Low)** — the opening `lr` round-count pin has no production counterpart: `SRS::verify`
  never checks `lr.len()`; oversized panics, and an undersized `lr` with a claim committed over the
  SRS prefix is **accepted**. BWire.lean:29–32's "a mis-shaped claim reaches the same rejection
  through the equations it then fails" is false for this corner. In the kimchi composition,
  exploiting it against a `Corresponds`-satisfying VK needs a DL break, so endpoint exposure is
  priced. (M11 residue.)
* **W-F4 (Low)** — the strengthening declaration covers `w_comm`/`z_comm` but not the VK-side
  chunk pins that `KimchiVK.check` equally applies.
* **C-4 / W-F6 (Low/Info)** — decoder hygiene: unknown-key dropping (an out-of-fragment payload
  parses-and-drops rather than being rejected — acceptance is then unreachable via transcript
  divergence, but the parse gives no out-of-fragment signal); `parseZMod` reduces non-canonical
  numerals mod p where arkworks rejects `≥ p`; `Nat.log2` truncation; `parseComm` rejects empty
  chunk arrays that serde accepts; `runNc`'s `Nat` subtraction returns 1 when `σ.k > domainLog2`,
  making the driver-resident guard load-bearing.
* **Confirmed positives** — the `t_comm` bound, the eval-length sweep, the `evals_public`
  tri-state; `prev_challenges` language-equality; the declared widenings all closed at the
  endpoints; the `psm_comm` rename; no legacy `shifted`; dimensions 15/7/6/15 = `COLUMNS`/
  `PERMUTS`/`PERMUTS−1`/`COLUMNS`; the Lean `GateType` is exactly the declared six plus `zero`;
  and the corruption matrices genuinely pin the chunk-level degrees of freedom across both curves
  and `nc ∈ {1,2,8}`.

---

## Addendum — verification of the remediation (2026-07-28, post-`5bea7d60`)

The project's response is `docs/external-audit-response.md`, covering commits
`4ff807a6 … 5bea7d60`. This addendum records what the auditors **re-verified independently**
against the remediated tree, rather than accepting from the response.

**Both Criticals are genuinely closed, and closed at the right layer.**

* **V-1.** `Gate/EndoMul.lean`'s list now reads `[bool b₁..b₄, window-1, window-2,
  (16n+8b₁+4b₂+2b₃+b₄) − n′, inv]` — position-for-position `endosclmul.rs:524–549`, with
  production's scalar-register sign. Verified by direct comparison of both sources.
* **V-2.** `FqSponge.absorbG` is `absorbFq spec s [P.x, P.y]`, branchless. Verified.
* **The masks that hid them are closed by production-generated fixtures, not by assertion.**
  `kimchi_proof_vesta_emul.json` is emitted by a new dumper (`kimchi_proof_dump_emul.rs`); it
  carries **NONZERO** `evals_emul_selector` and `evals_mul_selector` (independently checked — every
  pre-existing fixture has both identically zero), is run by `check_kimchi_verifier.lean:183`, and
  ACCEPTS under the fixed verifier. Its `public: []` also exercises the empty-public-input branch.
  Both curves' `fq_sponge` fixtures now contain the exact shape this report specified as the only
  discriminating one, `[absorb_g_inf, absorb_fr, challenge]`, plus a longer variant.

**Gate battery, re-run end to end on the remediated tree.** Axiom gates green at kimchi **52**,
bulletproof-pcs **30**, poseidon **19** (new), pasta 13, snarky 5; both locked-target gates green
(the new kimchi one pins both endpoints, `Wins`, `ExtractsWitness`, `relationFinder`, the
faithfulness bundle and both honest exhibits); sorry census green with the widened scope
(`KimchiFixture`, `BulletproofFixture`, every `scripts/` dir, `expected=''`); dead code 0 of 1545;
fixture manifest green (31 files, `mina 3969f761846e`); all fixture drivers green.

**CI wiring confirmed by reading `lean.yml`.** All four previously-unwired gates now run
(`check_locked_target.sh` ×2 pre-build, `check_sorry_census.sh`, `check_extractor_computes.lean`,
`check_ironwood_generic.lean`), plus the poseidon axiom gate and `check_fixtures_manifest.sh`.
Kernel replay carries no `if:` guard and its comment records the PR-coverage fix; there are no
conditional guards anywhere in the workflow.

**Independent regeneration.** Rebuilding `tools/fixture-dump` against the pinned submodule and
re-running all nine dumpers reproduces **every** committed fixture byte-for-byte, including the two
new ones (only the committed `.gitignore` and the two documented gitignored debug sidecars differ).
The A-7 manifest is therefore consistent with what production actually emits, not merely with
itself.

**Spot checks on the remaining dispositions**, all confirmed present and rooted:
`vesta/pallas_honest_extraction_failure_measure_le` (`Honest.lean:1767`, `:1790`, in both
`roots.txt` and the axiom gate); `identityTape` / `exists_complete_coins` (`Deployed.lean:861`,
`:867`, rooted); module-based `native_decide` trust via `env.getModuleFor?` against
`CompElliptic.*` or `Pasta.Endo`; `guard (0 < p.tComm.size)` in `Wire.lean` with a matching driver
rejection case; the four `Columns.lean` derivation `rfl`s; the E-1 prose replacement and the `hEff`
sentence at both endpoints; the fragment statement at the module preamble, both endpoint
docstrings, and `formal/CLAUDE.md`.

**B-4's account is truthful and the underlying incident is worth recording.** `git show e7c431b2`
confirms the dead-code sweep deleted 983 lines from `Honest.lean`, including the concrete-index
blocks — so the empty section was a regression, not an unwritten promise. The remediation's fix
(rooting the exhibits and gating them) is the correct one, but the *class* of risk generalizes:
under a dead=0 gate, any exhibit absent from `roots.txt` is by construction eligible for deletion,
and nothing but review distinguishes an anti-vacuity certificate from dead code.

### Residual findings

* **R-1 (Low) — C-3 is only partly closed at the scalar layer.** `linearization_vesta.json` is
  unchanged (it regenerates byte-identical) and still carries `gate_combined.endoMul = "0"` and
  `varBaseMul = "0"`, so `check_linearization`'s per-gate checks for exactly the two gates V-1
  concerned remain **vacuous** (`0 = 0`). Coverage for V-1 now rests entirely on the end-to-end
  emul proof, which is sufficient to catch a regression but reports it as a whole-proof rejection
  rather than localizing it to a gate and constraint index. The emul circuit's dumper already
  exists; emitting a second linearization fixture from it is cheap and would restore
  gate-by-gate adjudication.
* **R-2 (Info) — the one-time negative controls are prose.** That the pre-fix verifier rejects the
  emul fixture, and that a one-zero `absorbG` fails the new sponge case, are reported but not
  replayable from the tree. The standing controls are the fixtures themselves, which is the right
  design; the one-time discrimination checks are simply unrecorded. Structurally both hold: the
  emul fixture's acceptance depends on `ftEval0`, which consumes the gate linearization
  positionally.
* **R-3 (Info) — two unnumbered §2.1 observations remain open**, fairly, since they were never
  numbered findings: PR runs are filtered to pull requests *targeting `main`*, so a stacked PR onto
  a feature branch still runs no Lean gate; and `setup-lean` runs `lake update mathlib` at CI time
  rather than building from the committed `lake-manifest.json`.

### Verdict

Fourteen of the report's findings are fixed and independently verified; three are deferred with
recorded sign-off (E-1's upgrade, B-1's strong form, V-4) and one accepted as a tool residual
(A-6's second half). No fix introduced a statement change: `Gate.EndoMul.constraints` is a
definitional edit that leaves every `Holds`-based statement semantically unchanged (`Holds` is
∀-over-the-list, and `e = 0 ↔ −e = 0`) while deliberately changing the linearization *value* —
which is the fix. The deferrals are the honest ones: each is real proof work, each is stated as
open rather than closed, and E-1 in particular is left with the upstream tool cited at the point
where the work would begin.

### Follow-up round — verification of `c49054e4`

All three residuals of the addendum are closed, and the B-4 generalization was taken up rather
than noted. Re-verified independently:

* **R-1 — closed, and better than specified.** `linearization_vesta_emul.json` (emitted by the
  refactored `linearization_dump`) carries **LIVE** `endoMul` and `varBaseMul` targets — the two
  that were `0 = 0` — while the historical fixture keeps the other four, so every gate is live in
  at least one fixture. Two additions beyond the ask: the driver **fails** if a gate named in a
  fixture's `liveGates` has a zero target (`check_linearization.lean:120–126`), and zero targets
  are annotated `(0)` in the driver's own output, so a vacuous check now *reads* as vacuous
  (observed: `varBaseMul: ✓ (0), endoMul: ✓ (0)` on the mixed fixture, un-annotated on the emul
  one). The Rust refactor that shares the circuit between dumpers threads the prover's rng rather
  than reseeding, and the claim that this leaves the historical fixture untouched was checked the
  hard way: a full rebuild and regeneration of all nine dumpers reproduces **every** committed
  fixture byte-for-byte; the manifest gate is green at 32 files.
* **R-2 — closed.** `docs/negative-controls.md` records four controls (NC-1 end-to-end V-1, NC-2
  gate-localized V-1, NC-3 the V-2 trace shape, NC-4 the exhibit guards) with the exact mutation,
  the observed failure, and a replay convention. **NC-4 was replayed by the auditors**: renaming
  `chainAt_sg` produces `✗ EXHIBIT MISSING: chainAt_sg` and **exit 1**; restoring gives exit 0.
  The file's closing section, distinguishing self-discriminating structural gates from
  data-driven ones that need controls, is the right scoping and is accurate.
* **R-3 — closed by fixing, not accepting.** The `pull_request` branch filter is removed, so a
  stacked PR touching `formal/` is gated whatever its base; and `lake update mathlib` is replaced
  by a cache restore from the committed `lake-manifest.json`, with a fallback that re-resolves
  **and emits a `::warning::` saying the run is not on the committed pin** — drift becomes visible
  in the log instead of silent.
* **The B-4 generalization was implemented.** Both locked-target gates now pin the *existence* of
  the whole exhibit set — 20 in bulletproof-pcs, 6 in kimchi — with the rationale and the
  `e7c431b2` precedent recorded in the script header. This closes the class, not the instance:
  rooting protects an exhibit only while it stays rooted, whereas a sweep removing root and
  declaration together was previously green.

The auditors' report was committed unmodified (additive only; no deletions).

**Closing verdict.** Every finding this engagement raised is now either fixed and independently
verified, or deferred with a recorded rationale and the remaining work identified. The three
standing deferrals are E-1's upgrade (a proved extractor-cost bound — the substantive open item,
with ironwood's `ExpectedRuns.lean` cited at the point where the work begins), B-1's strong form
(discharging `t := 0`), and V-4 (the deterministic-conjunction modelling choice). No fix altered a
statement's meaning; the one definitional edit, `Gate.EndoMul.constraints`, leaves every
`Holds`-based theorem semantically unchanged while deliberately correcting the linearization value.
