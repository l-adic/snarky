# Response to the External Audit — Remediation Report

**To:** the auditing firm, in response to `docs/external-audit-report.md` (2026-07-28)
**From:** the `l-adic/snarky` project, `formal/` subtree
**Remediation revisions:** `4ff807a6` … HEAD on `kimchi-knowledge-soundness` (six commits,
one per work phase; each commit message carries the finding IDs it addresses)
**Baseline audited:** `2c8c57cc`

This document states, per finding, what we modified to accommodate the report — and, for
the three items we are deferring with the project owner's sign-off, exactly what remains
open and why. Findings are grouped by the report's own severity order. Where a fix changed
something the audit relied on (a pinned statement's spelling, a gate's root count), the
change is called out explicitly.

---

## 1. Critical findings — both fixed, both now fixture-pinned

### V-1 — EndoMul constraint order and sign (= internal C2)

**Fixed** (`4ff807a6`). `Gate.EndoMul.constraints` now lists the twelve expressions in
production's order — booleanity ×4, window-1, window-2, scalar register, distinct-point —
with production's scalar-register sign (`(16n + 8b₁ + 4b₂ + 2b₃ + b₄) − n′`). As the
report predicted, gate soundness/completeness survived untouched (`Holds` is
order-insensitive); `holds_iff` keeps its readable conjunction order with a shuffled
proof, so no downstream soundness proof changed. The version-reconciliation caveat is
resolved: the pinned proof-systems (`3969f761`) already carries the merged endomul
soundness fix, so the deployed order is unambiguous and it is the one now transcribed.

**And pinned** (`de76e2a8`): a new fixture, `kimchi_proof_vesta_emul.json` — a
production-accepted proof over a circuit with **live EndoMul and VarBaseMul rows**
(witnesses from production's own `gen_witness` helpers) — closes the mask that let this
divergence survive under green CI, and converts VarBaseMul's alignment from
review-evidence to fixture-evidence. **Negative control performed and recorded:** the
pre-fix verifier REJECTS this proof while accepting every previously committed fixture;
the fixed verifier accepts all.

### V-2 — the infinity-point absorb

**Fixed** (`4ff807a6`). `FqSponge.absorbG` is branchless — `[P.x, P.y]` unconditionally.
The identity is the `(0, 0)` sentinel by construction, so this reproduces production's
two-zero absorb exactly; the docstring that falsely claimed parity, and a stale module
preamble sentence, were corrected. Two `Transcript.lean` bridge proofs were re-proved
around the now-unblocked reduction (named-step equality via scrutinee destructuring).

**And pinned** (`de76e2a8`): the sponge-trace fixtures gain the shape
`[absorb_g_inf, absorb_fr, challenge]` — the one shape class that distinguishes the
two-zero from a one-zero encoding, per the report's own analysis of why the existing
traces were structurally blind. **Negative control performed:** the one-zero `absorbG`
fails exactly this case.

The new emul fixture also exercises identity-point commitments on the wire (the unused
columns' zero-polynomial commitments), encoded as the `(0, 0)` sentinel.

---

## 2. High findings

### A-1 — four gates wired into no automation

**Fixed** (`ab8f00e7`). All four are now `lean.yml` steps: both locked-target checks and
the sorry census run pre-build (pure source checks); `check_extractor_computes.sh` and
`check_ironwood_generic.sh` run with the fixture drivers. The census's scope gap the
report noted in passing is also closed: it now covers the fixture-decoding libraries and
every `scripts/` driver (with prose mentions of the word filtered; a planted `sorry` was
verified to fail the gate).

### A-2 — axiom gates blind to the Tier-2/3 surface

**Fixed** (`ab8f00e7`, `0fc479e9`). The kimchi gate grew from 39 to **52** roots: the
faithfulness layer (`kimchiVerify_eq_verifyWith`, `wins_iff_kimchiVerify`), the named
anti-vacuity exhibits (`honestKimchiFamily_failure_set`,
`exists_ne_zero_kernel_scalarBasis`, the per-curve honest corollaries of B-4), and the
seven REVISIT AGM lemmas. bulletproof-pcs grew to **30** (adding
`verifyWith_of_deferred_delta` and the D-2 witness). A `sorry` or stray axiom anywhere in
the named exhibit surface now fails the wired battery.

### C-1 — the modeled-fragment boundary absent from presentation surfaces

**Fixed** (`847a20d7`). The canonical fragment statement — condensed from the report's own
Appendix W.4 — now lives in the `KnowledgeSoundness.lean` module preamble; both endpoint
docstrings carry the compact form (explicitly including the sub-SRS exclusion, i.e. that
the deployed o1js/Mina default configuration is outside, and that Mina/pickles proofs are
outside on four axes); and `formal/CLAUDE.md`'s opening paragraph states the boundary.
The proof-shape clause (C-2) is part of the same statement everywhere it appears.

### B-1 — `htpos` excludes a production-accepted shape

**Fixed at the boundary, deferred in the strong form** (see §5). Of the report's three
offered remedies we adopted two: the wire parse now **rejects an empty quotient
commitment** (a declared strengthening, documented beside the existing `w_comm`/`z_comm`
declaration, with a parse-rejection case in the driver matrix), and the restriction is
carried in the fragment statement at every surface. The third remedy — removing `htpos`
and discharging the degenerate `t := 0` case through the run-soundness chain — is real
proof work and is deferred with sign-off (§5.2).

### A-8 — forgeable `native_decide` name-prefix trust

**Fixed** (`ab8f00e7`). All four gates (and the new poseidon gate) now discriminate by
**defining module** — `env.getModuleFor?` must return an upstream `CompElliptic.*` module
or `Pasta.Endo`, the one tree file declared to hold the two eigenvalue anchors. A
tree-local `native_decide` inside a `namespace CompElliptic` block no longer passes,
because tree files keep their own module names regardless of the namespaces they open.

---

## 3. Medium findings

| ID | Disposition |
|---|---|
| A-3 | **Fixed.** A kimchi-side locked-target gate (`kimchi/scripts/check_locked_target.sh`, 67 pinned lines) pins both endpoint statements, `Wins`, `ExtractsWitness`, and `relationFinder`; the `noncomputable` asymmetry the report flagged is documented in its header (the computability guard lives on the IPA extractor underneath plus the behavioural check). CI-wired. |
| A-6 | **Fixed** (kernel replay now runs on PRs) with the census-vs-replay division of labor documented at the CI step. The residual — lean4checker not recomputing the axiom tables — is accepted as inherent to the tool, per the owner's direction. |
| A-7 | **Fixed.** `scripts/fixtures.sha256` pins every committed fixture (31 files) by hash and records the proof-systems revision (`mina @3969f761`); a CI step verifies hashes and completeness. Regeneration remains a bump-time action with a `--regen` re-pin, per the dump README. |
| B-2 | **Fixed.** The endpoint docstrings now state the measured closure: the three standard axioms plus CompElliptic's certified `native_decide` witnesses per curve. |
| B-3 | **Fixed.** The stale cold-base caveat is rewritten to the current fact: the game evaluates at the warm base and `Bridge.lean` closes the slot identity by `rfl`. |
| B-4 | **Fixed, and the loop genuinely closed.** The empty "Non-vacuity of the family itself" section was a dead-code-sweep regression on our side (the blocks existed, unreferenced, one commit earlier); they are restored, and the loop is now closed AND rooted: `vesta/pallas_honest_extraction_failure_measure_le` — a concrete four-row index at `publicCount = 0` on each curve, with the honest family and its failure-set corollary — join `roots.txt` and the axiom gate, so the honest-family layer has its per-curve corollaries and a sweep can never take them again. This also resolves the report's C-6 residue. |
| C-2 | **Fixed** as part of the fragment statement (the proof-shape clause appears at every surface C-1 covers). |
| C-3 | **Fixed.** Three coverage additions: the live-EndoMul/VarBaseMul proof (above), `Corresponds` adjudicated at `nc = 8` (`index_vesta_nc8.json`; 28 columns × 8 chunks, all match), and the empty-public-input branch exercised by the emul fixture (which has `public_count = 0`). All pre-existing fixtures regenerate byte-identical. |
| E-1 | **Prose adopted in full; the upgrade deferred** (§5.1). The three overclaiming passages are replaced by the report's corrected account — the extractor's cost is *unproved*, not known-large — and both kimchi endpoints now carry the `hEff` sentence. We accept the report's characterization that this was the one place the development described itself as weaker than shown. |

## 4. Low / Info findings

All addressed (`ab8f00e7`, `a739a64d`):

* **A-5**: the poseidon package has its own axiom gate (19 roots — the duplex automaton,
  the FqSponge op surface the ROM idealisation concerns, the per-curve specs, SvdW),
  CI-wired; "axiom gates ×5" is now true by count (six with snarky).
* **A-9**: the vestigial `Lean.ofReduceBool` allowlist entries are gone; the gate prose
  now describes the real inherited certificate set (primality, point-count, sqrt-order,
  eigen anchors; compiler trust through `Lean.trustCompiler`).
* **A-10**: `formal/CLAUDE.md`'s axiom-boundary section — which documented the deleted
  `CMCurve`/`Cycle` free-axiom design — is rewritten to the zero-axiom reality, along
  with the deleted `Circuit`/`Cycle` layer structure the guide still described.
* **A-11**: the dead Fiat–Shamir comment block in the kimchi allowlist is gone.
* **A-12**: the four derivation `rfl` checks `Columns.lean` claimed now exist.
* **A-13**: the endo comment at the trap site now names the correct production
  derivation (`G::other_curve_endo() = endos::<OtherG>().0`).
* **A-4**: the lock-regeneration policy (isolated commit quoting the statement diff) is
  recorded in `docs/locked-target.md`. We note the episode the report identified
  (`2c8c57cc`) as the motivating instance.
* **V-3 / V-4**: the ζ-boundary junk-division divergence and the
  deterministic-conjunction / singleton-`batch_verify` differences join the declared
  deviation list in `Verifier/Kimchi.lean`'s preamble.
* **W-F3**: the false "reaches the same rejection through the equations" claim about the
  `lr` pin is corrected — the undersized-`lr` corner is production-accepted; the pin is a
  declared strengthening with its endpoint exposure priced by DL.
* **W-F4**: the strengthening declaration now names the VK-side chunk pins.
* **C-4**: `parseZMod` now **rejects** non-canonical numerals (aligned with arkworks
  serde — the one decoder-hygiene item where behavior changed); unknown-key dropping,
  the `log2` truncation, and the `runNc` underflow guard are documented at their sites.
* **A-14 / A-15**: the fixture-pinned SvdW sqrt sign and the PS-driver's synthesized
  shifts are documented at their sites.
* **B-5 / B-6**: `digest` self-policing and `hrepPrefix`'s off-run-cell AGM boundary are
  documented at their fields.
* **D-1**: the surviving `unusedSectionVars` warnings are fixed (three, once the
  A-2-widened builds surfaced two more of the same kind).
* **D-2**: `coins.Complete` has a closed in-tree witness: `identityTape` with
  `exists_complete_coins`, rooted and gated.
* **D-4**: `Bridge.lean`'s empty "§4" block, narrating the deleted locus-intersected
  corollaries, is removed.
* **D-3**: acknowledged as a SoW error, corrected here rather than by editing the
  engaged SoW: the `(2^k + 1)` factor is `Fintype.card (SetupIndex (2^k))` — the number
  of setup slots the DL challenge can be planted in — not "the fork's arity".

---

## 5. Deferred items (deferred with the project owner's explicit sign-off)

### 5.1 E-1, the upgrade: a proved extractor-cost bound

Plumbing ironwood's `ExpectedRuns.lean` bound (`E[runs] ≤ (6/δ)^k` under a fork-spread
floor) onto `ReductionEfficient`'s averaging axis is, as the report says, real work on a
different averaging axis (tapes vs tables), not plumbing. It is deferred to its own work
arc. What we adopted now is the full prose correction, so the development's self-account
is the audited one: worst case `(2·|F|+1)^k` proved; table-averaged cost unproved;
upstream's conditional tool identified and cited at the point where the work would start.
We accept the report's framing that closing this would restore ε's concrete-security
reading, and that the current state means ε is assumed for the finder rather than derived
from a time bound — both endpoint docstrings now say so.

### 5.2 B-1, the strong form: discharging `t := 0`

Removing `htpos` and proving the degenerate empty-quotient case through the
run-soundness chain is deferred. The adopted remedies (wire-boundary rejection as a
declared strengthening + the restriction carried at every presentation surface) mean the
hypothesis is now visible wherever the results are quoted, and the checked wire language
matches it. The attack shape the report's C2 log lists as #7 therefore remains a scope
boundary — now a *declared* one — rather than a priced one.

### 5.3 V-4, the modelling choice: deterministic conjunction

We keep the two bracket equations as a deterministic conjunction rather than modeling
production's rng-weighted MSM. Lean-accept implies production-accept with probability 1 —
the conservative direction for soundness — and the difference is now a *declared*
deviation with the report's own one-sentence characterization, alongside the
singleton-`batch_verify` note. No further work is planned here.

Two report items were, per the owner, closed as accepted residuals rather than worked:
the kernel-replay/census division of labor (A-6's second half, documented at the CI
step), and nothing else.

---

## 6. Changes to things the audit itself relied on

So the auditors can re-baseline quickly:

* **Gate root counts changed**: kimchi 39 → 52; bulletproof-pcs 28 → 30; poseidon 0 → 19
  (new gate); pasta and snarky unchanged (13, 5). All green at HEAD.
* **The kimchi gate's allowed list** is now `[propext, Classical.choice, Quot.sound]`
  with certified `native_decide` accepted by defining module (A-8/A-9); the printed gate
  output changed accordingly.
* **New pinned surfaces**: `kimchi/scripts/locked_target.expected` (67 lines);
  `scripts/fixtures.sha256` (31 files at `mina @3969f761`).
* **Fixture set changed**: + `kimchi_proof_vesta_emul.json`, + `index_vesta_nc8.json`,
  and the two fq-sponge trace files gained one case each (the V-2 probe). Everything
  else regenerates byte-identical, re-verified after the Rust-side changes.
* **`parseZMod` is stricter** (rejects ≥ p), matching arkworks serde.
* **One statement-adjacent change**: none of the pinned statement texts changed in this
  remediation. (The `Coins` re-spelling the report examined in A-4 predates it and is
  unchanged.)
* **The SoW is committed verbatim as engaged** (`docs/external-audit-sow.md`); its §7
  omissions and the §B6 gloss are corrected by this response and by the in-tree
  documentation, not by editing the engaged document.

## 7. The §7 accounting, as adopted

The report's nine-item augmentation of the SoW's self-declared list is adopted wholesale
into the in-tree documentation: V-1 and V-2 (now fixed and fixture-pinned, recorded in
the commit history and this response); the SRS-regime restriction, the proof-shape
clause, and `htpos` (all now part of the fragment statement at every surface); the
setup-distribution idealisation (stated in the module preamble's game description); the
gate battery's actual composition (now matching its description — the four gates wired,
five package axiom gates, kernel replay on PRs); the executable's ζ-boundary and
MSM-conjunction deviations (declared); and the E-1 correction (the extractor's cost is
unproved — the one item where the accounting now claims *less* than before, in the
accurate direction).

We thank the firm for the report's precision — in particular for V-1's independent
verification with the α-weighting argument, for the control-flow analysis behind E-1,
and for the attack log, three entries of which (#7, #11, #16) are now either priced,
declared at every surface, or fixed.
