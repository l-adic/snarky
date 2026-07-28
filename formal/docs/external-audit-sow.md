# Statement of Work — External Audit of the `formal/` Verification Stack

**Client:** the `l-adic/snarky` project, `formal/` subtree
**Subject revision:** branch `kimchi-knowledge-soundness` at `92a0fb7f` (PR #280)
**Date:** 2026-07-28
**Audience:** a formal-methods and security firm engaged to audit (1) the structure of the
Lean development, (2) the **well-formedness** of its top-level statements — do they express
the properties that need to be proven — and (3) their **anti-vacuity** — does the codebase
demonstrate that these statements apply to proofs produced by the production
[`o1-labs/proof-systems`](https://github.com/o1-labs/proof-systems) codebase.

---

## 1. Background and system under audit

`formal/` is a Lean 4 + Mathlib workspace of five packages — `pasta`, `poseidon`,
`bulletproof-pcs`, `kimchi`, `snarky` — formalizing the kimchi proof system as deployed over
the Pasta curves. The development culminates in per-curve **knowledge-soundness theorems for
the executable kimchi verifier**: a verifier written in Lean, validated byte-for-byte against
production wire data recorded from proof-systems, is proved knowledge-sound in a
forking/rewinding game with a concrete error bound, with extraction failure charged to
discrete log.

Three properties of the development frame this engagement:

* **The tree contains zero `axiom` declarations.** Every theorem's closure reduces to Lean's
  three standard axioms plus `Lean.ofReduceBool` (inherited solely from the CompElliptic
  dependency's `native_decide` primality/point-count certificates). Discrete-log hardness is
  a *hypothesis of the statements*; the random-oracle idealisation enters only as the game's
  uniform challenge table. There is no Fiat–Shamir axiom.
* **The kernel already checks the proofs.** Lean's kernel (independently replayed by
  lean4checker in CI) guarantees each proof proves its stated theorem. What no tool inside
  the system can check is whether the *statements mean what we intend* and whether they
  *apply to the deployed system*. That is precisely what this audit is for.
* **The project's own history motivates the anti-vacuity charter.** Two earlier endpoint
  formulations were satisfiable without content (one refutable by an extractor that always
  answers `none`; one by an adversary choosing the Schnorr commitment after its challenge),
  and one auxiliary hypothesis (`hU`) was mathematically unsatisfiable at the deployed
  instantiation. Each was caught internally and the current statements carry named exhibits
  blocking each failure mode. We are asking the auditors to attack the current statements the
  same way, independently.

The audit is **not** asked to re-verify proofs, and findings of the form "this proof is
long/ugly" are out of scope. Findings of the form "this *statement* does not say what the
docs claim", "this hypothesis is doing hidden work", or "this theorem cannot be applied to a
real proof-systems artifact" are exactly in scope.

---

## 2. Audit objectives

| # | Objective | Charter question |
|---|---|---|
| A | Structural & trust-surface audit | Is the trusted base exactly what is documented, and do the CI gates actually enforce what they claim? |
| B | Well-formedness of top-level statements | Does each top-level statement express the property that needs to be proven, with the right quantifiers, the right adversary, and hypotheses that are standard, minimal, and disclosed? |
| C | Anti-vacuity & applicability | Is every hypothesis satisfiable at the deployed instantiation, is every conclusion non-trivial, and do the theorems govern the verifier that accepts real proof-systems proofs? |

---

## 3. The claim inventory

The complete top-level surface is machine-enumerated: the packages' `roots.txt` manifests
(enforced by the dead-code gate: every declaration is reachable from them, currently
1516/1516 live) and the per-package `scripts/check_axioms.lean` root lists (kimchi: 39;
bulletproof-pcs: 28; pasta: 13; snarky: 5). The audit should treat those files as the
authoritative inventory. The tiers below organize it.

### Tier 1 — the endpoints

* `Kimchi.Verifier.KnowledgeSoundness.vesta_kimchi_knowledge_sound` /
  `pallas_kimchi_knowledge_sound` — for every adversary family (Section B2), over a uniformly
  sampled setup and uniform challenge table, and for every complete fork tape:

  ```
  μ { the run wins ∧ the extractor returns no satisfying witness table }
      ≤ (Q + k + 1)·3/2¹²⁸  +  (2ᵏ + 1)·ε  +  δ  +  (Q + 1)·szBudget/2¹²⁸
  ```

* `Bulletproof.Ipa.Forking.ipaVesta_knowledge_sound` / `ipaPallas_knowledge_sound` — the
  standalone-IPA analogues, plus the query-loss rungs `{vesta,pallas}_failure_measure_le`
  which assume no hardness at all.

### Tier 2 — faithfulness (the model *is* the shipped verifier)

* `kimchiVerify_eq_verifyWith` — the deployed executable verifier equals the
  challenge-generic one at the sponge's own squeezes, stated at **named** challenge sources
  (an existential form would be satisfied by a verifier with Fiat–Shamir deleted).
* `Bridge.FSFaithful` + `Bridge.wins_iff_kimchiVerify` — the eight equations separating the
  game's table from the deployed sponge (exactly the random-oracle idealisation), and the
  pointwise bridge: on a faithful table, the game's win predicate *is* deployed acceptance.
* `Bulletproof.verify_reflects`, and the IPA sponge-source exhibits
  (`verifyOracle_spongeFS`, `spongeFS_eq_from`, `uBaseOf_eq_transcript`,
  `toGroup_spongeOBase_preT`, cold/warm `*_eq_from` bridges).

### Tier 3 — anti-vacuity exhibits (what the endpoints do and do not claim)

* Honest families that win on **every** table: `honestKimchiFamily_wins` /
  `honestKimchiFamily_failure_set`; IPA `honestFamily_failure_set`,
  `honestNode_wins_everywhere`, `winsAtBase_uBaseOf`.
* The deferred-δ counterexample `verifyWith_of_deferred_delta` (pinned byte-for-byte by
  `check_locked_target.sh`) — why commit-then-challenge is a hypothesis, not a reading.
* `exists_ne_zero_kernel_scalarBasis` — commitment binding is *refutable* at the sampled
  basis, so no binding hypothesis can appear in the endpoints' ancestry.
* The sg-slot defence: `nodeTranscript_nodes`, `sg_determined_of_verifyWith`,
  `wireWins_pinTable`, `pinTable_factors`, `chainAt_sg`.
* `wireWins_U_irrelevant`, `deployedExtract_U_irrelevant`, `uRepresentationOfBreak`,
  `DeployedFamily.reductionEfficient_exists`, `derivedUDL_iff_residual_measure`.

### Tier 4 — the foundation the endpoints bottom out in

* Gate layer: per-gate `sound`/`complete` against **Mathlib's** elliptic-curve group law
  (AddComplete, VarBaseMul + `varBaseMul_scaleFast{1,2}`, EndoMul + per-curve
  `{pallas,vesta}_endoMul`, EndoScalar chain results, Poseidon, Generic), and the reflection
  bridges `ok_iff`.
* Arithmetization: `Kimchi.Index.satisfies_iff_fullFamily_dvd`; permutation certificate
  bridges (`isPrimitiveRoot_of_certificate`, `cosetShifts_of_certificate`,
  `{shift,sigma}Side_eval_row`).
* Executables: `kimchiVerify`, `Wire.KimchiProof.check` / `Wire.KimchiVK.check`, the fixture
  parsers, and the script-surface roots.
* Trust base: the `pasta` package's 13 roots (orders, GLV/endo facts — all *theorems* against
  CompElliptic certificates).

---

## 4. Work stream A — structure and trust surface

**A1. Axiom inventory and gate integrity.** Validate that the tree contains zero `axiom`
declarations; that each `check_axioms.lean` enumerates the roots it claims and its allowed
set is exactly `[propext, Classical.choice, Quot.sound]` (+ `Lean.ofReduceBool` where
declared); and that the gates cannot be dodged (e.g., by declaring a new root that never
enters a root list, or by an `Environment`-level trick that kernel replay would miss).
*Why: every claim in this document reduces to "the closure of these constants is these
axioms". A gate that under-enumerates is a silent hole in the entire trust story.*

**A2. `Lean.ofReduceBool` provenance.** Confirm the only `native_decide` axioms in any
closure are CompElliptic's primality and point-count certificates, and characterize what is
being trusted there (the Lean compiler, on those specific closed computations).
*Why: `ofReduceBool` puts the compiler in the TCB. Its scope must be exactly the curve
certificates and nothing from this tree — the kimchi gate rejects tree-local
`native_decide` by construction, and that construction should be checked.*

**A3. Upstream surface.** Review the pinned dependencies (Mathlib, `daira/CompElliptic`,
`zcash/ironwood` — the latter contributes the forking machinery and has zero axioms of its
own) and the specific upstream definitions our statements *import meaning from*:
`WeierstrassCurve.Affine` and its group law, `ZMod p` fields, ironwood's
`RecursiveForkCoins`/`OracleComp`/AGM types, and the probability plumbing
(`PMF.uniformOfFintype`, `toOuterMeasure`).
*Why: a statement is only as meaningful as the definitions it is written in. If ironwood's
`Complete` or Mathlib's outer measure meant something unexpected, our theorems would be
well-typed and wrong.*

**A4. Kernel replay and reproducibility.** Confirm `scripts/kernel-replay.sh` (lean4checker)
replays every module, and that a clean-machine build reproduces the gate results from the
documented commands.
*Why: all other gates trust the elaborated environment; kernel replay is the check on that
trust, and the audit itself needs a reproducible baseline.*

**A5. Definitional single-sourcing.** Verify there is exactly one definition of each
load-bearing predicate (gate `Holds` predicates only in `Gate/` modules; one `Satisfies`;
one executable verifier; no parallel "escape-hatch" copies), that `roots.txt` matches the
intended public API (dead-code gate at 0), and that the locked-target mechanism pins the
statements it claims to pin.
*Why: the classic formalization failure is proving a theorem about a fork of the definition
the consumer reads. The gates exist to prevent drift; the audit should try to construct a
drift they would miss (the locked-target gate is textual — assess that design).*

**A6. Constants and conventions.** Independently re-derive and check against proof-systems:
the Pasta moduli and curve equations; the endo coefficients (base-field vs scalar-field endo
— a historical trap site); the shifted-scalar conventions (Type 1 vs Type 2, `2^254` vs
`2^255`); the 128-bit challenge squeeze and `endoExpand`; the column/batch layout constants
in `Kimchi/Columns.lean` (`wCols = 15`, `permCols = 7`, `tailRowCount = 43`, …) against
`wires.rs` / `verifier.rs`.
*Why: a single transposed constant re-targets every downstream theorem at a different
system, and constants are exactly where review outperforms testing — fixtures exercise the
deployed values but cannot tell you a name is bound to the wrong role.*

**A7. CI process integrity.** Review the full gate battery (`lean.yml`) — axioms ×5, locked
target, dead-code, sorry census, style, per-root lint, shake, kernel replay, shape literals,
and the ten fixture drivers — for what each actually enforces, its bypass conditions, and
whether the set is complete with respect to the trust story told in §1.
*Why: the claims are maintained over time by these gates, not by any one review. Their
soundness is a first-class audit target.*

---

## 5. Work stream B — well-formedness of the top-level statements

**B1. The executable verifier is the deployed algorithm.** Perform a semantic, side-by-side
review of `Kimchi/Verifier/Kimchi.lean` + `Verifier/Wire.lean` against proof-systems
(`verifier.rs`, `oracles.rs`, the linearization and permutation code): transcript schedule
(absorb order, digest, public commitment), challenge derivation (128-bit squeeze +
endo-expansion), the batch/eval layout across chunking regimes (`nc = 1, 2, 8`), the
public-row treatment (barycentric and carried), `ft`/linearization scalars, the permutation
argument, the in-protocol derivation of the opening base `U` from the warm sponge state
(`group_map` of a squeeze), and the final MSM.
*Why: the endpoints quantify over **this** verifier. The fixture drivers prove agreement on
recorded points; only review can argue agreement as algorithms. This single item carries
more of the audit's value than any other.*

**B2. The adversary model.** Review `KimchiFamily`: a basis-indexed family supplying, per
sampled setup — a claim (`cvk`, public input, digest), an oracle-machine adversary with
query bound `Q` (`queryBound`), and the AGM data of B3. Classify every field and hypothesis
as (i) adversary-chosen data, (ii) an AGM obligation, or (iii) an explicit restriction —
the declared restrictions being `hnc : 0 < nc`, `hpub` (public arity), `htpos` (non-empty
quotient commitment), `hvk : (cvk basis).Corresponds (srsOfBasis k basis) idx` — and assess
each restriction as standard/minimal or flag it as hidden work.
*Why: knowledge soundness is only as strong as the adversary class it quantifies over. A
family definition that quietly forces honest structure would make the theorem true and
uninteresting; conversely each restriction must be visible to any consumer citing the
result.*

**B3. The AGM obligations.** Validate that `aRef`/`ρRef`/`hrep` (SRS-basis representations
of every commitment in the run's flat stream), `aT`/`ρT`/`hTC` (the quotient chunks), and
the prefix-determination laws `hrepPrefix`/`hTCPrefix` (a row's representation is a function
of the transcript prefix at the node where that row is absorbed) together constitute the
**standard algebraic-group-model adversary** — no more (which would weaken the theorem) and
no less (which would break the forking argument's right to replay representations across
reprogrammed tables).
*Why: the endpoints are AGM theorems, as is standard for IPA-based systems. The exact AGM
formalization is where such proofs most often diverge from the literature, and
prefix-determination is the load-bearing subtlety: it is what makes representations stable
under the fork's reprogramming.*

**B4. Quantifiers and the probability space.** Check the endpoint's logical shape: for all
families, for all complete fork tapes (`coins.Complete` — validate its definition gives the
fork enough fresh challenges rather than smuggling a success assumption), the hardness
hypothesis (`DiscreteLogRelationHardFor`, which under `ReductionEfficient` bounds the
relation finder's textbook-DL advantage by `ε` and the derived-base residual by `δ`) implies
a bound on the **uniform product measure over (setup scalars × challenge table)** of the
failure event. Confirm there is no quantifier inversion, no per-run (rather than
per-measure) reading, and that the finite-uniform outer-measure framing is the intended
probability statement.
*Why: quantifier and measure structure is the canonical way a formal statement silently
weakens — e.g., ∃-coins, or a bound conditioned on an adversary-dependent event, would
formally verify and mean little.*

**B5. The extraction predicate.** Validate `ExtractsWitness`: the extractor's left payload
`a`, assembled by `runWTab`, satisfies `Satisfies fam.idx (pubView fam.idx (fam.pub basis))`
— i.e., the extracted table satisfies **the circuit the verifying key corresponds to**
(via `hvk`), at the claimed public input. Trace `Satisfies` down through
`satisfies_iff_fullFamily_dvd` to the gate-semantics layer, and check `pubView` binds the
public input the way the deployed verifier does.
*Why: "knowledge" is exactly "possession of a witness for the claimed statement". If
`Satisfies` or the public binding deviates from the deployed relation, the theorem extracts
the wrong thing. Note the deliberate design: the extractor's payload carries **data, not
proofs**, and all semantics live in `ExtractsWitness` — so the audit should confirm the
measured event can only be enlarged, never shrunk, by that separation.*

**B6. The error bound, term by term.** Re-derive the shape of each summand against the
literature: `(Q + k + 1)·3/2¹²⁸` (presence/query loss of a three-way fork over a `2¹²⁸`
prechallenge alphabet), `(2ᵏ + 1)·ε` (the DL charge across the fork's arity), `δ` (the
residual: **the derived-base event's own measure**, per
`derivedUDL_iff_residual_measure` — validate that presenting a residual, rather than a
reduction to a standard problem, is honestly documented and sound), and
`(Q + 1)·szBudget/2¹²⁸` (the seven counted Schwartz–Zippel exclusion sets — audit
`szBudget`'s arithmetic against the degree bounds).
*Why: a bound of the wrong shape is the cheapest external signal that the proved game is
not the intended game; and the δ-as-residual design is unusual enough that its honesty and
its consequences for interpretation deserve independent judgment.*

**B7. Concrete-security reading.** Instantiate the bound numerically at deployed parameters
(production SRS sizes `2ᵏ`, domain sizes `n`, `zkRows`, realistic query budgets `Q`, Pasta
DL-hardness beliefs for `ε`) and confirm the theorem is quantitatively meaningful — the
right-hand side is far below 1 in realistic regimes.
*Why: a formally impeccable bound that is numerically vacuous at deployed sizes would pass
every other audit item while guaranteeing nothing.*

**B8. Gate and circuit statements.** For each gate: the soundness statement concludes in
**Mathlib's group law** (`Point.some _ _ h₁ + Point.some _ _ h₂ = Point.some _ _ h₃`,
`n • P`, the GLV eigenvalue identity), not in a restatement of the field constraints; the
completeness statement gives the honest prover a satisfying witness; the per-curve entry
points (`varBaseMul_scaleFast{1,2}`, `{pallas,vesta}_endoMul`) match the scalar conventions
the deployed prover uses (shifted scalars, crumb schedules).
*Why: the semantic content of "the circuit computes X" bottoms out here. The
spec-restates-implementation anti-pattern is the standard failure of arithmetization
formalizations, and it is only detectable by reading the statements.*

**B9. The faithfulness layer and the ROM boundary.** Validate that
`kimchiVerify_eq_verifyWith` pins the deployed verifier to the challenge-generic one at
**named** sponge squeezes; that `FSFaithful`'s eight equations say exactly "the game's
table agrees with the deployed sponge on the reads the verifier performs" — no more, no
fewer; and that `wins_iff_kimchiVerify` composes them into the pointwise bridge. Confirm
the random-oracle idealisation enters the development **here and only here** and is carried
by no axiom.
*Why: this is the single modelling step between the theorem and the shipped code. If
faithfulness were existential, partial, or duplicated elsewhere, the "no Fiat–Shamir axiom"
headline would overclaim.*

---

## 6. Work stream C — anti-vacuity and applicability to proof-systems artifacts

**C1. Hypothesis satisfiability, hypothesis by hypothesis.** For every hypothesis of every
Tier-1 statement, identify its satisfaction evidence and assess sufficiency:
`Index` (built from production fixtures by `check_index_fixture.sh` — note §7: no Lean-side
witness); `hvk`/`Corresponds` (production verifier keys, `check_vk_correspond.sh`); family
inhabitation (`honestKimchiFamily`); `ReductionEfficient`
(`reductionEfficient_exists` obtains a call bound without inspecting the counter — confirm
the efficiency gate is therefore not a hidden efficiency claim); `coins.Complete`
(constructibility of complete tapes); `DiscreteLogRelationHardFor` (a hypothesis by design
— confirm it is the standard DL assumption plus the declared residual, satisfiable in
principle, and not self-contradictory).
*Why: an unsatisfiable hypothesis makes any theorem free. This project has already refuted
one of its own drafts on exactly these grounds; the audit should apply the same standard
with fresh eyes. The house doctrine is that vacuity has two directions — a free conclusion
and an unsatisfiable hypothesis — and both must be checked.*

**C2. Adversarial degeneracy attempts.** Actively attempt to satisfy each endpoint without
doing the work, and confirm each attempt is blocked by a named hypothesis or refuted by a
named exhibit. Minimum attempt set: the always-`none` extractor (blocked by the honest
families: the win set can have measure 1); the deferred-δ adversary (blocked by
`DecodesFromPrefixes`; exhibit `verifyWith_of_deferred_delta`); assuming commitment binding
(refuted outright by `exists_ne_zero_kernel_scalarBasis`); grinding the un-absorbed `sg`
slot (priced by `Q` via the pinning factorization); planting challenges via the sampled
basis (blocked by `uRepresentationOfBreak` being computed data); base-override games
(blocked by the `*_U_irrelevant` pair). The auditors are asked to extend this list with
attacks of their own devising.
*Why: independent attack attempts are the strongest anti-vacuity evidence there is. The
exhibits were built against the failure modes we found; the audit's value is the failure
modes we did not.*

**C3. End-to-end artifact run.** From an unmodified proof-systems checkout, regenerate the
fixtures with `tools/fixture-dump`, and re-run the drivers: the executable kimchi verifiers
accepting five production proofs (both curves; `nc = 1` barycentric and carried; `nc = 2`
both curves; `nc = 8`), rejecting corruptions, refusing ragged wire data; the index,
permutation, VK-correspondence, linearization, IPA, and sponge-trace checks. Confirm the
constant appearing in the endpoint statements (`kimchiVerify`, via
`kimchiVerify_eq_verifyWith` and the bridge) **is literally the function** the drivers run
on those bytes — no fork between the theorem's subject and the check's subject.
*Why: this is charter dimension (2) verbatim: the statements must be usable to verify
proofs the production codebase produces. Regeneration from a clean checkout also rules out
fixture staleness or fixture-side accommodation.*

**C4. Wire-protocol identity and parser totality.** Review the check-then-verify parse
layer (`Wire.KimchiProof.check`, `Wire.KimchiVK.check`, the fixture decoders): within the
modeled fragment, the accepted wire language neither narrows (silently rejecting real
proofs — which would make "the verifier accepts" quantify over a sublanguage) nor widens
(accepting shapes production serde rejects) the production format; shape checks (sizes,
`runNc`, chunk counts) mirror serde-enforced invariants.
*Why: the theorems are about acceptance of parsed wire data. Any gap between the parsed
language and the production language is a gap in what the endpoints govern.*

**C5. Modeled-fragment delineation.** Produce, and check the documentation against, a
precise statement of which production circuits the endpoints govern: the transcribed basic
gate set (generic, poseidon, completeAdd, varBaseMul, endoMul, endoScalar); **no lookups,
no optional gates (range check, foreign field), no recursion** (`prev_challenges` absent
from the wire records); chunking regimes covered; `zkRows` handling.
*Why: scope overclaim is the most likely way this work gets misused downstream — e.g.,
Mina's pickles proofs use recursion and lookups and are therefore outside the modeled
fragment. The audit should confirm the boundary is stated everywhere the results are
presented, and that nothing inside the boundary is silently unmodeled.*

**C6. Per-curve instantiation completeness.** Confirm every abstract result in the chain
has its Vesta and Pallas corollaries at the deployed parameters, with no
instance-obligation gaps hidden behind abstraction.
*Why: house doctrine — "no per-curve corollary" is the historical tell of a hypothesis
that cannot be met at the real instantiation.*

**C7. Fiat–Shamir schedule fidelity.** Confirm the Lean transcript encoding (absorb order,
squeeze points, the warm-state derivation of the opening base, the `Fin 6` pre-IPA
challenge tuple β, γ, α, ζ, polyscale, evalscale) against `oracles.rs`, and assess whether
the sponge trace fixtures (`check_fq_sponge.sh`, `check_sponge_vectors.sh`) cover the full
schedule the faithfulness theorems rely on.
*Why: the FS schedule is the security-critical surface of any transcript argument. A wrong
absorb order would make the faithfulness layer a theorem about a different protocol while
every proof still checks.*

**C8. The setup distribution.** Assess the game's sampled setup — uniform scalars `s`
against a base point `B`, basis `= augOfSetup (scalarBasis B s)`, with the adversary seeing
only the points and the scalars known only to the reduction — against the deployed SRS
(hash-derived, nothing-up-my-sleeve points), confirming this is the standard
"generators-as-uniform-group-elements" idealisation; and review the per-run override of the
`U` slot by the transcript-derived warm base (`runSrs`) for consistency with the deployed
in-protocol derivation of `U`.
*Why: the DL charge is priced against this distribution. If the sampled setup differed
materially from what the deployed SRS is modeled to be, `ε` would misprice reality — and
the known-scalars sampling must demonstrably never leak to the adversary.*

---

## 7. Self-declared modelling steps and known gaps — validate our accounting

We declare the following up front and ask the auditors to **confirm or correct this list**
— including finding anything that belongs on it and is missing. An audit that verifies our
own accounting of limitations is worth more than one that discovers them adversarially.

1. **The random-oracle model is a frame, not an assumption in the system.** The game runs
   over a uniform challenge table; `FSFaithful` names the eight equations identifying that
   table with the deployed Poseidon sponge's reads. That Poseidon soundly instantiates
   Fiat–Shamir is deliberately **not claimed, not axiomatized** — it is outside the
   formalism, as in ironwood.
2. **The endpoints are AGM-relative.** The adversary family carries algebraic
   representations (B3). This matches the literature for IPA-based systems, and it is a
   real restriction of the adversary class.
3. **δ is a residual, not a reduction.** `derivedUDL_iff_residual_measure` records that the
   δ summand is the derived-base event's own measure. Only ε is a reduction to a standard
   problem.
4. **The oracle domain carries an `sg` slot the deployed sponge never absorbs.** The
   defence (locality + pinning factorization, priced by `Q`) is Tier 3; its scope — the
   *game's* reads factor, the adversary's need not — is stated in
   `Forking/Deployed.lean`'s preamble.
5. **The honest kimchi family is `Index`-parameterized with no Lean-side witness.**
   Inhabitation is demonstrated by `check_index_fixture.sh` (CI, from production data), not
   by a term in the library.
6. **The modeled fragment is the basic gate set** — no lookups, no optional gates, no
   recursion (C5).
7. **The `snarky` package (the circuit-DSL embedding) is outside the dead-code audit** and
   outside this engagement's Tier 1; its five interpreter laws are gated separately.
8. **The locked-target gate is textual** (statement bytes), by design; semantic drift of
   *unlocked* statements is constrained only by review and this audit.
9. **Deleted prior art is in git history**: the refuted drafts, the vacuity analyses of the
   pre-forking Fiat–Shamir-axiom formulation (`Forking/{Triviality,Extraction,Knowledge}`,
   removed at `e7c431b2`), and the internal statement audit that preceded this SoW.

---

## 8. Out of scope

* Re-verifying Lean proofs by hand (kernel + lean4checker cover proof-checking); proof
  style, length, or performance.
* Auditing Mathlib, CompElliptic, or ironwood internals beyond A3's
  definitions-we-import-meaning-from review.
* Auditing proof-systems (Rust) for its own correctness — it is the *reference*, not the
  subject. (Divergences found under B1/C7 are findings about our model, though auditors
  should flag apparent upstream bugs.)
* The PureScript/Rust prover stack outside its role in fixture generation; the `snarky`
  DSL package (§7.7); side channels; anything about proving performance.

---

## 9. Materials, reproduction, and prior work

* **Repository:** `l-adic/snarky`, branch `kimchi-knowledge-soundness` (`92a0fb7f`, PR
  #280). Subject tree: `formal/`. Toolchain pinned (`lean-toolchain`, Lean v4.30.0).
* **Build:** `cd formal && lake build` (workspace; ~full Mathlib build on first run).
  Gates: `make lean-lint lean-shake lean-deadcode lean-kernel-check`;
  `formal/*/scripts/check_*.sh` (each package-local, env-var overridable);
  `formal/scripts/{check-style.sh,check_sorry_census.sh}`.
* **Fixtures:** `formal/*/fixtures/`, recorded by `tools/fixture-dump` (see its README for
  the proof-systems pin and regeneration workflow — C3 should regenerate rather than trust).
* **Prior internal audits and design records** (in `formal/docs/`): `statement-audit-sow.md`
  / `statement-audit-report.md` (the earlier internal statement audit — validate and
  extend, do not assume), `locked-target.md`, `minimum-support.md`,
  `w2-oracle-model-scope.md`, `agm-reuse-scope.md`, `standard-model-line.md`,
  `architecture.md`, and the module dependency graph (`module-deps.svg`).

---

## 10. Deliverables

1. **Findings report**, with severities calibrated to formal claims:
   * **Critical** — a Tier-1/2 statement does not express the intended property, or is
     vacuous (unsatisfiable hypothesis / free conclusion), or the executable verifier
     semantically diverges from the deployed algorithm inside the modeled fragment.
   * **High** — a hypothesis does hidden work (adversary class materially narrower than
     documented); a scope overclaim in documentation; a gate that can be bypassed.
   * **Medium** — a modelling deviation that is real but inadequately recorded; a fixture
     coverage gap; an error-bound term that is correct but misleadingly presented.
   * **Low / Informational** — hygiene, documentation, process.
2. **Per-claim verdict table** over the Tier 1–4 inventory: *well-formed?* /
   *anti-vacuous?* / *scope confirmed?* — with a sentence of justification each.
3. **Attack log** for C2: every degeneracy attempt made, including unsuccessful ones, with
   the blocking hypothesis or exhibit identified.
4. **Concrete-security note** (B7): the bound evaluated at deployed parameters.
5. **Accounting verdict** on §7: each self-declared item confirmed, corrected, or
   augmented.
6. **Reproduction transcript**: the clean-machine build + gate + fixture-regeneration run.

---

## 11. Acceptance criteria

The engagement is complete when every item in the claim inventory (§3) carries an explicit
verdict; every line item in work streams A–C is either validated or converted into a
severity-classified finding; the §7 accounting has been independently confirmed or
corrected; and the C2 attack log demonstrates genuine adversarial effort beyond the attempt
set we supplied.

We consider the audit *successful* not when it returns zero findings, but when its findings
— including "this statement does not say what you think it says", the most valuable
sentence an audit of a formal development can produce — are specific enough to act on.
