# Statement of Work — Capstone / Statement-Correctness Audit of `formal/`

**Object under audit:** the Lean statements (not the proofs) of the kimchi formalization —
are the capstone theorems, the definitions they quantify over, and the declared axioms the
*right things to have proved* about the deployed Rust verifier?

**What is explicitly trusted and therefore NOT re-audited here:**

* Proof bodies — kernel-checked at build, replayed by the lean4checker gate.
* Axiom *closures* — pinned by the per-package `check_axioms.lean` gates.
* Value-level agreement of the executable layer with production — adjudicated by the
  fixture drivers (accept + corruption matrices, both curves, nc = 1 and nc = 2).
* Correctness of proof-systems itself. The Rust is the *reference*, not a target.

The residual gap this SoW targets: **semantic faithfulness of the Props**. A theorem can be
kernel-true, axiom-clean, fixture-consistent — and still not say what we believe it says
(vacuous hypothesis, weakened conclusion, wrong quantifier order, drifted definition, or an
axiom strong enough to beg the conclusion).

---

## 1. Inputs

| Input | Location |
| --- | --- |
| Lean development | `formal/{kimchi,bulletproof-pcs,poseidon,pasta,snarky}` |
| API surface (audit enumeration) | each package's `roots.txt` + `scripts/check_axioms.lean` |
| Rust reference | proof-systems checkout used by `tools/fixture-dump`: `kimchi/src/verifier.rs` (`to_batch`, final check), `oracles.rs`, `circuits/{wires.rs,constraints.rs,polynomials/*}`, `verifier_index.rs`; `poly-commitment` (IPA); `mina_poseidon` |
| Fixtures (non-vacuity witnesses) | `*/fixtures/*.json` + the check drivers |
| Prior claims to audit against | module preambles, `roots.txt` prose, memory-ledger claims ("AGM soundness of the deployed verifier") |

## 2. Statements in scope (the audit inventory)

Primary (the claims the library exists to make):

1. **Terminal theorems** — `kimchi{Vesta,Pallas}_run_sound_algebraic_ft`: genuine
   `verify = true` + AGM representations of the `44·nc + 1` flat segment rows and the `t`
   chunks ⟹ guarded `Satisfies idx (pubView idx pub)`.
2. **Run-level standard-model capstones** — `kimchi{Vesta,Pallas}_run_sound`,
   `ft_opening_of_reflected_{vesta,pallas}`.
3. **The reduction spine** — `kimchiProof_sound`, `kimchiProof_sound_algebraic_ft`,
   `kimchiProof_sound_of_openings`, `Kimchi.Protocol.sound`,
   `Index.satisfies_iff_fullFamily_dvd`.
4. **The executable boundary** — `kimchiVerify`, `Wire.{KimchiProof,KimchiVK}.check`,
   `Ipa.verify`/`verify_reflects`.
5. **PCS soundness** — `chunked_ipa_soundness`, `chunked_batch_soundness`,
   `commitmentBinding_iff_no_relation`, `ipa{Vesta,Pallas}_sound`.
6. **The declared trust surface** — `poseidon_fiat_shamir_{vesta,pallas}`,
   `kimchi_fiat_shamir_{vesta,pallas}`, the `hbind` DL-binding hypothesis, the Pasta
   Hasse/CM axioms, `Lean.ofReduceBool` (via CompElliptic).
7. **Load-bearing definitions quantified by the above** — `Index`, `Satisfies`, `pubView`,
   `Accepts`, `Evals`/`evalsOf`, `fullFamily` (α-pool layout), `batchC`/`streamPos`,
   `ftEval0`, the guard predicates in the terminal conclusions.
8. **Gate layer** (secondary; audited once before in the `sound`/`complete` sweep) —
   spot-check that each `Gate.*.sound/complete` pair still brackets the gate (a wrong
   `Holds` fails completeness OR the fixture, so exposure is low).

## 3. Workstreams

### D1 — Capstone back-translation (blind)

For each statement in items 1–5: an agent receives the Lean statement **with all
docstrings stripped** and must state in precise prose (a) what is assumed, (b) about which
objects, quantified in which order, (c) what is concluded. A second agent independently
does the same. A judge compares both against the documented claim and the Rust behavior.
Divergence = finding. This catches the "docstring says more than the binder does" class.

### D2 — Vacuity and hypothesis reachability

Every hypothesis of every primary statement must be shown *satisfiable in the intended
instance* — ideally by instantiating on recorded fixture data (the strongest witness: the
hypotheses of the terminal theorems should be dischargeable, or clearly discharge-shaped,
at the nc = 2 production fixture), otherwise by a constructed witness or a prose argument
reviewed adversarially. Special attention (historical trap): every counted bad-set must be
quantified BEFORE the challenges it excludes (`badXiOf`/`badROf`/`badZ` discipline), and
no hypothesis may secretly imply the conclusion. Also confirm each `complete` direction
still exists where soundness alone could be vacuously strong.

### D3 — Axiom-strength audit

For each of the four FS axioms + `hbind` + Hasse/CM: state the assumption in standard
crypto vocabulary; compare against the literature form (Fiat–Shamir in the ROM /
rewinding-forking, DL-relation hardness, curve point counts); verify the axiom is (a) not
stronger than the standard assumption it names, (b) not quantified so as to yield the
capstone directly, (c) used the declared number of times (cross-check `check_axioms`
output), and (d) mutually independent in the sense documented. Deliverable includes a
plain-English trust-surface statement suitable for an external reviewer.

### D4 — Definition ↔ Rust correspondence (meaning level)

Line-by-line reading of each load-bearing definition against its Rust origin:
`kimchiVerify` vs `verifier.rs::verify`/`to_batch` (row order, ft interposition,
`sigma_comm[PERMUTS−1]` linearization, public-row handling), `Evals`/`evalsOf` vs the
proof-evaluations bundle, `fullFamily` vs `linearization.rs` + the α-pool
(`gateAlphaCount = 21`, perm members at α²¹⁻²³), `ftEval0` vs `oracles.rs::ft_eval0`,
`Index`/`VKCorresponds` vs `verifier_index.rs`, wire `check` vs the serde types, the IPA
`verify` vs `poly-commitment`. The fixtures pin these *by value on recorded runs*; D4
audits the *reading* — that each Lean definition means the same computation on all inputs,
and that the corruption matrices actually cover the failure modes claimed.

### D5 — Layer-drift audit

Walk each boundary: wire record → `check` → checked record → `kimchiVerify` → reflection
(`runStreamP`/`runInput`) → abstract batch (`batchC`, `streamPos`) → reduction → protocol
(`Accepts`) → `Satisfies`. At each hop: is the translation total where claimed, are all
pins ("the parse IS the proof") actually enforced by the parse, does any information get
dropped or weakened (e.g. `pubView`'s guard, the `tComm_le` bound, the zk-rows regime),
and do the two sides of every reflection lemma quantify the same objects?

### D6 — Claim-gap register

Reconcile what is PROVED against what is SAID — in module preambles, `roots.txt` prose,
and the informal claim "AGM soundness of the deployed verifier at production chunking."
Enumerate the known deferred items (forking/density model for FS, `hbind` as hypothesis,
Hasse discharge, the 45-row ↔ `batchC` residue reconciliation) and verify every written
claim is scoped to exclude them. Output: a definitive "what this development does and does
not establish" statement.

## 4. Method and discipline

* **Panels per workstream**, each agent given only the sources it needs (Lean modules +
  the matching Rust files); D1 agents get docstring-stripped sources.
* **Adversarial verification:** every finding goes to ≥ 2 independent refuters prompted to
  kill it (wrong reading, already handled, fixture-covered). Only findings surviving
  refutation are reported, with verdict CONFIRMED (refuters failed on concrete grounds)
  or PLAUSIBLE (needs human/mathematical adjudication).
* **Severity taxonomy:**
  * **Critical** — a primary statement does not establish its documented claim (vacuous,
    wrong quantifiers, axiom begs conclusion, definition diverges from Rust).
  * **Major** — statement is materially weaker/narrower than documented, or a trust-surface
    description is inaccurate.
  * **Minor** — doc drift, misleading prose, missing non-vacuity witness.
* **No code changes.** The deliverable is findings; fixes are follow-up work, scoped after
  the user reviews the report.
* Where a non-vacuity witness is computable, the auditor may WRITE (not commit) a
  throwaway `#eval`/instantiation script and report its result.

## 5. Deliverables

1. `formal/docs/statement-audit-report.md` — findings by severity, each with: the
   statement, the reading at issue, the failure scenario, refutation history, verdict.
2. The D3 trust-surface statement and the D6 claim-gap register (sections of the report;
   both are deliverables even if empty of findings — they are the audit's positive
   artifact).
3. A follow-up worklist (proposed, unscoped) for anything Critical/Major.

## 6. Execution plan

| Phase | Content | Gate to next |
| --- | --- | --- |
| P0 | Inventory freeze: extract the exact statements (pretty-printed, docstring-stripped variants), collect the Rust excerpts per D4 target | user confirms inventory |
| P1 | D1 + D2 + D3 panels (independent; parallel) | verify pass on findings |
| P2 | D4 + D5 panels (need P0 pairings; parallel) | verify pass on findings |
| P3 | D6 synthesis + report assembly | user review |

Estimated scale: this is a multi-agent workflow run per phase (roughly 15–30 agents per
panel phase including refuters); expect material token spend and a few hours wall-clock
spread over the phases, with user checkpoints between them. P0 is cheap and produces the
inventory for sign-off before the expensive phases run.

## 7. Acceptance criteria

The audit is complete when: every inventory item has a D1 back-translation on record; every
primary hypothesis has a reachability witness or an explicit PLAUSIBLE flag; all four FS
axioms have literature comparisons; every D4 pairing has a written correspondence
verdict; the claim-gap register covers every prose claim in `roots.txt` and the module
preambles of the statements in scope; and every finding carries a refutation history.
