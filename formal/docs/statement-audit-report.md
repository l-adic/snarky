# Statement-Correctness Audit of `formal/` — Findings Report

> **STATUS (superseded): the probabilistic soundness line this document is largely about was
> RETIRED.** The forking / knowledge-soundness tree in `kimchi` and `bulletproof-pcs`, and the
> `Zcash/ironwood` dependency under it, were deleted; see `soundness-line-retirement.md` for
> what went, why, and where to recover it. This file is kept as the record of an outside
> engagement — read it as history. Its open items (O-1a / O-1b), its locked-target and
> exhibit-set invariants, and its gate counts no longer describe this repository.

**Scope.** This report executes `formal/docs/statement-audit-sow.md`: an audit of the Lean
*statements* (theorem signatures, load-bearing definitions, declared axioms, and their
docstrings/manifest prose) of the kimchi formalization — **not** the proof bodies, which
are kernel-checked and out of scope. The question throughout is *semantic faithfulness of
the Props*: does each statement say what the development claims it says about the deployed
Rust verifier?

**Reference.** proof-systems checkout at
`mina/src/lib/crypto/proof-systems` @ `370f13c59a` (`kimchi/src/verifier.rs`, `oracles.rs`,
`linearization.rs`, `circuits/polynomials/*`, `poly-commitment/src/{ipa,commitment}.rs`,
`poseidon/src/sponge.rs`).

**Method and its limitation (read this).** The audit ran as a multi-agent workflow: for
each inventory group, two independent blind back-translators worked from
docstring-stripped sources (D1), a judge reconciled them against the documented claim and
the Rust (D1 judge), and dedicated panels ran vacuity/reachability (D2), axiom-strength
(D3), definition↔Rust correspondence (D4), and layer-drift + claim-sweep (D5/D6). **The
finder and judge stages completed; the planned adversarial-refuter stage (≥2 refuters per
finding) did not run — it was cut twice by session/credit limits.** In its place, the lead
auditor **directly re-verified every Critical and Major finding against source** (the
verifications are cited inline below); Minor findings are single-pass reviewed, not
adversarially refuted. Findings that would normally carry a CONFIRMED-by-refutation verdict
are marked **VERIFIED (author-direct)**; the rest are **REVIEWED (single-pass)**. 75 unique
findings were raised across the panels; 6 panels returned clean.

Severity per the SoW: **Critical** — a primary statement does not establish its documented
claim (vacuous, wrong quantifiers, axiom begs the conclusion, or a load-bearing definition
diverges from Rust). **Major** — statement materially weaker/narrower than documented, or a
trust-surface description is inaccurate. **Minor** — doc drift, misleading prose, missing
non-vacuity witness.

---

## Executive summary

Two Critical findings survive verification:

- **C1 — the terminal theorems are vacuously satisfiable as *statements*.**
  `kimchi{Vesta,Pallas}_run_sound_algebraic_ft` quantify their bad-challenge sets
  `∃ badB badG badA badZ wTab` *after* the concrete records `(cvk, cp, pub)` — hence after
  the run's deterministic sponge challenges — are fixed, so the guarded implication is
  discharged by the trivial witness `badZ := {runζ}` with no hypothesis used. The real
  content lives only in the proof term. This is the project's own documented "vacuity trap."
- **C2 — the EndoMul gate linearization diverges from Rust.** The Lean `EndoMul` constraint
  list is a re-ordering of Rust's `constraint_checks` vec (booleans moved from first to
  seventh, distinct-point check moved into the middle) *and* the scalar-register constraint
  is negated. Because `gateLinearization` assigns α-powers positionally over this list,
  `ftEval0` — and therefore `kimchiVerify` — computes a different value than production on
  any circuit with a nonzero EndoMul selector (which includes real pickles step circuits).
  All fixtures mask it (every recorded `emul_selector = 0`).

The Major findings cluster into three themes: **(a) fidelity of the executable verifier to
Rust** (the Poseidon `absorb_g` identity-point encoding; the IPA two-equation vs single
randomized-MSM acceptance; the `htpos` hypothesis that excludes a deployed-accepted input
class; the IPA wire-parse guards attributed to production checks that don't exist);
**(b) the Fiat–Shamir axioms** are universally quantified over unconstrained (including
degenerate) SRS and asserted at probability 1, making them in-principle false — treated
asymmetrically from `hbind`, which the development honestly carries as a hypothesis;
**(c) trust-surface documentation** that describes a deleted axiom boundary, omits the four
FS axioms, or overstates what the fixture drivers adjudicate.

The internal soundness chain (gate `Holds` → `Accepts`/`Protocol.sound` → reduction → PCS)
is, on this audit, **statement-consistent**: the divergences are between the *modeled*
verifier and the *deployed* verifier, or between statements and their prose, not internal
contradictions. The load-bearing definitions the SoW named (`Index`, `Satisfies`, `pubView`,
`fullFamily` with `gateAlphaCount = 21` + perm at α²¹⁻²³, `batchC`, `claimedEvals`) matched
their Rust origins on the panels that examined them, with the single exception of the
EndoMul α-ordering (C2).

---

## Critical findings

### C1 — Terminal roots vacuously satisfiable as statements (quantifier order)

**Statements.** `Kimchi.Verifier.kimchiVesta_run_sound_algebraic_ft` and its Pallas twin
(`kimchi/Kimchi/Verifier/Capstone/Reflection.lean:1303, 1361`), and the private
`run_sound_algebraic_ft` they wrap (`:1089`).

**Reading at issue.** The conclusion has the form
```
∃ badB badG badA badZ wTab,
    (card bounds) ∧
    ( (runOracles …).beta ∉ badB → (runOracles …).gamma ∉ badG … →
      (runOracles …).alpha ∉ badA … → (runOracles …).zeta ∉ badZ … β γ α (ftChunkAssembly …) →
      (runOracles …).zeta ≠ 1 → (runOracles …).zeta ≠ idx.omega^(n−zkRows) →
      Satisfies idx (pubView idx pub) wTab )
```
Every guard subject is a **fixed, deterministic** sponge output of the record parameters
`(σ, cvk, cp, pub)`, which are bound *before* the `∃`.

**Failure scenario (VERIFIED, author-direct).** Instantiate
`badB = badG = badA = ∅`, `badZ := fun _ _ _ _ => {(runOracles … cvk cp pub).zeta}`,
`wTab := fun _ _ => 0`. Every cardinality conjunct holds (`0 ≤ …`; and `1 ≤ Index.degreeBound n
= 9·n`, with `n ≥ 1` from `[NeZero n]` — verified at `Index/Degree.lean:57`). The guarded
implication is discharged by the contradiction `runζ ∉ {runζ}`. **No hypothesis** — not
`hacc`, `hFS`, `hbind`, `hvk`, `hrep`, `hξ`, `hr`, `htpos` — is used. So the statement is
provable independently of its proof term: it does not establish the documented claim ("from
a genuine `verify = true`, the AGM path delivers the guarded `Satisfies` — the assembled
witness table of the algebraic prover's own per-chunk representations"). The statement pins
neither the bad sets nor `wTab` to prover data; that content exists only in the (out-of-scope)
proof.

**Contrast (why this is a regression, not endpoint design).** The family-level
`kimchiProof_sound_algebraic` (`Capstone/Algebraic.lean:276`) is **immune**: its `∃`-sets
precede the *universally* quantified `β γ α ζ ξ r`. The run-level `hξ/hr` hypotheses are
immune because `badXiOf`/`badROf` are **named `def`s** of `(σ, aRef, x, E)`, not existentials.
The defect is specifically the `∃`-placement in the *run-level* conclusion, where the
universals get instantiated at the fixed `runOracles` values but the bad sets are
re-existentialized afterward. `kimchiVesta_run_sound`/`kimchiPallas_run_sound`
(`Capstone/Standard.lean`) share the shape (see M5).

**What the theorem should say.** Expose the canonical bad sets as named functions of the
prover data (exactly as `badXiOf`/`badROf` already are), pin
`wTab := extractTable idx.omega (assembledRow … aRef …)` in the statement, or state the run
root so the `∃`-sets precede a `∀`-challenge family — and add an honest scope note that the
run-oracle guards (`runOracles ∉ badZ`, and `hξ/hr`) are *not* discharged in-development
(that is the deferred forking/density model).

**Verdict: Critical. VERIFIED (author-direct).**

### C2 — EndoMul constraint order and sign diverge from Rust (definition drift)

**Definition.** `Kimchi.Gate.EndoMul.constraints` (`kimchi/Kimchi/Gate/EndoMul.lean:132`),
consumed by `Kimchi.Protocol.Linearization.gateLinearization`/`ftEval0`
(`Linearization.lean:81, 110`).

**Reading at issue (VERIFIED, author-direct).** `gateLinearization` weights each gate's
constraint list by its selector and combines it with `alphaCombo α L = Σ_k α^k · L.getD k 0`
— **positional** α-powers (`Linearization.lean:61`). `EndoMul.argument.constraints` is a
verbatim read-through of `Gate.EndoMul.constraints` with no reordering (`Lift.lean:438-440`).
So the list order fixes which α-power multiplies which constraint. Comparing the two lists:

| position | Lean (`EndoMul.lean:132`) | Rust `constraint_checks` vec (`endosclmul.rs:524`) |
|---|---|---|
| first | window-1 slope, x, y (3) | `boolean(b1..b4)` (4) |
| next | window-2 slope, x, y (3) | window-1 slope, x, y (3) |
| next | distinct-point `inv` check | window-2 slope, x, y (3) |
| next | `boolean(b1..b4)` (4) | `n_constraint` |
| last | `n_constraint` | distinct-point `inv` check |

and the scalar-register constraint is **negated**: Lean `nPrime − (16n+8b1+4b2+2b3+b4)`
vs Rust `(16n+8b1+4b2+2b3+b4) − n_next` (`endosclmul.rs:517-522`; `nPrime = n_next`).

**Failure scenario.** For any evaluation record with `emulSelector ≠ 0`, the positional
α-weighted sum differs (different constraints at α⁰…α¹¹, plus one sign flip), so
`gateLinearization`, hence `ftEval0` (`Linearization.lean:121`), hence `kimchiVerify`'s
combined-inner-product (`Verifier/Kimchi.lean:450`), computes a different field element than
production's `PolishToken::evaluate(constant_term)` (`verifier.rs:479`). The Lean-modeled
verifier and the deployed verifier therefore accept different sets on EndoMul-active circuits
— which include real pickles step circuits.

**Why undetected.** Every fixture the CI drivers use has `emul_selector = ['0','0']`
(`fixtures/linearization_vesta.json`, `kimchi_proof_vesta.json`, `*_nc2.json`), so the
EndoMul term is multiplied by zero in every value check — `check_linearization` and
`check_kimchi_verifier` are blind to this gate's ordering. (VarBaseMul, similarly masked,
was checked by the panel to match Rust exactly, incl. the `n_next`-first orientation
`VarBaseMul.lean:196`; EndoMul is the sole divergent gate.)

**Internal-validity note.** Gate `Holds`/soundness are order-insensitive (they demand the
*set* of constraints vanish), and the Lean linearization↔aggregate identity is internally
consistent because both sides use the same Lean order. So no Lean soundness theorem is
internally false — what breaks is the *fidelity* claim "`kimchiVerify` transcribes
`verifier.rs`" on EndoMul rows.

**Caveat for remediation.** The reference checkout's two most recent commits are
`370f13c59a`/`263d9cb737` "update endosclmul gate", and the project ledger records a pending,
not-started `proof-systems` endomul bump. The correct fix (reorder the Lean list to Rust's
`[bool×4, window1, window2, n_constraint, distinct-check]` and un-negate `n_constraint` —
`Holds` consumers are order-insensitive, so only linearization-value proofs and fixtures are
affected) must be reconciled with which endosclmul version deployed mina actually runs, and
a fixture whose circuit *contains* EndoMul rows must be added so the mask is closed.

**Verdict: Critical (definition diverges from Rust). VERIFIED (author-direct), with the
endomul-version reconciliation caveat.**

---

## Major findings

### M1 — Poseidon `absorb_g` identity-point encoding (definition drift)

`Poseidon.FqSponge.absorbG` (`poseidon/Poseidon/FqSponge.lean:76`) absorbs a **single** `0`
for the identity point (`if P = 0 then absorbFq spec s [0]`). Rust `DefaultFqSponge::absorb_g`
absorbs **two** zeros — `self.sponge.absorb(&[zero]); self.sponge.absorb(&[zero])`
(`sponge.rs:337-339`; trait comment `:23` "the values `(0, 0)` are absorbed"). **VERIFIED
(author-direct).** The Lean docstring's claim "a single `0` for the identity (sponge.rs
absorb_g, both cases)" (`:28, :74`) directly contradicts the cited source. Because
`Poseidon.absorb` is a per-element duplex fold, one element vs two shifts the rate position
for everything absorbed afterward, so all subsequent challenges diverge whenever an absorbed
point (a `w/z/t_comm` chunk, or an IPA `L/R/δ`) is the identity — an adversarially reachable
input class the fixtures never exercise. Consequence: `Ipa.verify`/`kimchiVerify` compute a
different transcript than production there, so the soundness headlines' antecedent neither
implies nor is implied by deployed acceptance on identity-carrying proofs. (One panel rated
this Critical; the soundness impact is bounded — identity commitments are honestly
unreachable — so Major, but the false docstring should be fixed regardless.)

### M2 — IPA acceptance: two exact equations vs one randomized MSM (definition drift)

`Ipa.verify`/`verifyFrom` decide `schnorr && sgOk` — two exact equations as separate
`decide`s (`bulletproof-pcs/Bulletproof/Wire.lean:244-258`; the kimchi copy at
`Verifier/Kimchi.lean:266-270`). **VERIFIED (author-direct):** the Lean check is a
conjunction. Rust `SRS::verify` folds every proof's Schnorr residual (× `rand_base^i`) and
sg-correctness residual (× `sg_rand_base^i`) into **one** MSM checked against zero
(`ipa.rs`); at batch slot 0 both randomizers are 1, so the deployed check there is the single
equation `R_schnorr + R_sg = 0`, strictly **weaker** than the conjunction. Since `sg` is
never absorbed into the transcript, an attacker can (after fixing all challenges) solve for
an `sg` making the *sum* vanish while neither residual is individually zero — accepted by
production, rejected by Lean. So `ipa{Vesta,Pallas}_sound` and the kimchi capstones prove
soundness of a *stronger* acceptance predicate than the deployed one: a production-accepted
proof at slot 0 can fall outside every theorem's antecedent. The safe direction
(Lean-accepts ⟹ deployed-accepts) holds; whether the summed check is itself knowledge-sound
is unmodeled. `Protocol.lean:181` calls `rand_base` "cross-proof batching, out of scope" but
misses that `sg_rand_base` merges the two per-proof equations deterministically at slot 0.

### M3 — Fiat–Shamir axioms over-quantified over unconstrained SRS (axiom strength)

`Bulletproof.poseidon_fiat_shamir_{vesta,pallas}` (`Reflection.lean:190, 200`) and
`Kimchi.Verifier.kimchi_fiat_shamir_{vesta,pallas}` (`Capstone/Reflection.lean:56, 73`)
quantify `∀ (σ : SRS …)` with **no constraint on σ** — `Bulletproof.SRS` is a bare structure
(`Protocol.lean:38`), so `σ` may be degenerate (`g = 0`, `h = 0`). At such `σ`, an accepting
run exists (the Schnorr equation is solvable via prime-order cyclicity, which the pasta
package carries), yet `FiatShamirTreeB`'s conclusion forces, through `ipa_soundV`
(`SingleOpening.lean:253`), a witness with `commitGen σ.g a = P − ρ•σ.h = 0`, i.e. `P = 0` —
false whenever the combined commitment is nonzero. So the axioms are **false as propositions
of classical mathematics**; the environment is inconsistent in principle (deriving `False`
requires exhibiting one concrete accepting degenerate instance, so no short refutation
exists). The asymmetry is the finding: `hbind`, of the *same* epistemic status, is
deliberately carried as a **hypothesis** and loudly documented as info-theoretically false
(`Soundness.lean:104-108`), while the FS assumptions are asserted as global axioms with prose
("the Poseidon sponge provides a valid Fiat–Shamir transform … no arithmetic content") that
frames them as a plausible ROM assumption. What is actually assumed is the *conclusion of the
forking/tree-extraction lemma at probability 1 with its knowledge-error discarded, over all
SRS and all wire inputs*, plus the Schnorr/hiding de-blinding and the scalar-equation↔tree
correspondence. **A strict reading is Critical** (a refutable axiom in the declared trust
surface); rated Major because the guarded downstream theorems don't propagate the falsity to
a false conclusion and the honest fix is local: restrict `σ` to the deployed/nondegenerate
class (or demote to a hypothesis in the `FiatShamirTreeB` style already used everywhere
else), and give the FS axioms the same "false at real/degenerate parameters, computational
idealization, probability loss discarded" caveat `hbind` already carries.

### M4 — Terminal roots require an unenforced `htpos` (weakened conclusion)

`kimchi{Vesta,Pallas}_run_sound_algebraic_ft` and `run_sound_algebraic_ft` carry
`htpos : 0 < cp.tComm.size` (`Capstone/Reflection.lean:1097, 1309, 1367`), **omitted from the
docstrings' explicit "hypothesis surface carried by the statement" enumeration** (which lists
`aRef/ρRef`, `aT/ρT`, `hξ/hr`, `Corresponds`, `hbind`). **VERIFIED (author-direct):** the
checked record enforces only `tComm_le : tComm.size ≤ 7·nc` (`Kimchi.lean:117`, `Wire`
parse), faithfully mirroring Rust's upper-bound-only `t_comm.len() > chunk_size*7`
(`verifier.rs:260`); `kimchiVerify`'s only argument-dependent guards are the two public-size
bounds; and `Ipa.combineCommitments` on an empty array is total (yields 0). So
`kimchiVerify … = true` is reachable with `tComm = #[]`, and production accepts it too
(`PolyComm::chunk_commitment` folds empty chunks to the zero point) — yet that deployed-
accepted run is **outside** the terminal theorems (`htpos` is needed downstream by
`ft_identity_of_chunks`/`ftChunkAssembly_natDegree_lt`, where `nt = 0` breaks the degree
argument). Honest provers always emit `7·nc` chunks, so the gap is an excluded *adversary*
class — exactly what a soundness statement exists to cover. Fix: enforce non-emptiness at the
wire/verifier boundary (a declared deviation from Rust), or scope the roots.txt/docstring
claim to nonempty quotient commitments, or discharge the degenerate `t := 0` case.

### M5 — Standard-model run-level roots vacuously satisfiable (quantifier order)

`kimchiVesta_run_sound`/`kimchiPallas_run_sound` (`Capstone/Standard.lean:269, 349`) have the
same `∃-bad-sets-after-cp` shape as C1: the witness
`⟨∅, _↦∅, _↦_↦{(runOracles …).alpha}, _↦_↦_↦_↦∅, 0⟩` proves the full conclusion with none of
the fifteen hypotheses used (`1 ≤ n·(gateAlphaCount+permAlphaCount−1) = 23·n`, `n ≥ 1`). The
parent `kimchiVesta_sound` (`:164`) is *not* vacuous (its `∃` precedes the `∀`-challenges), so
the counting style is compatible with a non-vacuous statement — this is purely the
`∃`-placement relative to `cp`. Rated Major (not Critical) because these are the
standard-model secondary roots, not the terminal capstones; the fix is identical to C1.

### M6 — `KimchiVK.Corresponds` "adjudicated numerically" overclaims (doc drift)

`KimchiVK.Corresponds`'s docstring (`Capstone/Reflection.lean:581`) and the terminal roots'
"the checked `KimchiVK.Corresponds`" claim that it is "adjudicated numerically, per chunk, by
`check_vk_correspond`." The driver checks only the **relative** identity (column chunk
commitments = value-MSM against the key's *own* `lagrange_basis` chunks), never reads the SRS
generators, and runs on **Vesta only** ("Pallas has no index fixture"). The **absolute** pins
— `VKCorresponds` (`comms = indexerOf σ`, i.e. `commitPolyChunk` equalities against the SRS)
and the load-bearing Lagrange conjunct that `publicCommitment_corresponds` uses to bind the
public input into `Satisfies` — are machine-checked nowhere, and nothing is adjudicated for
Pallas. So `hvk`'s truth at the fixture additionally trusts that the recorded `lagrange_basis`
is the true chunked Lagrange commitment family of the fixture SRS. Trust-surface prose
overstates what the driver establishes.

### M7 — CI axiom-gate wrapper omits the FS axioms (doc drift)

`kimchi/scripts/check_axioms.sh:2-4` says the gate fails unless every axiom is "the standard
logical set plus the two trusted Pasta point-count axioms" — omitting the four FS axioms the
`.lean` allowlist actually permits (`check_axioms.lean:71-84`) and which are in the terminal
theorems' real closure. An auditor reading the CI wrapper concludes the headline closure is
Fiat–Shamir-free, which it is not. (The `.lean` driver is accurate; only the shell header
drifted. Same header also over-claims "imports both libraries.")

### M8 — `isTrustedNativeDecide` is a prefix match, and inherited `native_decide` trust is broader than "point counts" (axiom strength)

`isTrustedNativeDecide` (`check_axioms.lean:86-95`) is documented as "CompElliptic's point
counts … exactly those declarations, by name," but the CompElliptic arm is a **namespace
prefix match** (`"CompElliptic.".isPrefixOf`), not a by-name whitelist. And the terminal roots'
closure inherits CompElliptic `native_decide` certificates beyond point counts — the
Tonelli–Shanks 2-adic root-of-unity order certificates (`Fields/Sqrt.lean`), entering via
Poseidon's SvdW `group_map`. The compiled-code trust base is ~7 per-declaration certificates
(2 point counts + 4 sqrt-order legs + 2 eigen anchors), while the gate prose says "point
counts + anchors." All certificates are concrete closed facts consistent with CompElliptic's
discipline — the trust is defensible, only its description is wrong.

### M9 — `formal/CLAUDE.md` and `Standard.lean` trust story describe a deleted axiom boundary and omit the real axioms (doc drift)

`formal/CLAUDE.md` (package table; "The three layers"; "The axiom boundary
(Cycle/Axioms.lean, Cycle/Pasta.lean)"; "Axiom discipline") describes a `Kimchi/Cycle/` layer
with a `CMCurve`/`TwoCycle` structure and free axioms `pallas_order_smul`/`pallas_eigen`/`lam`,
and calls pasta's contents "the **Hasse/CM axioms**." **VERIFIED:** `kimchi/Kimchi/` has no
`Cycle/` directory and no `CMCurve` anywhere; the pasta package declares **zero** axioms (the
eigen relations are theorems). The actual trust surface — the four free top-level FS axioms —
is the exact pattern the doc's "axiom discipline" section forbids, and it is never mentioned.
Separately, `Standard.lean:17-21`'s "Trust story" for the standard-model capstones enumerates
only the grid hypothesis and the FS axioms and then claims "everything else proved," silently
dropping `hbind` (present in all four theorems, `:169/:217/:276/:356`) — the one hypothesis the
development itself calls info-theoretically false — and `hvk`/`hpubC`. An auditor following
these docs gets the trust surface wrong in both directions.

### M10 — `Protocol.sound`/`kimchiProof_sound` bad-sets placed after `z`/reference data (quantifier order)

In `Kimchi.Protocol.sound` (`Equation.lean:498`) the `∃ badB badG …` sits inside the scope of
the accumulator polynomial `z`; in `kimchiProof_sound` (`Reduction/Soundness.lean:563`) inside
the scope of the whole reference grid `ζ₀/E₀/ξ₀/r₀`. In the deployed transcript `z` and the
reference runs are fixed only *after* `β/γ` are squeezed, so the statement permits `badB =
f(z)` and the documented "quantified BEFORE the challenges" SZ discipline is not delivered for
`badB/badG` w.r.t. `z`. **This is not a vacuity** (the Critical trigger — a bad set depending
on the challenge it guards — is absent: `badB` precedes `∀β`; `badG` takes `β` and guards `γ`;
`badZ(…,t)` guards `ζ` and `t` legitimately precedes `ζ`). The proof builds `badB/badG` from
the extracted witness table only (z-free), so the stronger statement is provable — but the
current statement is materially weaker than its own construction on exactly the axis the
deferred forking/density discharge will need. Fix: bind `badB/badG` before `z`/the grids, or
state them as explicit functions of `(idx, pub, W)`.

### M11 — IPA wire-parse guards misattributed to production checks (doc drift)

`Bulletproof.Ipa.Wire.{Proof,Input}.check` docstrings (`Bulletproof/Wire.lean:26-30, 299-308`)
call the round-count and evals-squareness parses "the verifier's own dimension guards …
the same observable behavior as the guards' false returns." Rust `SRS::verify` has **no**
such guards: `OpeningProof::challenges` folds over `lr` with no length check; a short `lr` is
accepted with prefix-SRS semantics, a long one panics (indexes past the pre-sized scalars
vector); and the eval matrix is never read by verify (the caller supplies
`combined_inner_product`). So the parse is an undeclared *modeling strengthening* presented as
a transcription — a production-accepted short-`lr` run has no Lean counterpart. Kimchi's
`Wire.lean` correctly declares its `w_comm/z_comm` pins as strengthenings but leaves the `lr`
pin unclassified. Fix is prose-only: classify these as declared strengthenings with the
honest fidelity-direction caveat.

---

## Minor findings

Grouped by theme; all **REVIEWED (single-pass)** — not adversarially refuted. Every one is
prose/coverage drift with no effect on a statement's internal validity unless noted.

**Terminal / capstone prose.**
- `htpos` also omitted from the roots.txt hypothesis surface (subset of M4).
- `run_sound` docstring "the quotient residue stays the one undischarged antecedent" undercounts:
  `hζ1`/`hζb` are also undischarged hypotheses and the four ∉bad guards remain in the conclusion
  (`Standard.lean:266`).
- `run_sound` headlined "soundness of the deployed verifier" but no statement consumes
  `kimchiVerify = true`; the deployed verifier enters only via `runOracles` values + a posited
  grid; preamble misplaces the run corollaries "in the reflection layer" (they are in the same
  file) (`Standard.lean:8-22`).
- roots.txt block over the `run_sound` pair claims they include "the AGM corollary with the
  residue-free algebraic quotient" — that belongs to the `_ft` roots below; the #260 rewrite
  dropped the residue/grid-is-a-hypothesis caveats from the manifest (`roots.txt:80-85`).
- `ft_opening_of_reflected_*` docstring cites "a genuine `KimchiVesta.verify … = true`" (no such
  declaration; hypothesis is the weaker `Ipa.verifyFrom`), and cites `ReflectedRun.accepts`
  (no such structure; only `docs/chunking-plan.md`) (`Reflection.lean:335, 11, 43`).
- roots.txt entry for `ft_opening_of_reflected_*` omits the `hbind`/AGM/good-challenge
  qualifiers the statement carries (`roots.txt:86-88`).
- Private `card_badXiOf_le`/`card_badROf_le`/`ftChunkAssembly_natDegree_lt` are not exported, so
  the `hξ/hr` non-vacuity and the `badZ` side-condition are not consumable from the public
  surface (`Algebraic.lean`).
- Stale pre-public-in-batch numbers: "43-row batchC", "`≤ 84 = 2·(43−1)`", and `batchC wC zC
  comms` (missing `pubC`) — `batchC` is 44 rows and the bound is `2·(44·nc−1)`
  (`Algebraic.lean:17, 50, 59, 68, 85, 116`).

**Executable-verifier fidelity.**
- `ftEval0` uses total field division (0 at zero denominator) where Rust `.expect("negligible
  probability")` panics on `ζ ∈ {1, ω^(n−zkRows)}` — Lean may accept where production aborts
  (safe direction for soundness) (`Linearization.lean:119`).
- "the verifier rejects `σ.k > domainLog2`" is false — no such guard exists in `kimchiVerify`;
  the regime is excluded only client-side and by capstone hypothesis, and production accepts it
  (`Kimchi.lean:39`; three panels).
- `max_poly_size` (a serialized, adversary-controlled VK field on the verify path) is silently
  identified with the trusted SRS width `2^σ.k`, not named in the deferral list (`Wire.lean:70`).
- `KimchiVK.endo` documented as serde data "verifier_index.endo" but is `#[serde(skip)]` in
  production (caller-supplied constant); unlike `digest` it carries no "input here" flag
  (`Wire.lean:100`).
- The 44-row batch "to_batch order with the ft row omitted" also silently omits the recursion
  (`polys`) rows and optional-gate rows (declared elsewhere, not here) (`Reduction/Soundness.lean:110`).
- Corruption-matrix coverage gaps: the raw public-input array is never corrupted; VK corruption
  is only parse-level (never a bumped commitment or wrong `digest`); the `s`/coefficient/selector
  evaluation families and the opening `sg/δ/z1/z2` are never corrupted at verify level; nc=1
  exists only on Vesta though the success line reads "both curves" (`check_kimchi_verifier.lean`,
  `check_ipa_fixture.lean`).

**Protocol / reduction prose.**
- `Protocol.sound` docstring says one accepting tuple "outside explicit counted bad sets" forces
  satisfaction, omitting the two uncounted exclusions `ζ ≠ 1`, `ζ ≠ ω^(n−zkRows)` and the
  `deg t < 7n` guard on the `badZ` bound (`Equation.lean:482-512`; consumers carry them).
- `kimchiProof_sound` trust-boundary line ("acceptance + binding + correspondence compose into
  Satisfies") omits the load-bearing `hteq` (Maller/ft identity with a free `t`)
  (`Reduction/Soundness.lean:33`).
- Permutation-vanishing-mask section prose says `zkpm` ranges over the full `[n−zkRows, n)`
  window — true only at `zkRows = 3`; the definitions are correctly three-factor
  (`Equation.lean:207`).
- `bound_unique` docstring's "per (β,γ) accumulator row" describes a structure no consumer has
  (`zC` is one commitment fixed across the grid) (`Reduction/Soundness.lean:48`).
- `Aggregate.lean` module docstring describes the retired injective-α-grid/Vandermonde
  separation and lists `dvd_separation` as file content; the file defines only `aggregate`, and
  the real `dvd_separation` (in `SchwartzZippel.lean`) is single-challenge counting.
- `kimchiProof_sound` bad-sets after reference-grid data (F68) — same family as M10, harmless in
  the deterministic-counting reading.

**Axiom / trust-surface prose.**
- `poseidon_fiat_shamir_*` "sole non-standard axiom of `ipaVesta_sound`" ignores `Lean.ofReduceBool`
  in the closure (via CompElliptic point-count Module instances) (`Reflection.lean:190`).
- `kimchi_fiat_shamir_*` "no arithmetic content" understates the bundled scalar-equation↔tree
  and derived-base↔SRS correspondences (bulletproof's own scope note discloses them)
  (`Capstone/Reflection.lean:12, 41`).
- FS-axiom transcript is the cold-start `Ipa.verify` (sponge never absorbs the commitments,
  points, or the two combination scalars) — the axiom does not bind the statement, undocumented
  (`Bulletproof/Reflection.lean:185`).
- `commitmentBinding_iff_no_relation` headline says "DL-relation **hardness**" but proves
  equivalence with DL-relation **triviality** (info-theoretic); the file defines hardness as the
  distinct computational assumption two lines above (`SingleOpening.lean:305`).
- `chunked_ipa_soundness`/`chunked_batch_soundness` docstrings attribute the conclusion to
  "binding + accepting run," dropping the FS-tree hypothesis (which carries all the extraction —
  acceptance is logically inert); `chunked_batch_soundness` summary says "pairwise-distinct
  pairs" but the binder needs the full injective `N×m` grid (`Soundness.lean:329, 403`).
- `hbind` scope note "discharged elsewhere" (nothing discharges it), and a dozen dead
  cross-references to modules deleted in the #248 reorg (`Soundness/Batch.lean`, `ChunkedBatch.lean`,
  …) — including the pointer that is supposed to carry the `hbind` vacuity scoping.
- pasta `check_axioms.sh` wrapper still says "Hasse + … (eigen is downstream-only)" — no Hasse
  axiom exists and eigen is a gated root; `EndoMul`/`VarBaseMul`/roots.txt call the eigen/point-count
  theorems "the CM axiom"/"a point-count axiom" (they are theorems + trusted `native_decide`).
- `ipa{Vesta,Pallas}_sound` `hm : 0 < p` named after `chunked_batch_soundness`'s point-count `m`
  but constrains `p` (`Reflection.lean:280`).
- `KimchiBatchAcc` "forking/rewinding idiom" — the discharging event is really programmable-oracle
  reprogramming at the polyscale/evalscale squeezes (deterministic FS rewinding cannot vary
  ξ/r), and the hypothesis is a full ξ×r rectangle sharing `r`, not a tree (`Standard.lean:61`).

**Missing non-vacuity witnesses.**
- No exported completeness/non-vacuity statement at the `Accepts`/`Protocol.sound` level: the
  reverse direction exists only as private `verifierEquation_iff` + the Index-layer iff, and no
  fixture ever evaluates `Accepts` to true (the honest quotient `t` never materializes)
  (`Accepts.lean`, `Equation.lean`).
- No formalized non-vacuity witness for the abstract PCS soundness statements: `hbind` is
  unsatisfiable at every real σ, so each concrete capstone is a classically vacuous conditional;
  a contradiction hidden in the abstract hypothesis package would go undetected. A free-module
  `example` (`G := (Fin (2^k)→F)×F`, `σ.g i := (single i 1, 0)`, `σ.h := (0,1)`) would close it
  (`Soundness.lean:225, 403`).

---

## D3 — Trust-surface statement (for an external reviewer)

The verified soundness of the deployed kimchi verifier, as this development establishes it,
rests on the following and nothing else:

1. **Three standard logical axioms** — `propext`, `Classical.choice`, `Quot.sound`.
2. **`Lean.ofReduceBool`** — trusting the Lean compiler for the `native_decide` certificates
   inherited from the vendored `CompElliptic` package. Concretely these certify the Pasta
   curve **group orders** (unconditionally, via CompElliptic's elementary fibre-bound argument
   `#E ≤ 2·#F+1` — *not* a Hasse axiom), the **GLV eigenvalue** anchors
   `Pasta.{pallas,vesta}_lam_nsmul_Gpt`, and — reached through Poseidon's SvdW `group_map` —
   **Tonelli–Shanks 2-adic root-of-unity order** certificates. The pasta package itself declares
   **no axioms** (M8 corrects the "point counts only" description; M9 corrects docs that still
   call these "Hasse/CM axioms").
3. **Four Fiat–Shamir axioms** — `Bulletproof.poseidon_fiat_shamir_{vesta,pallas}` (for the IPA
   PCS heads) and `Kimchi.Verifier.kimchi_fiat_shamir_{vesta,pallas}` (for the kimchi terminal
   `_ft` roots). Each asserts that an accepted run admits a de-blinded accepting special-soundness
   **transcript tree** — i.e. it *packages the conclusion of the Fiat–Shamir/forking extraction
   lemma at probability 1*, folding in the ROM idealization of the Poseidon sponge, the rewinding,
   the Schnorr/hiding de-blinding, and the scalar-equation↔tree correspondence. Independence: the
   kimchi pair is not derived from the poseidon pair, and each terminal root consumes exactly one
   kimchi FS instance. **Caveat (M3):** as *stated* these axioms quantify over all SRS including
   degenerate ones and are therefore in-principle false; they are meaningful only when read at the
   deployed hash-derived SRS, and — unlike `hbind` — they are not documented as such.
4. **The `hbind` DL-relation hypothesis** — carried as an explicit per-theorem hypothesis (never
   an axiom): no nontrivial discrete-log relation among the SRS generators. Information-theoretically
   false at real parameters; meaningful only as the computational binding assumption. Honestly
   documented at the definition site (but not repeated in the standard-model capstones' trust
   story — M9).
5. **Per-transcript computational hypotheses carried in the terminal statements** — the AGM
   SRS-basis representations (`aRef/ρRef/aT/ρT`), the good-combination-challenge guards (`hξ/hr`),
   the key–index correspondence `KimchiVK.Corresponds` (adjudicated only relatively and only on
   Vesta — M6), and `htpos` (M4).

**What is *not* covered by the above and must be understood as a gap:** (i) the run-oracle
challenge-avoidance guards in the terminal conclusions are *not discharged* — that is the deferred
forking/density model, and as written the terminal statements are additionally vacuously
satisfiable (C1); (ii) the executable verifier is not, on this audit, a faithful transcription of
`verifier.rs` on EndoMul-active circuits (C2), on identity-carrying inputs (M1), or with respect
to the deployed single-MSM acceptance (M2); (iii) the FS axioms in their stated (unrestricted-σ)
form are inconsistent (M3).

## D6 — Claim-gap register

For each prose claim about what is proved, whether it is scoped to exclude the known deferrals
(forking/density model; `hbind` as hypothesis; recursion/`prev_challenges` deferral; lookups
absent; the sub-SRS regime):

| Claim (source) | Scoped? | Finding |
|---|---|---|
| "AGM soundness of the deployed verifier at production chunking" (roots.txt, ledger) | Partially — omits that the terminal statement is vacuously satisfiable and that the run-oracle guards are undischarged | C1 |
| "From a genuine `verify = true` … deliver the guarded `Satisfies`" (roots.txt:95) | No — omits `htpos`; the guards are undischarged | M4, C1 |
| "transcribed from `verifier.rs`" (`Kimchi.lean` preamble) | No — diverges on EndoMul rows, identity absorbs, and the summed IPA check | C2, M1, M2 |
| FS axioms = "Poseidon provides a valid FS transform, no arithmetic content" | No — understates (probability-1 tree extraction over all σ) | M3 |
| "the grid is a HYPOTHESIS, one FS axiom per node, everything else proved" (`Standard.lean`) | No — omits `hbind`, `hvk`, `hpubC` | M9 |
| "the quotient residue is the one undischarged antecedent" (`run_sound`) | No — `hζ1/hζb` + guards also undischarged; and the roots are vacuous | Minor, M5 |
| "adjudicated numerically by `check_vk_correspond`" (`Corresponds`) | No — only relative, Vesta only | M6 |
| CI gate = "standard logical + two Pasta point-count axioms" (`check_axioms.sh`) | No — omits the four FS axioms | M7 |
| pasta = "the Hasse/CM axioms"; `Kimchi/Cycle/` axiom boundary (`CLAUDE.md`) | No — describes deleted structure; omits real FS axioms | M9 |
| "binding is exactly DL-relation hardness" (`commitmentBinding`) | No — proves triviality, not hardness | Minor |
| "the verifier rejects `σ.k > domainLog2`" | No — no such rejection; production accepts it | Minor |
| Wire IPA parses = "the verifier's own dimension guards" | No — production has no such guards | M11 |
| lookups absent, `prev_challenges`/recursion deferred, digest an input, sub-SRS out of scope | **Yes** — declared in the `Kimchi.lean`/`Wire.lean` preambles | — |
| counting (non-probabilistic) bad-set style is deliberate; `hbind` a hypothesis | **Yes** — established design, honestly documented | — |

**Definitive "what this development does and does not establish":** *It establishes, kernel-checked
and axiom-audited, that the abstract kimchi protocol is sound (`Protocol.sound`) and that a
per-chunk AGM-representable prover whose single reflected opening is accepted, under DL-binding and
the Fiat–Shamir tree assumption, yields a satisfying witness table — for the **Lean-modeled**
verifier, over the deployed gate set without lookups or recursion. It does **not**, as the
statements currently stand, establish (a) that this holds non-vacuously at the deployed run (the
terminal run-level roots are trivially satisfiable — C1/M5, and their challenge-avoidance guards are
undischarged), nor (b) that the Lean-modeled verifier faithfully transcribes `verifier.rs` on
EndoMul-active circuits, identity-carrying inputs, or the deployed summed IPA check (C2/M1/M2). The
Fiat–Shamir axioms as written are inconsistent in principle (M3).*

---

## Follow-up worklist (proposed, unscoped)

Ordered by severity; each is statement/prose-level unless noted.

1. **C1/M5 — de-vacuate the run-level roots.** Restate `run_sound_algebraic_ft`,
   `kimchi{Vesta,Pallas}_run_sound_algebraic_ft`, and `kimchi{Vesta,Pallas}_run_sound` so the bad
   sets are named functions of the prover data (like `badXiOf`) with `wTab` pinned, or so `∃`-sets
   precede a `∀`-challenge family; add a scope note that the run-oracle guards are undischarged.
2. **C2 — fix the EndoMul linearization.** Reorder `Gate.EndoMul.constraints` to Rust's
   `[bool×4, window1, window2, n_constraint, distinct-check]` and un-negate `n_constraint`;
   reconcile with the pending endosclmul-version bump; add a fixture whose circuit contains EndoMul
   rows so the `emul_selector = 0` mask no longer hides it. (Touches linearization-value
   proofs/fixtures only; `Holds` consumers are order-insensitive.)
3. **M3 — repair the FS axioms.** Restrict `σ` to the deployed/nondegenerate class (or demote to a
   `FiatShamirTreeB` hypothesis à la `hbind`); give them the same "false at degenerate parameters,
   computational idealization, probability loss discarded" caveat.
4. **M1/M2 — executable-verifier fidelity.** Make `absorbG` absorb two zeros for the identity (and
   fix its docstring); model the deployed single randomized-MSM acceptance (or scope the
   "deployed verifier" headline to the derandomized two-equation predicate and document the gap).
5. **M4 — `htpos`.** Enforce non-emptiness at the wire boundary (declared deviation) or discharge
   the `t := 0` case or scope the claim; list `htpos` in the hypothesis-surface prose.
6. **M6/M11 — fixture/parse honesty.** Correct the `Corresponds` "adjudicated numerically" claim and
   the IPA wire-parse "production guard" claims to declared strengthenings; note Pallas has no index
   fixture.
7. **M7/M8/M9 — trust-surface docs.** Update `check_axioms.sh` headers to name the four FS axioms;
   correct `isTrustedNativeDecide`'s "by name" prose and the "point counts only" description;
   rewrite `formal/CLAUDE.md`'s axiom-boundary/three-layers sections and `Standard.lean`'s trust
   story to the actual surface (four FS axioms + `hbind` + `ofReduceBool`), removing the deleted
   `Cycle`/`CMCurve`/"Hasse" references.
8. **Minor sweep.** The doc-drift and coverage items above (dead module cross-references, stale
   "43-row/≤84" numbers, `ReflectedRun`/`KimchiVesta.verify` dangling names, the "verifier rejects
   σ.k>domainLog2" claim, the missing corruption classes, the missing free-module non-vacuity
   `example`). Individually cheap; collectively they are what an external reviewer reads first.

---

*Audit executed as a multi-agent workflow (D1–D6 finder + judge panels complete; adversarial
refuter stage not run — cut by session/credit limits). All Critical and Major findings
re-verified against source by the lead auditor (verifications cited inline); Minor findings
single-pass reviewed. No code was modified.*
