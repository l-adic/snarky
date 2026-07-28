# Follow-up register — the external audit of `formal/`

**Purpose.** This is the forward-looking residue of the external audit engagement
(`external-audit-sow.md` → `external-audit-report.md` → `external-audit-response.md`). It exists so
that someone picking this up months from now can act without re-reading three long documents or
re-deriving what was already settled. It records what is **open**, what is **closed and must not be
re-litigated**, what would **silently regress** if the guards were removed, and what to **re-check
on the next proof-systems bump**.

**Status at close (2026-07-28, `c49054e4`).** Every finding the engagement raised is either fixed
and independently verified by the auditors, or deferred with a recorded rationale. Three deferrals
stand. All gates green: axiom gates at kimchi 52 / bulletproof-pcs 30 / poseidon 19 / pasta 13 /
snarky 5; both locked-target gates; sorry census; dead code 0 of 1545; fixture manifest 32 files at
`mina 3969f761846e`; all eleven fixture drivers; full regeneration byte-identical.

---

## The three open items

### O-1 (substantive) — a proved extractor-cost bound

**Audit ID:** E-1. **Deferred with sign-off.** This is the only open item that changes what the
endpoints are worth.

**What is open.** `ReductionEfficient` gates the discrete-log hypothesis on a call bound `R`, but
no theorem in this tree bounds the extractor's cost, so `R` is supplied by
`reductionEfficient_exists` — which obtains *some* `R` by a sup without inspecting the counter.
Since ε bounds the DL advantage of one specific algorithm (`fam.relationFinder coins`, which runs
the forking extractor), a generic-group grounding of ε needs a cost bound we do not have. ε is
therefore **assumed for the finder** rather than derived from a time bound.

**What closing it buys.** It converts the endpoints from "knowledge soundness with an extractor of
unproved cost" into a proof of knowledge with a stated extraction cost, and makes ε derivable from
`t²/2²⁵⁴` instead of posited. That is the difference between a concrete-security claim and a
structural one.

**Do not repeat the reasoning error this replaced.** Until the audit, two docstrings argued from
`Complete`'s `2¹²⁸`-long order lists to an astronomical honest `R`. That inference is wrong and the
prose is now corrected: `Complete` is a *search-completeness* condition (it is what makes
non-escape imply extraction), not a cost condition; and a table on which the adversary **loses
costs exactly one run**, because `recursiveAlgebraicForkFrom` descends without rewinding, the leaf
returns `none`, and each level forwards `first.runs`. The exhaustive scan fires only on winning
tables. Since `ReductionEfficient` averages over oracle tables, it constrains
`P[win]·E[cost | win] + P[¬win]·1` — the classical expected-forking quantity, not the worst case.

**Entry points.**

| Piece | Location |
|---|---|
| Upstream conditional bound | `ExpectedRuns.lean:902` `recursiveAlgebraicFork_sum_runs_le_of_forkSpread` — `E[runs] ≤ (6·|F|/(σ₀−1))^k = (6/δ)^k` |
| Its hypothesis | `ExpectedRuns.lean:583` `ForkSpread σ₀` — a **uniform** (∀-table, ∀-node) good-challenge floor, i.e. a strong heavy-row condition, not an average |
| Our predicate (kimchi) | `Kimchi/Verifier/KnowledgeSoundness.lean:1758` `ReductionEfficient`, counting `attemptRuns` (`:1744`) |
| Our predicate (IPA) | `Bulletproof/Forking/KnowledgeSoundness.lean:620`, counting `DeployedFamily.attemptRuns` (`:614`) |
| The run counter itself | `Bulletproof/Forking/Game.lean:507` `kimchiExtractRuns` — a *projection* of the extractor's own recursion, deliberately never a separate definition |
| Only unconditional bound today | ironwood `Recursive.lean`, "Worst-case run bound": `≤ (2·|F| + 1)^k`, plus `reductionEfficient_exponential` (`Algebraic.lean:1440`) |

**The actual obstacle, so nobody mistakes it for plumbing.** The averaging axes differ. Upstream
sums over **tapes** for a fixed oracle table; our `ReductionEfficient` sums over **tables** for a
fixed tape. Bridging them is the work. Note the endpoints are ∀-tape, so a consumer is free to
instantiate at a favourable tape — the same probabilistic-method shape the upstream bound has,
which is the natural route.

**Quantitative regime, if plumbed.** `(6/δ)^k` at `k = 15`: `δ = 1/2` → ≈ `2^54` adversary calls
(fine for a reduction); `δ = 2^-20` → ≈ `2^339`, worse than solving DL outright. The exponent in
`k` is real, so any resulting claim must be scoped to adversaries whose per-round good-challenge
density is not tiny. Say so wherever the number is quoted.

**Also open upstream.** `ExpectedRuns.lean`'s own file docstring: "An unconditional polynomial AFK
bound remains open." Do not expect to find it there.

### O-2 — discharge the degenerate quotient (`t := 0`) and retire `htpos`

**Audit ID:** B-1 strong form. **Deferred with sign-off**, but see the cost note — it may be
cheaper than the deferral implies.

**What is open.** `KimchiFamily.htpos` (`KnowledgeSoundness.lean:863`) requires
`0 < tComm.size` of every run of every adversary in the family. Production checks only
`t_comm.len() ≤ 7·chunk_size` (`verifier.rs:260`) and processes an empty quotient fine. The wire
parse now **rejects** an empty quotient (`Wire.lean:163`, a declared strengthening with a driver
rejection case), and the restriction is stated in the fragment at every presentation surface — so
the gap is *declared* rather than closed. Attack shape #7 of the audit's C2 log remains a scope
boundary rather than a priced one.

**Cost note (worth scoping before assuming it is hard).** The load-bearing consumer is
`ftChunkAssembly_natDegree_lt` (`Capstone/Algebraic.lean:354`), whose `0 < nt` is genuinely
essential *to its own statement*: at `nt = 0` the assembly is the empty sum `0`, and the conclusion
`natDegree < nt·2^k` becomes `0 < 0`, which is false. But the downstream consumer,
`runBounds_zeta_at_assembly` (`Capstone/Reflection.lean:1273–1279`), needs only `natDegree < 7·n`,
and at `nt = 0` that is `0 < 7n`, true from `NeZero n`. So the degenerate branch plausibly closes by
a case split taking a different route, not by strengthening the degree lemma. The second consumer,
`ft_identity_of_chunks_of_eq` (`Reflection.lean:1181`), reduces at zero chunks to
`ft = pScalar·σ₆ − (ζⁿ−1)·0`, which also looks tractable. **Scope both before committing to an
estimate** — this note is a pointer, not a proof.

**What closing it buys.** The wire strengthening could then be dropped, making the Lean accepted
language exactly production's on this axis, and the endpoints would govern the empty-quotient
adversary instead of excluding it.

### O-3 — the randomized final check

**Audit ID:** V-4. **Deferred; no further work planned.** Production verifies one rng-weighted MSM
(`r₁·A + r₂·B = 0`, fresh `thread_rng`, `ipa.rs:249–254`); the Lean verifier checks the two bracket
equations as a deterministic conjunction (`Bulletproof/Wire.lean:254–268`). Lean-accept implies
production-accept with probability 1 — the conservative direction for soundness — and the
difference is a declared deviation in `Verifier/Kimchi.lean`'s preamble alongside the
singleton-`batch_verify` note. Recorded here only so a future reader does not rediscover it as a
finding.

**Accepted residual (not work):** lean4checker replays declarations through the kernel but does not
recompute the per-module axiom tables `collectAxioms` reads. Inherent to the tool; documented at
the CI step.

---

## Standing invariants — what would silently regress

Each of these was created in response to a finding and protects a property that has **already
failed once** or was demonstrably unprotected. Removing any of them re-opens the corresponding
hole, and in most cases the tree would stay green while doing so.

1. **Exhibit-existence pins** (`*/scripts/check_locked_target.sh`, 20 exhibits in bulletproof-pcs,
   6 in kimchi). Anti-vacuity exhibits are by construction consumed by nothing, so under the
   dead=0 gate they are indistinguishable from dead code. **This is not hypothetical:** the sweep
   at `e7c431b2` deleted 983 lines from `Honest.lean`, including the concrete-index exhibits, and
   every gate stayed green. Rooting alone is insufficient — a sweep removing root *and* declaration
   together was still green, which is why existence is pinned separately.
2. **`liveGates` non-vacuity** (`check_linearization.lean:120–126`). A per-gate check whose target
   is `0` agrees vacuously. The driver now fails if a gate declared live has a zero target, and
   annotates zero targets `(0)` so vacuity is visible in the output. This is the guard that would
   have caught V-1 years earlier.
3. **The two coverage fixtures.** `kimchi_proof_vesta_emul.json` (live EndoMul *and* VarBaseMul
   selectors — every other proof fixture has both identically zero) and
   `linearization_vesta_emul.json` (live `endoMul`/`varBaseMul` targets). Without them, a
   reordering of a gate's constraint list is invisible.
4. **The `[absorb_g_inf, absorb_fr, challenge]` sponge shape.** The only shape class that
   distinguishes the one-zero from the two-zero identity absorb: any shape ending at
   `absorb_g_inf`, or squeezing immediately after it, cannot see the difference.
5. **The fixture manifest** (`scripts/fixtures.sha256`, CI-verified). CI never regenerates (no
   submodule), so this is what makes fixture-side accommodation visible in review.
6. **Module-based `native_decide` trust** (`env.getModuleFor?` against upstream `CompElliptic.*` or
   `Pasta.Endo`). A name-prefix test was forgeable, and this tree *does* author declarations inside
   `CompElliptic` namespaces.
7. **`docs/negative-controls.md`.** The convention that a fixture added to close a defect carries a
   recorded mutation and observed failure. A fixture that cannot fail is not a control.

---

## Watch list for the next proof-systems bump

Regeneration is byte-stable for unchanged sources, so a diff after regenerating is itself a drift
check — but these specific items have bitten or nearly bitten, and deserve a direct look:

* **`endosclmul.rs` constraint order and sign.** The defect the engagement found. Re-diff the list
  against `Gate/EndoMul.lean` position-for-position; the α-weighting is positional on both sides,
  so a reordering upstream silently re-targets `ft_eval0`. The pinned revision already carries the
  merged endomul soundness fix, so today the deployed order is unambiguous — that may change.
* **`absorb_g`'s identity encoding** (`sponge.rs:335–339`, two zeros). A change here is invisible to
  every sponge shape except the one in invariant 4.
* **The endo roles.** `endos::<G>().1` (scalar-field, challenge expansion) versus
  `G::other_curve_endo() = endos::<OtherG>().0` (base-field, the `ft_eval0` coefficient). The two
  differ by a squaring in the same field — the historical trap site.
* **`zk_rows`** — `(16·nc + 5)/7` (3/5/19 at nc = 1/2/8), and the three-factor `zkpm` including its
  `ω^(n−1)` term, whose agreement with the full window is a `zkRows = 3` coincidence.
* **arkworks' `sqrt` convention.** The SvdW sign choices are fixture-pinned, not derived; a
  convention change flips the derived `U` base and is caught only by fixtures.
* **Optional-gate and lookup evaluation fields.** Production accepts them on a fragment VK and
  **fr-absorbs** them, so they are transcript-affecting; the Lean wire language cannot represent
  them. If upstream changes what is absorbed when absent, the fragment's proof-shape clause moves.

---

## Settled — do not redo

* **The endpoints' statement shape.** Quantifier order, the uniform product measure, the
  data-valued extractor with semantics in `ExtractsWitness`, the AGM obligations including
  `hrepPrefix`'s emission-time locality — all audited as well-formed. The binding hypothesis is
  *refutable* at the sampled basis (`exists_ne_zero_kernel_scalarBasis`), so no future formulation
  may carry it.
* **δ is a residual, not a reduction** (`derivedUDL_iff_residual_measure`). No reduction can be
  written, because no DL challenge can be planted at a transcript-derived point. Do not attempt
  one; state the slice.
* **The ROM boundary.** `FSFaithful`'s eight read equations are the whole identification, carried by
  no axiom. Do not try to internalize the sponge-is-a-random-oracle step — ironwood deliberately
  keeps it external, and an earlier in-tree attempt produced a *false* axiom.
* **The `sg` slot defence** and its honest scope: the *game's* reads factor through the sg-free
  domain; the adversary's queries do not and are not claimed to — they are priced by `Q`.
* **`reductionEfficient_exists` asserts nothing about efficiency.** It is bookkeeping recording
  which reductions the hardness assumption is indexed against. Retained deliberately, mirroring
  upstream.
* **Constants.** Thirty were independently re-derived (moduli, curve equations, both endo pairs
  with the `endos()` square-selection reproduced by explicit EC arithmetic, the 128-bit squeeze and
  `endoExpand` bit-for-bit, layout 15/7/6/43/45, `zk_rows`, α layout 21/22/23, the `2^255` shift
  conventions). No re-derivation is owed absent a bump.

---

## Provenance

`external-audit-sow.md` (engagement scope, committed verbatim as engaged) →
`external-audit-report.md` (findings, per-claim verdicts, attack log, concrete-security note, and
the two verification addenda covering `5bea7d60` and `c49054e4`) →
`external-audit-response.md` (the project's per-finding disposition) →
`negative-controls.md` (discrimination evidence) → this register.

The SoW's §7 self-declared list is superseded by the report's nine-item augmentation, which the
response adopted into the in-tree documentation rather than by editing the engaged SoW.
