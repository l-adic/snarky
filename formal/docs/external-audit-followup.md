# Follow-up register — the external audit of `formal/`

**Purpose.** This is the forward-looking residue of the external audit engagement
(`external-audit-sow.md` → `external-audit-report.md` → `external-audit-response.md`). Of those
three, **only `external-audit-report.md` is in this repository**; the SoW and the response are not
in `docs/` and are not recoverable here (this tree has a single commit over an empty tree). It
exists so that someone picking this up months from now can act without re-reading three long
documents or re-deriving what was already settled. It records what is **open**, what is **closed
and must not be re-litigated**, what would **silently regress** if the guards were removed, and
what to **re-check on the next proof-systems bump**.

**Status at close (2026-07-28, `c49054e4`).** Every finding the engagement raised is either fixed
and independently verified by the auditors, or deferred with a recorded rationale. Three deferrals
stood at that revision. All gates green: axiom gates at kimchi 52 / bulletproof-pcs 30 / poseidon
19 / pasta 13 / snarky 5; both locked-target gates; sorry census; dead code 0 of 1545; fixture
manifest 32 files at `mina 3969f761846e`; all eleven fixture drivers; full regeneration
byte-identical.

**Since close.** Two pieces have been **closed**. O-2 (the degenerate quotient) went first; the
route and its consequences are recorded under *Closed after the engagement* below, and it moved no
gate counts. Then O-1 was split, and its worst-case half **O-1a** closed — see §O-1 below, which
now carries the split. That one *did* move counts, as expected of new rooted trust-surface
results: kimchi 52 → 53, bulletproof-pcs 30 → 32, dead code 0 of 1545 → 0 of 1555. Clearing O-1a's
residue (the two falsified endpoint docstrings, the four unpinned exhibits, and the gate's own
`1 ≤ R`) moved them again: kimchi 53 → 54, bulletproof-pcs 32 → 33, dead code 0 of 1555 → 0 of
1558 at 169 roots (168 before: two new roots in, `one_le_kimchiExtractRuns` out, now reachable).
The doc-truth pass after it (H-3, the axiom-gate existence-pin correction, M-3, M-4) added no
declaration and changed no root list, so those numbers are **unmoved and re-verified**: axiom
gates at kimchi 54 / bulletproof-pcs 33 / poseidon 19 / pasta 13 / snarky 5, dead code 0 of 1558
at 169 roots, both locked-target gates green without `--regen`. What it did move is the printed
exhibit counts: bulletproof-pcs 23 → 24 (one new pin) and kimchi "seven" → 6 — the kimchi *set*
grew by the same pin, from 5 loop names to 6, while the printed number fell because the count is
now loop-pinned names only, with the four separately-checked guards named beside it.

The **docs-status sweep** after *that* (H-4, the five H-5 instances, M-5, M-6) likewise added no
declaration and changed no root list, and the gate counts are again **unmoved and re-verified**:
axiom gates at kimchi 54 / bulletproof-pcs 33 / poseidon 19 / pasta 13 / snarky 5, dead code 0 of
1558 at 169 roots, both locked-target gates green without `--regen` (printed exhibits 24
bulletproof-pcs / 6 kimchi). Two numbers did move, neither of them a deletion:

- **The style gate's printed file count, 120 → 115.** `scripts/check-style.sh` excluded
  `./.archon-seed/*` but not `./.archon/*`, so it was linting the prover harness's own
  `.archon/logs/*/snapshots/*/baseline.lean` snapshots — one more per snapshotting iteration.
  Nothing was deleted; the gate simply stopped counting files it never owned. The drift is
  directly observable: the planner measured the old `find` at 120 with 5 snapshots, and by the
  time the fix landed the same `find` returned **121** with 6, iter-007 having snapshotted one
  more. A snapshot captured mid-edit could also fail the gate for a reason outside the tree.
- **The `Snarky.*` dead-code deferral is now priced: 43 of 76.** `scripts/deadcode.lean` audits
  everything traversable *except* `Snarky.*` (`isAudited`), so "dead 0 of 1558" said nothing about
  the DSL port's surface, and the size of that exclusion had never been measured. Measured by
  temporarily widening `isAudited` to all of `isOurs` and restoring byte-identically: **76
  authored `Snarky.*` declarations, 43 unreachable from `snarky/roots.txt`'s 8 roots, 33
  credited** — so dead-0 covers 1558 of 1634. The number is now recorded in both headers
  (`scripts/deadcode.lean`, `snarky/roots.txt`). The deferral **stays open by design**: the 43 are
  overwhelmingly plain DSL API (`assertEq`, `mul`, `witness`, `mapVec`, the `CircuitM` instances,
  the `CheckedType`/`CircuitType` classes), so closing it means deciding which combinators are API
  of the port, and rooting them liberally would make the gate vacuous for that package.

The **reference-doc truth sweep** after *that* (H-6, H-7, M-7) added no declaration, changed no
root list and touched no statement, so the gate counts are again **unmoved and re-verified**: axiom
gates at kimchi 54 / bulletproof-pcs 33 / poseidon 19 / pasta 13 / snarky 5, dead code 0 of 1558 at
169 roots (169 resolved, 0 missing), both locked-target gates green without `--regen` (printed
exhibits 24 bulletproof-pcs / 6 kimchi), `check-style.sh` 115 files, `runLinter` clean for `Kimchi`
and `Bulletproof`, sorry census 0, authored `axiom` declarations 0. What moved is **the build log**:

- **The build is now silent.** `lake build Kimchi Snarky Pasta Poseidon FixtureKit Bulletproof
  BulletproofFixture` (8,632 jobs) emitted two `info: Try this: [apply] ring_nf` messages, both from
  `kimchi/Kimchi/Gate/Semantics/EndoMul.lean:508:54` — Mathlib's `ring` falling back to `ring_nf` on
  two of the goals a `<;>` chain lands on, succeeding *noisily*. They were the only non-`#eval`
  diagnostic in the whole build. Replacing that one `ring` with the `ring_nf` the message asked for
  closes the same goals with no output; the remaining five `info:` lines are all `#eval` demos
  (`Gate/Generic.lean:135`, `:136`, `Gate/VarBaseMul.lean:289`,
  `Gate/Semantics/AddComplete.lean:331`, `Gate/Semantics/Poseidon.lean:60`). A warning-free build
  log now exists for this tree, which is what makes any *future* diagnostic visible instead of
  lost in known noise. `:506` in the same proof already used `ring_nf`, so the file is internally
  consistent.

**The EndoScalar range check — the first additive result since O-1a.** Four consecutive iterations
had gone to doc truth; this one put a theorem in. The gap it closes is the one deployed circuit the
formalization said **nothing** about:
`packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/RangeCheck.purs` implements the project's
128-bit range check as `rangeCheck128 endo v = void $ EndoScalar.toField @8 v endo` — an eight-row
`EndoScalar` chain whose effective scalar is discarded, keeping only the constraints — and its whole
soundness argument is that such a chain cannot represent a value ≥ 2¹²⁸. The Lean model of that gate
proved the decomposition (`chain_toField`), its uniqueness (`endoScalar_unique`) and its
completeness (`chain_complete`), but never stated the bound. Four public theorems in
`kimchi/Kimchi/Gate/Semantics/EndoScalar.lean` now do, over five new private helpers
(`chainCrumbs_length`, and the fixed-width base-4 digit expansion `crumbsOf` with `crumbsOf_length`,
`crumbsOf_valid`, `nReconstruct_crumbsOf`):

- `chain_range` — a satisfying `m+1`-row run of uniform crumb width `c`, threaded from the canonical
  `(2, 2, 0)`, pins its register to the image of a natural `< 4 ^ (c(m+1))`. Hypotheses are
  `chain_toField`'s verbatim plus the width, so the chain theorems compose on one run; no
  `[DecidableEq F]` in the statement (the `ℕ` shadow `valNat` gets its instance from `classical`
  inside the proof, and crumb validity comes from `holds_iff` + `crumb_iff`, not from `Gate.sound`,
  which would drag the instance in through its `cFunc`/`dFunc` tables).
- `chain_range_128` — the deployed instance, `c = 8`, `m = 7`: `4 ^ 64 = 2 ^ 128`.
- `chain_range_unique` — the sharp form: under the no-wrap bound `4 ^ width ≤ p` the natural is
  `∃!`, so the register is pinned to a *value*, not a residue class. This is the one an auditor
  should read as "the range check", and the Lean counterpart of the PureScript `Compare nBits n LT`
  side-condition on `toField`.
- `range_complete` — non-vacuity: for `k < 4 ^ N` the honest prover fills a satisfying witness whose
  register is `k`. Without it the bound would be compatible with a circuit that accepts nothing.

Two counts moved, both because declarations and roots were **added**, and both are the invariant's
real content (*dead 0*, *all roots resolved*) rather than the old numbers: the kimchi axiom gate
**54 → 58** (all four theorems pinned in `kimchi/scripts/check_axioms.lean`, which is an existence
pin as well as an axiom pin), and dead code **0 of 1558 at 169 roots → 0 of 1567 at 172 roots**
(`kimchi/roots.txt` gains only the three the minimal-generating-set policy needs — `chain_range` is
live through `chain_range_128` and `chain_range_unique`). `docs/architecture.md`'s live root clause
was updated in the same pass, since writing a fresh stale count in the sweep whose subject is stale
counts is the defect class itself. Everything else is **unmoved and re-verified**: axiom gates
bulletproof-pcs 33 / poseidon 19 / pasta 13 / snarky 5, both locked-target gates green without
`--regen` (printed exhibits 24 bulletproof-pcs / 6 kimchi), `check-style.sh` 115 files, `runLinter`
clean for `Kimchi` and `Bulletproof`, sorry census 0, authored `axiom` declarations 0, and the build
log still exactly the five `#eval` lines. The eleven-driver fixture sweep was deliberately **not**
re-run: the change adds declarations to a gate-semantics file and touches no existing statement, no
fixture, no wire layer and no executable path.

**The scope boundary, which is where the next instance hides** (invariant 9's own lesson, applied to
a development boundary rather than a census one). Four things this result does **not** cover.
(1) Soundness is at the deployed *multi-row* shape but completeness is at a *single* witness
carrying all `N` crumbs; the row split is arithmetically inert (`nReconstruct_append`,
`chain_decompose`), but multi-row completeness needs a crumb-chunking argument that was not done —
it is the next step, not a covered case. (2) `lowest128Bits` itself is not modelled; this is the
primitive it rests on. (3) `lowest128Bits'` witnesses `x = lo + 2¹²⁸ · hi` with both halves
range-checked, and over a ≈2²⁵⁴ field that *pair* is not unique (two splits can be congruent mod
`p`) — no uniqueness claim for the split follows, and none is stated. (4) `chain_range` is
*informative* only when `4 ^ width ≤ p`; in a field smaller than the budget it is true but vacuous,
which is why `chain_range_unique` is the sharp form. All four are stated in the docstrings, not just
here.

**H-8 — three one-clause self-corrections and two MEDIUM items, all inside text iter-008 wrote.**
The pattern of H-6 repeating one layer up: the sweep that fixed a document introduced smaller
defects into its own new text. **H-8a** — `docs/architecture.md`'s *Migration* bullet said "of the
names it samples only `kimchiProof_sound` still exists"; at declaration level *none* of the sampled
names does, and what survive are two relatives under longer names,
`kimchiProof_sound_of_openings_of_vkrep` (`Verifier/Reduction/Soundness.lean:444`) and
`run_sound_algebraic_at_of_vkrep` (`Verifier/Capstone/Reflection.lean:1095`). **H-8b** — this
register's own H-6c clause (above). **H-8c** — `docs/locked-target.md`'s scope section said "neither
name occurs anywhere in the tree", which the *same document* contradicts 40 lines later by
enumerating the five surviving `poseidon_fiat_shamir` mentions; the checkable claim is that neither
survives **as a declaration**. Two MEDIUM: `locked-target.md:53–54`, where an inserted clause broke
a sentence into its own code block (one-word fix, the frozen quote beside it verified read-only and
untouched); and `negative-controls.md`'s *Convention* paragraph, which told the reader to
`git checkout` the mutated file and only disclosed at NC-6 that this tree cannot — hoisted, together
with the fact that the pre-reseed revisions the recipes name (NC-1's `4ff807a6`) are not objects in
this repository (`git cat-file -t` → *not a valid object name*). The mechanical lesson, and the
mirror of iter-007's: **existence of a declaration is a declaration-level grep, not a hit count** —
`grep -rn "$n" | wc -l` counts *longer* names as the sampled one, so `kimchiProof_sound` "exists"
because `kimchiProof_sound_of_openings_of_vkrep` does. iter-007's failure was the opposite
direction (`\b`-anchored, structurally unable to match a *suffixed* name); both belong in the rule.
**The doc-truth class is closed.** Four consecutive censuses (iters 005–008) plus this residue pass,
and the yield is now self-generated at one clause per instance: every H-8 item is a defect in text
written one iteration earlier, none in the original documents. Invariant 9 plus the review's re-run
is the anti-recurrence device, and it worked.

**H-6 / H-7 — the residue, and the class extended to the reference layer.** Two groups:

- **H-6, residue in the documents the previous sweep itself wrote** — 4 items, all in text
  authored one iteration earlier, which is the useful part: a truth pass is not self-verifying.
  `forking-consolidation-plan.md`'s step-8 row asserted "`kimchiForkGood` occurs nowhere" (H-6b)
  when it has **25** hits including `kimchiForkGoodAtU`/`_update`, the very pair that row's own
  step text lists for hoisting — so the row went from "not settled cheaply" to settled, NOT DONE.
  Its step-4 row (H-6c) said "all seven" and listed **six**, and got the set wrong: five of the six
  (`honestProver`, `honestProver_accept`, `lrAt_congr`, `leafAt_congr`, `padChal`) *were* among the
  document's own seven, the omissions were `commitGen_one` and `tail_snoc'`, and the extra was
  `padChal`'s companion `padChal_apply_of_lt` — plus a wrong line range. (This sentence itself said
  "none of them" until iter-009; see H-8b.) `kimchi-reorg.md`'s banner (H-6a) claimed the new-file
  column of **every** table names a file that exists: 16 of 22 do. Two mechanical lessons: an
  absence claim needs an *unanchored,
  untruncated* grep (`kimchiForkGood\b` structurally cannot match `kimchiForkGoodAtU`, and the
  second attempt was `| head`-truncated by an unrelated alternative in the same regex); and a
  filed fix can itself be wrong — the proposed H-6c wording yielded eight names for a seven-set,
  and a filed `docs/chunking-plan.md:49` item ("cites a nonexistent `Constants.md`") did not exist
  at all, the text reading `Constants.mds`, production's Rust MDS constant, with zero tree-wide
  hits for `Constants.md`.
- **H-7, the reference-class census the previous boundary excluded** — 5 documents: **2 stale**
  (`locked-target.md`, ~10 drifted coordinates plus a future-tense closing section — see
  invariant 9, where this instance is written up as the reason the class extends to this layer;
  `minimum-support.md`, where **8 of the support table's 13 line counts** were pre-consolidation —
  3 were still exact and 1 is an estimate that stands — and one row named a since-deleted file),
  **1 verified clean** (`negative-controls.md` — every cited fixture, driver, declaration and
  script string checked against the tree and accurate, including `chainAt_sg` at
  `Deployed.lean:754`, `one_le_of_reductionEfficient` bare at
  `kimchi/…/KnowledgeSoundness.lean:1811` vs dotted at
  `Bulletproof/…/KnowledgeSoundness.lean:746`, and NC-5's assertion strings verbatim in
  `check_kimchi_verifier.lean:180`; **no entry added, since a tactic-token change is not a
  discrimination claim**), **1 one-clause fix** (this register, M-7), and **1 already corrected**
  (`standard-model-line.md`, at iter-007). Two further findings beyond the filed list: the
  `hencodes` hypothesis named in `locked-target.md`'s scope section occurs **nowhere** in the tree,
  and `kimchi-reorg.md`'s own three self-references were stale by the length of the banner that
  shifted them.

Two deferrals still stand (O-1b and O-3).

**H-4 / H-5 — the docs-status instance of the class.** H-1 (endpoint docstrings), H-2 (the same in
a second tree) and H-3 (`CLAUDE.md`/`README.md`'s false-green `lake build` criterion) were all
*one document asserting what its own tree contradicts*. H-4/H-5 is that class in the `docs/`
status layer, and it was swept doc-by-doc with a census rather than instance-by-instance. Of the
19 `.md` files in `docs/`: 2 are read-only audit reports, 5 are reference (`locked-target`,
`minimum-support`, `negative-controls`, this register, and the `standard-model-line` record), and
**12 are plan/scope**. Of those 12, **2 banners were accurate** (`chunking-plan`,
`protocol-wire-split` — left untouched), **3 were false** (`ironwood-refoundation-plan`: "PLAN
ONLY — nothing here is enacted", contradicted by its own `:101` and by the tree;
`kimchi-reorg`: "not yet executed", when its target layout *is* the current tree; `architecture`:
six stale claims, including a dropped ironwood dependency that is git-required today), **1 was
superseded** (`w3-guard-escape-scope`: IMPLEMENTED, crediting a spine, `escape_coord`, that is in
no `.lean` file — proved, then deleted to upstream), **4 were missing entirely** (`agm-reuse-scope`;
`forking-consolidation-plan`, 71 KB of ordered migration steps with nothing at the top saying
whether they happened; `ironwood-generic-application`; `statement-audit-sow`), and **2 were true
of the document but misleading about the work** (`w2-oracle-model-scope`, `w5-forking-scope`:
"SCOPING ONLY — no code changes", when both workstreams have since executed). All 10 were
corrected, plus the `standard-model-line` record, whose stated recovery path ("reconstructed from
git", branch `kimchi-cut-standard-model`) does not exist in this repository — one branch `main`,
one commit with an empty tree. Two findings worth carrying forward, because both were *reviews*
asserting more than the tree supports: `agm-reuse-scope`'s Stage 4 is **half** done (the FS axioms
are gone; `hbind` survives 23 times, retired only from the endpoints) and its Stage 2 is **not**
done at all (`Bulletproof.commitGen`, `loHalf`/`hiHalf`/`append` all still exist).

---

## The two open items

### O-1 (substantive) — a proved extractor-cost bound

**Audit ID:** E-1. **Deferred with sign-off, then split.** The item as filed bundled two questions
with very different difficulty. It is now recorded as two:

* **O-1a — the worst case, proved for our own recursion. CLOSED.**
* **O-1b — the conditional average `(6/δ)^k`. OPEN**, and it is the half that changes what the
  endpoints are worth.

**What was open (both halves).** `ReductionEfficient` gates the discrete-log hypothesis on a call
bound `R`, but no theorem in this tree bounded the extractor's cost, so `R` was supplied only by
`reductionEfficient_exists` — which obtains *some* `R` by a sup without inspecting the counter.
Since ε bounds the DL advantage of one specific algorithm (`fam.relationFinder coins`, which runs
the forking extractor), a generic-group grounding of ε needs a cost bound. ε is still **assumed
for the finder** rather than derived from a time bound: that is O-1b's job, not O-1a's.

#### O-1a — CLOSED: the worst-case bound, at an explicit complete tape

**Route taken.** A *pointwise* bound on the deployed extractor's own counter, proved by structural
recursion on the coin tape, then summed. Pointwise is the whole trick: a bound that holds at each
(table, tape) pair sums over either averaging axis, so the axis mismatch recorded under O-1b
below — which is a genuine obstacle for the conditional average — does not arise here at all.

Three facts make it land on the endpoints:

1. `Bulletproof/Forking/Game.lean:494` `kimchiForkFrom_runs_le` — an `n`-bounded coin tape makes
   at most `(2n+1)^(e+1)` adversary runs. A structural port of ironwood's
   `recursiveAlgebraicForkFrom_runs_le` (`Forking/Adversary/Recursive.lean:578`) to *our*
   recursion, which is indexed by certificate depth with coins one level deeper and whose base
   case runs a Schnorr scan rather than costing a bare `1`. That leaf scan is why the exponent is
   `e + 1`; the sharper `(2n+1)^e` is false at `e = 0`.
2. `Bulletproof/Forking/Deployed.lean:914` `exists_complete_bounded_coins` — the identity tape is
   `Complete` **and** `Bounded (2^128)` simultaneously. The two conditions are independent
   (a complete tape with redundant orders is unbounded), and every endpoint hypothesizes the
   first while the cost bound consumes the second, so the joint witness is the load-bearing step.
3. The two families' `exists_complete_reductionEfficient`
   (`Bulletproof/Forking/KnowledgeSoundness.lean:733`,
   `Kimchi/Verifier/KnowledgeSoundness.lean:1797`) — the endpoints' two coin-side hypotheses are
   jointly dischargeable at an explicit `R = (2·2¹²⁸ + 1)^(k+1)`.

**What it does and does not buy.** `R` is now *computed from the counter* rather than obtained
from a sup that never inspects it, which is upstream's own state of the art for its recursion.
It is bracketed below as well as above: `one_le_kimchiExtractRuns` (`Game.lean:694`) pins the
counter at `≥ 1`, so the upper bound cannot be read as satisfied by a reduction that does nothing.
But the number is **exponential in `k` and in the challenge domain**, so this is bookkeeping, not
concrete security: it records which reductions the hardness assumption is taken against. Quote the
caveat wherever the number is quoted. Nothing about ε's grounding changes.

Both endpoint docstrings that *denied* a cost bound have been corrected — the kimchi endpoints'
shared "what the bound rests on" paragraph and `ipaVesta_knowledge_sound`'s "Four limits" item 3,
each of which asserted the opposite of a theorem in its own file. The correction is bookkeeping in
the same sense the bound is: discharging `hEff` fixes which reductions the hardness assumption is
quantified over and nothing more, because at `R = (2·2¹²⁸ + 1)^(k+1)` a reduction permitted that
many oracle calls solves Pasta discrete log outright, leaving `hHard` satisfiable only at `ε ≈ 1`.
Any future corollary that instantiates an endpoint at the witnessed tape must repeat that sentence.

`reductionEfficient_exists` stays, rooted, unchanged: its job is to say what `ReductionEfficient`
does *not* do, and the new theorem stands beside it rather than superseding it.

One finding from clearing this residue is not a soundness item at all: **H-3**, the build
instruction in `CLAUDE.md`, `README.md` and two workspace gate headers that named bare
`lake build` from `formal/` — a no-op there, so acting on it yields a *false green* rather than a
false theorem. It is filed here only because it was found in this pass; the fix is the explicit
target list, now stated in all four places.

#### O-1b — OPEN: the conditional average

**What closing it buys.** It converts the endpoints from "knowledge soundness with an extractor of
unproved *expected* cost" into a proof of knowledge with a stated extraction cost, and makes ε
derivable from `t²/2²⁵⁴` instead of posited. That is the difference between a concrete-security
claim and a structural one. O-1a does not do this.

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
| Our predicate (kimchi) | `Kimchi/Verifier/KnowledgeSoundness.lean:1757` `ReductionEfficient`, counting `attemptRuns` (`:1743`) |
| Our predicate (IPA) | `Bulletproof/Forking/KnowledgeSoundness.lean:637`, counting `DeployedFamily.attemptRuns` (`:626`) |
| The run counter itself | `Bulletproof/Forking/Game.lean:651` `kimchiExtractRuns` — a *projection* of the extractor's own recursion, deliberately never a separate definition |
| Our worst-case bound (O-1a) | `Game.lean:677` `kimchiExtractRuns_le` → `Deployed.lean:863` `deployedExtractRuns_le` → the two families' `reductionEfficient_of_bounded` / `exists_complete_reductionEfficient` |
| Its anti-vacuity companion | `Game.lean:694` `one_le_kimchiExtractRuns` — the counter is `≥ 1` on every table and every tape |
| The same floor at the level the endpoints read | the two families' `one_le_of_reductionEfficient` (`Bulletproof/Forking/KnowledgeSoundness.lean:746`, `Kimchi/Verifier/KnowledgeSoundness.lean:1811`) — no `R` below `1` satisfies `ReductionEfficient`, so `hEff` cannot be met by a number advertising a zero-call reduction. Via `Deployed.lean:877` `one_le_deployedExtractRuns` on the IPA side |
| Upstream's worst-case bound | ironwood `Recursive.lean`, "Worst-case run bound": `≤ (2·|F| + 1)^k`, plus `reductionEfficient_exponential` (`Algebraic.lean:1440`) — about *upstream's* recursion, which is why O-1a had to be proved rather than cited |

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

## Closed after the engagement

### O-2 — the degenerate quotient (`t := 0`), and `htpos` retired

**Audit ID:** B-1 strong form. **CLOSED.** Deferred at close with sign-off; the cost note in that
deferral turned out to be right, and the item was executed as one atomic change. It is recorded
here rather than in *Settled* because the route matters to anyone reading the endpoints.

**What was open.** `KimchiFamily.htpos` required `0 < tComm.size` of every run of every adversary
in the family, and the wire parse carried a matching declared strengthening
(`guard (0 < p.tComm.size)`), so a proof production accepts — production bounds `t_comm.len()`
from above only, `verifier.rs:260` — had no Lean counterpart. Attack shape #7 of the audit's C2
log was a scope boundary rather than a priced one.

**The route actually taken.** The degree lemma was NOT weakened. `ftChunkAssembly_natDegree_lt`
keeps its `0 < nt`, which is essential to its own statement (at `nt = 0` its conclusion reads
`0 < 0`); a companion absorbs the split instead:

* `ftChunkAssembly_natDegree_lt_of_le` (`Capstone/Algebraic.lean:369`) — for any positive `m`
  dominating the chunk budget, `natDegree (ftChunkAssembly k nt aT) < m`, with no positivity
  hypothesis on `nt`. It calls the original on the positive branch (which also keeps that lemma
  reachable under the dead=0 gate); at `nt = 0` the assembly is the empty sum `0` and the bound
  is `hm`.
* `hnt0` dropped from `ft_identity_of_chunks_of_eq` (`Algebraic.lean:498`) and
  `ft_identity_of_chunks` (`:573`); the rest of those proofs are arity-generic and went through
  unchanged.
* `htpos` dropped from `run_sound_algebraic_at_of_vkrep` (`Capstone/Reflection.lean:1095`) and
  `runBounds_zeta_at_assembly` (`:1258`), where `0 < 7·n` now comes from the `[NeZero n]` instance
  already in scope.
* The `KimchiFamily` field deleted (`KnowledgeSoundness.lean:831`) with its two uses, and the
  fragment preamble's empty-quotient exclusion clause with it. Nothing reintroduced nonemptiness:
  every other `tComm.size` occurrence is a summation index (empty-sum-inert at 0), and the AGM
  fields quantify over `Fin size`, vacuous at 0.
* The honest exhibit still emits `nc` zero chunks — now a stated convenience (`tComm_le` is the
  unconditional `nc ≤ 7·nc`, and the polyscale combination of an all-zero list is `0` either way),
  not a requirement.
* The wire guard deleted (`Wire.lean:161`), which is the payoff: the Lean accepted language now
  matches production on this axis.

**Why widening is safe, so nobody re-derives it.** At `tComm.size = 0` the assembled quotient is
the empty sum `0`, so the ft identity reads `pScalar·σ₆(ζ) = v0` — the aggregate constraint
polynomial is forced to vanish outright rather than to be a multiple of `Z_H`. That is *more*
restrictive on the adversary, so extraction still goes through. The change is a strict widening
of the adversary class; no conclusion weakened.

**The driver's negative control was inverted, not deleted.** The empty `t_comm` case moved from
`check_kimchi_verifier.lean`'s `parses` array (parse must return `none`) to its `corrupts` array
(`verify` must return `false`) — a stronger control, and one matching production semantics. Its
non-vacuity needed its own assertion; see standing invariant 8 and `negative-controls.md` NC-5.

**Gates after the change:** kimchi axiom gate 52 (unmoved), locked target intact without `--regen`
(no pinned text contains the `KimchiFamily` body), dead code 0 of 1545, style clean, all fixture
drivers green.

---

## Standing invariants — what would silently regress

Each of these was created in response to a finding and protects a property that has **already
failed once** or was demonstrably unprotected. Removing any of them re-opens the corresponding
hole, and in most cases the tree would stay green while doing so.

1. **Exhibit-existence pins** (`*/scripts/check_locked_target.sh`, 24 exhibits in bulletproof-pcs,
   6 in kimchi). Both counts are **loop-pinned names only** — the convention is now stated in a
   comment in each script, and the guards checked by the separate `if`s are named beside the
   count rather than folded into it (bulletproof-pcs: 2 anti-vacuity companions; kimchi:
   `FSFaithful`, `wins_iff_kimchiVerify`, and the two honest-family guards). Anti-vacuity exhibits
   are by construction consumed by nothing, so under the
   dead=0 gate they are indistinguishable from dead code. **This is not hypothetical:** the sweep
   at `e7c431b2` deleted 983 lines from `Honest.lean`, including the concrete-index exhibits, and
   every gate stayed green. Rooting alone is insufficient — a sweep removing root *and* declaration
   together was still green, which is why existence is pinned separately. Of O-1a's four new
   certificates, `exists_complete_bounded_coins` was the one held by `roots.txt` alone until the
   residue pass added it here; `one_le_kimchiExtractRuns` and both families'
   `exists_complete_reductionEfficient` were already existence-pinned by their package's axiom
   gate as well. See *The protection map* below for which mechanism catches which deletion.
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
8. **The emptied-quotient parse assertion** (`check_kimchi_verifier.lean`, the
   `emptied t comm reaches the verifier` line). O-2's corruption entry runs through
   check-then-verify, so a reinstated `0 < t_comm.size` wire guard would leave it reading
   `✓ REJECT` while silently restoring the strengthening O-2 removed. The positive
   parse assertion beside it is what fails instead (negative control NC-5). Removing it makes the
   corruption vacuous, not absent.
9. **The tree-truth convention for `docs/`, over BOTH document classes.** Every plan/scope
   document in `docs/` carries a status banner at the top, and the banner is *checked against the
   tree* when it is written or touched. **The same obligation binds the reference class** — the
   documents that describe the tree as it is rather than as it is planned (`locked-target`,
   `minimum-support`, `negative-controls`, `standard-model-line`, this register): their
   coordinates, counts and tenses are claims about the tree and are checked the same way. This
   exists because H-1 → H-2 → H-3 → H-4/H-5 → H-7 are one defect class — **a document asserting
   something its own tree contradicts** — and the status layer is where it recurs. It is
   the most misleading shape the class takes: a status line is exactly what a reader trusts
   without checking, and three of the instances told a reader that work was unbuilt when the tree
   had it, or built when the tree had deleted it. A banner that cannot be established cheaply must
   say **that** ("steps 6–8 not re-verified") rather than guess — an honest gap outranks a
   confident wrong word.

   **The reference class is the higher-stakes half, and was the last to be swept.** A stale plan
   banner misleads about **work**: the reader mis-estimates what is left to do, and the tree itself
   corrects them the moment they look. A stale reference document misleads about **the artifact**:
   it is the reader's model of what was built, consulted precisely *instead of* reading the tree,
   so nothing corrects it. `locked-target.md` — the document that declares what is locked, the
   first thing an auditor opens — went five iterations with ~10 drifted coordinates and a closing
   section in the future tense about a retirement that had already happened, naming two axioms and
   a file that exist nowhere. It survived because the iter-007 census drew its boundary at the
   plan/scope class and classified the reference documents as presumed-fresh without checking
   them. **A census's own scope boundary is where the next instance hides**; state the boundary
   explicitly and treat what it excluded as unchecked, not as clean.

   Note also that a *line number into a living document* is this class in miniature — including a
   document's references into itself. `kimchi-reorg.md`'s three self-references were computed
   before its own status banner was prepended, so adding the banner invalidated all three. Prefer
   a section or declaration name over a line number for any reference into a file that is still
   being edited.

   **There is deliberately no mechanical gate for this, and there should not be one.** A script
   can check that a banner *exists*; it cannot check that the banner is *true* — truth here is a
   claim about a whole tree, in prose, and establishing it is the judgement the convention asks
   for. A presence-check would convert an unchecked property into an apparently-checked one,
   which is this tree's standing lesson (invariant 1, `e7c431b2`: 983 lines deleted, every gate
   green). A green gate that cannot discriminate is worse than no gate. The enforcement is
   therefore procedural: the census in the iteration's task result is the record, and the review
   re-runs it.

### The protection map — which mechanism catches which deletion

Two consecutive review passes mis-attributed this, so it is written down once here. For a
declaration that disappears from the tree:

| Mechanism | Fails when |
|---|---|
| the compiler | a *consumed* declaration is deleted (its consumer stops elaborating) |
| `roots.txt` + `scripts/deadcode.sh` | a declaration becomes unreachable — but NOT when root line and declaration are deleted together |
| `*/scripts/check_axioms.lean` | a listed root is absent from the environment (`env.contains` throw) **or** its closure gains a stray axiom |
| `*/scripts/check_locked_target.sh` | a pinned statement text changes, or a pinned exhibit name leaves its file |
| the `-- script-surface:` blocks + the `scripts/*.lean` drivers | a driver-consumed declaration is deleted (the driver stops elaborating) |

**The correction.** All five axiom gates are existence pins, not only axiom pins: each `run_cmd`
throws `axiom-check root not in environment: <name>` before collecting the closure, which
`kimchi/roots.txt` has said in as many words since it was written. So "protected only by
`roots.txt`" is a claim to check by grepping the five gates, not to assume. Concretely: both
`one_le_of_reductionEfficient` were **already** existence-pinned by their package's axiom gate
when the iter-005 review recorded them as protected by `roots.txt` alone. Adding them to the
locked-target exhibit sets is a *second, independent* gate — this tree's redundancy discipline —
not the closure of an open hole. Invariant 1's `e7c431b2` precedent is untouched by this: those
exhibits were in *neither* other gate.

**And what needs no pin at all.** `Bulletproof.Ipa.Forking.one_le_deployedExtractRuns`
(`Forking/Deployed.lean:877`) is consumed at `Forking/KnowledgeSoundness.lean:755`, so the
compiler is its existence pin. It is deliberately not in the exhibit sets: those are documented
as certificates consumed by nothing, and listing a reachable lemma there would misdescribe it.

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
  upstream — and now retained *for the contrast*, since O-1a's `exists_complete_reductionEfficient`
  supplies an `R` that is computed from the counter. Do not delete one in favour of the other.
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

**Which of the chain are at hand.** `docs/` holds 19 `.md` files; `external-audit-report.md`,
`negative-controls.md` and this register are among them. **`external-audit-sow.md` and
`external-audit-response.md` are not in this repository**, and cannot be recovered from it (single
commit, empty tree). The chain above is the real provenance and is worth recording as such — but
read the two absent links as history, not as documents you can open. Anything this register needed
from them is restated here.

The SoW's §7 self-declared list is superseded by the report's nine-item augmentation, which the
response adopted into the in-tree documentation rather than by editing the engaged SoW.
