# Follow-up register — the external audit of `formal/`

> **STATUS (superseded): the probabilistic soundness line this document is largely about was
> RETIRED.** The forking / knowledge-soundness tree in `kimchi` and `bulletproof-pcs`, and the
> `Zcash/ironwood` dependency under it, were deleted; see `soundness-line-retirement.md` for
> what went, why, and where to recover it. This file is kept as the record of an outside
> engagement — read it as history. Its open items (O-1a / O-1b), its locked-target and
> exhibit-set invariants, and its gate counts no longer describe this repository.

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
it is the next step, not a covered case *(closed at iter-011 by `chain_range_complete`; see the
paragraph below)*. (2) `lowest128Bits` itself is not modelled; this is the
primitive it rests on. *(Iter-016 modelled it — both `constrainLowBits` settings, completeness,
and the compiled non-uniqueness of the split — but the split modelling was REMOVED at PR review,
2026-08-01, by the user's decision: the load-bearing deployed use of the gate-as-range-check is
the bound alone, and the split's affine relation belongs to whatever consumer one day interprets
the surrounding circuit. What remains is the packaged check `Chain128` with its two directions
and the deployed per-field entry points `fp_/fq_rangeCheck128_{sound,complete}` — every field
hypothesis discharged at `Fp` and `Fq`. This item is again OPEN as stated, now deliberately so.)*
(3) `lowest128Bits'` witnesses `x = lo + 2¹²⁸ · hi`, range-checking `hi`
unconditionally and `lo` only under its `constrainLowBits : Boolean` flag (`lowest128Bits =
lowest128Bits' true` checks both; the `false` path is OCaml's `squeeze_scalar`, only `hi` checked).
Over a ≈2²⁵⁴ field that *pair* is not unique even with both halves checked (two splits can be
congruent mod `p`) — no uniqueness claim for the split follows, and none is stated *(iter-016 had
compiled this sentence into a theorem; removed with the rest of the split modelling, see (2) — the
sentence is again the record)*; the unchecked-`lo` path is more non-unique still. (4) `chain_range` is
*informative* only when `4 ^ width ≤ p`; in a field smaller than the budget it is true but vacuous,
which is why `chain_range_unique` is the sharp form. All four are stated in the docstrings, not just
here.

**Iter-011 — multi-row range completeness, and the provenance residue one tree over.** The
crumb-chunking argument that scope-boundary item (1) above named as "the next step" is proved:
`chain_range_complete` (for `k < 4 ^ (c(m+1))`, an entire satisfying `m + 1`-row run of uniform
width `c`, threaded from the canonical `(2, 2, 0)`, whose output register is `k`) and its deployed
instance `chain_range_complete_128` (eight rows of eight crumbs, `k < 2¹²⁸`, proved by applying the
general theorem). Its conclusion is `chain_range`'s hypothesis list **verbatim**, so the two compose
on one run: at a fixed row shape the accepted register set is exactly `[0, 4 ^ (c(m+1)))`, and at
the deployed shape `chain_range_128` / `chain_range_complete_128` is an **iff** — a register has a
satisfying eight-row `EndoScalar` witness iff it is the cast of a natural below `2¹²⁸`. The two
halves of that *iff* do **not** carry the same hypotheses: the soundness half (`chain_range_128`)
needs `h2 : (2 : F) ≠ 0` and `h3 : (3 : F) ≠ 0`, which is what lets a crumb's base-4 digit be read
back; neither completeness theorem needs `h2`/`h3` or `[DecidableEq F]` — completeness asks nothing
of the field. Four private helpers
carry it — `nReconstruct_append_pos` (the *positional* append; the existing `nReconstruct_append`
resumes the fold and so leaves the tail in fold form, which no chunking argument can consume), its
`ℕ` shadow `valNat_append` (hoisted out of `valNat_cons`'s own proof, whose statement and both
consumers are unchanged), `chainCrumbs_chainBuild`, and `nReconstruct_rowsOf` (the Horner peel at a
row rather than a crumb).

Three counts moved, all by **addition**, and all consistent with the invariant's real content
(*dead 0*, *all roots resolved*) rather than with the old numbers: the kimchi axiom gate **58 → 60**
(both new theorems pinned in `kimchi/scripts/check_axioms.lean`, existence as well as axioms), dead
code **0 of 1567 at 172 roots → 0 of 1573 at 173 roots** (`roots.txt` gains only
`chain_range_complete_128`, the minimal-generating-set policy's choice — the general theorem is live
through it), and `docs/architecture.md`'s live root clause updated in the same pass. Unmoved and
re-verified: axiom gates bulletproof-pcs 33 / poseidon 19 / pasta 13 / snarky 5, both locked-target
gates green **without** `--regen` (24 bulletproof-pcs / 6 kimchi exhibits), `check-style.sh` 115
files, `runLinter` clean for `Kimchi` and `Bulletproof`, `shake` clean, sorry census 0, authored
`axiom` declarations 0, `native_decide` still only the two anchors in `Pasta/Endo.lean`, and the
build log still exactly the five `#eval` lines at 8632 jobs. The eleven-driver fixture sweep was
again deliberately **not** re-run: the change adds declarations to a gate-semantics file and touches
no existing statement, no fixture, no wire layer and no executable path.

**The scope boundary of *this* result.** The bound and its converse both fix **one** row width `c`
for every row; a *ragged* run is mentioned by neither, so the "exactly `[0, 4 ^ (c(m+1)))`" reading
is at a fixed row shape. The deployed circuit never emits a ragged run — `EndoScalar.purs:74`'s
nibbles are `Vector rows (Vector 8 (FVar f))`, uniform by construction — so this is a gap in
generality, not in coverage of the deployed shape. `lowest128Bits` itself remains unmodelled, and
the non-uniqueness of its split over a ≈2²⁵⁴ field is genuine — not a modelling shortfall to close.
*(Both clauses were overtaken at iter-016: the split is modelled, and its non-uniqueness is the
theorem `lowest128Bits_split_not_unique`. The reason given here for the delay — that the split
"needs a Generic-gate model in `Witness F` form" because `Gate/Generic.lean` is "the runnable
`Array Int` checker" — was **false about this tree** and held the phase up for six iterations; see
the iter-016 paragraph.)*

**The lesson, and why this is a paragraph rather than a footnote.** Two clauses that iter-009 wrote
into the Lean docstrings and into item (3) above were **false about the PureScript source they
cited**: `lowest128Bits'` was said to range-check "both halves" (its first argument is
`constrainLowBits : Boolean` — `hi` is checked unconditionally, `lo` only when the flag is set, and
"both" is the `lowest128Bits' true` specialisation), and to be `rangeCheck128`'s *caller* (it never
calls it; it inlines `EndoScalar.toField @8` twice, making it a sibling consumer of the same
primitive). Both clauses' **conclusions** were correct and stand — only the provenance was invented.
Iters 005–008 checked doc coordinates against the **Lean** tree; the first iteration to quote the
**PureScript** tree produced its residue exactly there. A census's own scope boundary is where the
next instance hides, one layer further out this time. Standing invariant 9 is extended accordingly:
a provenance quote is a claim about the tree it names, and is checked against that tree.

**Iter-012 — the first Lean step of O-1b, and the iter-011 *iff* imprecision.** Milestone **M1** of
the O-1b route landed: eight public declarations in `Bulletproof/Forking/Game.lean` — the two named
scan attempts (`kimchiScanCandidate`, `kimchiLeafCandidate`), the two good sets
(`kimchiGoodChallenges`, `kimchiLeafGoodChallenges`), the spread hypothesis `KimchiForkSpread`, the
two pointwise run bounds (`kimchiForkFrom_node_runs_le`, `kimchiForkFrom_leaf_runs_le`) and the
depth-0 tape-sum lemma `kimchiForkFrom_sum_runs_le_leaf`. All eight reduce to
`[propext, Classical.choice, Quot.sound]`. **This is one milestone of four**: M2 (the `e + 1`
induction and its public corollary), M3 (the table-axis swap) and M4 (narrowing the spread
predicate) are still open, and nothing existing was restated to make M1 fit. The route, the two
findings it established, the arithmetic of the depth-0 case and the moved counts are all in §O-1b
below rather than repeated here; the counts that moved are the bulletproof-pcs axiom gate
**33 → 41** and dead code **0 of 1573 at 173 roots → 0 of 1581 at 175 roots**, both by addition.

The same iteration cleared the iter-011 review's MEDIUM, a prose imprecision three sites deep: the
`chain_range_128` / `chain_range_complete_128` *iff* was stated without saying the two halves carry
different hypotheses. The soundness half needs `h2 : (2 : F) ≠ 0` and `h3 : (3 : F) ≠ 0` — what lets
a crumb's base-4 digit be read back — and completeness needs neither. Fixed in
`Kimchi/Gate/Semantics/EndoScalar.lean`'s `§ The 128-bit range check` preamble, in
`chain_range_complete_128`'s own docstring, and in the iter-011 paragraph above. Both directions
were and are true; only the sentence was imprecise, so no statement, signature or proof moved.

**Iter-013 — the spread predicate narrowed, and the depth induction landed (M4′ + M2).** Two
milestones of the O-1b route, fused because the narrowing is nearly free before the induction and
costly after it. **M4′**: `KimchiForkSpread`'s two clauses now read their good sets on the diagonal
`p = A.run O` instead of at arbitrary pairs `(O, p)`, and `kimchiForkFrom_sum_runs_le_leaf` is
restated there. That is not a weakening — it makes our predicate *exactly* upstream's `ForkSpread`,
and the un-narrowed form was plausibly degenerate (see fact (2) in §O-1b, rewritten). **M2**: the
depth induction `kimchiForkFrom_sum_runs_le_of_forkSpread` (upstream `:590–897`, upstream's `d`
becoming our `e + 1`, with two summands rather than three and without upstream's `2 ≤ σ₀`), the
normal form `kimchiScanCandidate_runs_cases` it consumes, and its public root corollary
`kimchiExtractRuns_sum_le_of_forkSpread`. Two further declarations pin the degeneracy the narrowing
avoids rather than arguing it in prose: `kimchiLeafGoodChallenges_eq_empty_of_unstable` and
`kimchiForkSpread_eq_zero_of_leaf_unstable`. Five new public declarations in all, every one
reducing to `[propext, Classical.choice, Quot.sound]`. **M3, the table-axis swap, is what remains
of O-1b**, and it was deliberately not attempted; nothing existing was restated to make M2 fit —
`ReductionEfficient` and both families' endpoints included (audit item A-4). The counts that moved,
both by addition: the bulletproof-pcs axiom gate **41 → 46** and dead code **0 of 1581 at 175 roots
→ 0 of 1586 at 175 roots** — the root *total* is unchanged because the M1 TEMPORARY group was
deleted exactly as its own comment instructed (the corollary consumes both of its entries through
the induction) and the two terminals that replace it are the corollary and the anti-vacuity lemma.
The single corrective sentence permitted in `kimchiExtractRuns_le`'s docstring was taken: its claim
that the conditional average "is not proved anywhere in this tree" was made false by this iteration
and now names the new theorem, with the three ways it does *not* supersede the unconditional bound
spelled out.

**Iter-014 — the M2 bound was vacuous at every deployed depth, and M4″ is what makes it
contentful.** `KimchiForkSpread`'s node clause quantified over *arbitrary* coin trees, and
`Zcash.Snark.RecursiveForkCoins` carries an arbitrary sampling order — `[]` included. Every scan an
empty order drives is `nextForkChallenge attempt _ []`, whose `[]` case is
`{ output := none, runs := 0 }`, so both arms of `kimchiForkFrom` fail outright on such a child,
the good set is empty, and the clause reads `σ₀ ≤ 0`. Instantiated at certificate depth `0` and
round `σ.k − 1` — legal exactly when `1 ≤ σ.k` — it forces `σ₀ = 0`, so
`kimchiExtractRuns_sum_le_of_forkSpread` as shipped at iter-013 read `0 ≤ …` at **every** `σ.k ≥ 1`,
and the deployed `k` is nowhere near `0`. The degeneracy is now compiled rather than argued:
`kimchiGoodChallenges_eq_empty_of_order_nil` and `kimchiNodeFloor_eq_zero_of_forall_coins`, the
latter stated at the *un-narrowed* clause so that it survives the fix and stays the record of why
the quantifier moved. **M4″** is that fix, and it is the M4′ doctrine applied at the other axis —
quantify only over what the recursion visits: the node clause now reads
`child : Pre → RecursiveForkTape Pre (e + 1)`, whose order list is a full enumeration of `Pre`, and
the depth induction's only two uses of the clause already instantiated it at tape-derived coins, so
the repair was two call sites and nothing else in that ~400-line proof moved. **The non-vacuity
companion** answers the question the narrowing opens in the other direction:
`exists_kimchiForkSpread_two_le` exhibits a parameter telescope carrying `KimchiForkSpread … 4`, at
`σ.k = 0` over `T = Pf = Unit`, `Pre = Fin 5`, `F = G = ℚ` and an all-zero SRS, and
`spreadExhibit_extractRuns_sum_le` reads the conditional bound at those parameters as
`3 · ∑ ≤ 30 · |tapes|`. It exercises the **leaf** clause only — at `σ.k = 0` the node clause is
vacuous — so whether the narrowed node clause is satisfiable at `σ₀ ≥ 2` for `σ.k ≥ 1` is open, and
is the next milestone rather than a defect of this one. Nothing existing was restated to make any
of it fit: `ReductionEfficient`, both families' endpoints and all of O-1a's declarations are
untouched (audit item A-4), and the one permitted clause in `kimchiExtractRuns_le`'s docstring notes
only that the hypothesis is now discharged at `σ.k = 0`. Counts moved by **addition**: the
bulletproof-pcs axiom gate **46 → 51** and dead code **0 of 1586 at 175 roots → 0 of 1601 at 178
roots**, with `docs/architecture.md`'s live root clause updated in the same pass. Unmoved and
re-verified: axiom gates kimchi 60 / poseidon 19 / pasta 13 / snarky 5, both locked-target gates
green **without** `--regen`, `check_extractor_computes.sh`, `check-style.sh` 115 files, `runLinter`
clean for `Kimchi` and `Bulletproof` with `nolints.json` ungrown, `shake` clean, sorry census 0,
authored `axiom` declarations 0, and the build log still exactly the five `#eval` lines at 8633
jobs. The eleven-driver fixture sweep was again deliberately **not** re-run: nothing in this diff
reaches a fixture, the wire layer or an executable verifier path.

**Iter-015 — the spread hypothesis has a model at *every* round count (M5), and "the third scan is
the hard part" was false.** O-1b's last milestone. The iter-014 telescope was **generalized in
place** by a round count rather than duplicated: `spreadExhibitSRS` and its four data definitions
now take `(k : ℕ)`, so every iter-014 statement survives as its own instance at `0` and there is no
second parameter family to keep in sync. On it, `spreadExhibit_forkFrom_isSome` proves by induction
on certificate depth that `kimchiForkFrom` returns a certificate from every position it can be
entered at, on every `Complete` coin tree. `spreadExhibit_forkSpread k` then discharges **both**
clauses of `KimchiForkSpread` at `σ₀ = 4` — the node one included, which is vacuous only at
`σ.k = 0` — and `exists_kimchiForkSpread_two_le_of_rounds` is the type-clean headline, whose
`σ.k = K` conjunct is what makes it say more than the `k = 0` witness already did. The applied
bound generalizes with it (`spreadExhibit_extractRuns_sum_le`, now `3^(k+1)·∑ ≤ 30^(k+1)·|tapes|`),
and `spreadExhibit_card_le_extractRuns_sum` compiles the anti-vacuity direction — `|tapes| ≤ ∑`
from `one_le_kimchiExtractRuns` via `Finset.card_nsmul_le_sum` — so "the left-hand side is nonzero"
is a theorem at every depth rather than a sentence. **The framing this tree carried was wrong, and
is corrected rather than softened.** `Game.lean`, this file and `roots.txt` all said node-clause
satisfiability needed a genuinely harder argument whose hard part was the *third* scan finding an
eligible challenge in the residual list `rest`. Against an adversary whose every reprogrammed run
succeeds it is not: `nextForkChallenge_other_good_mem_rest` puts every *other* good challenge in
`rest` and `nextForkChallenge_output_fresh` identifies the seen set, so the whole obligation is
"`Fin 5` has an element outside `{0, q₁, q₂}`". What the exhibit does **not** touch is a spread at
*deployed* parameters: its adversary wins identically, which no real one does, and deriving `σ₀`
from a success probability `ε` remains user-excluded open research. Counts moved by **addition**:
the bulletproof-pcs axiom gate **51 → 53** and dead code **0 of 1601 at 178 roots → 0 of 1606 at
180 roots**, with `docs/architecture.md`'s live root clause updated in the same pass. Unmoved and
re-verified: axiom gates kimchi 60 / poseidon 19 / pasta 13 / snarky 5, both locked-target gates
green **without** `--regen` (24 bulletproof-pcs / 6 kimchi exhibits),
`check_extractor_computes.sh`, `check_ironwood_generic.sh`, `runLinter` clean for `Kimchi` and
`Bulletproof` with `nolints.json` ungrown, `shake` clean, sorry census 0, authored `axiom`
declarations 0, and the build log still exactly the five `#eval` lines. Two published numbers moved
for reasons **outside** this lane and are recorded so the next reader does not chase them:
`check-style.sh` reads **116** `.lean` files and the build reports **8634** jobs, both because the
user's concurrent PureScript-alignment work under `snarky/` added modules; this lane adds no file.
The eleven-driver fixture sweep was again deliberately **not** re-run: the change adds declarations
to the forking game's counting layer and reaches no fixture, wire layer or executable path.

**Iter-016 — the lowest-128-bits split is modelled, its non-uniqueness is a theorem, and the blocker
that held it up for six iterations did not exist.** Route 1's second phase. `RangeCheck.purs`'s
`lowest128Bits'` — the split every Fiat–Shamir challenge in the deployed circuit goes through — now
has a model in `Kimchi/Gate/Semantics/EndoScalar.lean`, composed out of the range-check primitive
that was already there. `Chain128` packages `chain_range_128`'s hypothesis list once, so its two
directions (`Chain128.range`, `Chain128.exists_of_lt`) are the two range theorems read through one
predicate. On them: `lowest128Bits_sound` is the `constrainLowBits = true` path (OCaml's
`squeeze_challenge`) — both halves are casts of naturals below `2¹²⁸` and `x` is the cast of the
natural those two are the base-`2¹²⁸` digits of; `lowest128Bits_sound_lowUnchecked` is the `false`
path (`squeeze_scalar`), where only `hi` is pinned and `lo` carries **no** bound at all;
`lowest128Bits_complete` is the honest prover's split of any `n < 2²⁵⁶`.
`splitRow`/`splitRow_holds_iff` is the single bridge saying the affine relation `x = lo + 2¹²⁸ · hi`
is one generic row — every other statement takes that relation as a hypothesis, so the Generic gate
enters in exactly one place.

**The result an auditor should read is the negative one.** `lowest128Bits_split_not_unique` compiles
what iters 009 and 011 could only assert in prose: over an odd characteristic with
`2¹²⁸ ≤ p < 2²⁵⁶` — both Pasta primes — the value `x = 0` has two accepted splits whose low halves
differ, `(0, 0)` and `(p % 2¹²⁸, p / 2¹²⁸)`. Both halves range-checked, both rows satisfied. For a
verifier that means the circuit does **not** determine `lo` as a function of `x`: the honest
prover's split is one of several the constraints accept, so a caller may rely on the bound each
half carries and never on which pair was chosen. No uniqueness corollary follows from
`chain_range_unique`, and the earlier prose caveat is repointed at the theorem rather than
restated.

**The six-iteration blocker was a stale docstring.** `STRATEGY.md`, `CLAUDE.md` and the iter-011
paragraph below all said this phase first needed an algebraic `Witness F` model of the Generic gate,
because `Gate/Generic.lean` was "the runnable `Array Int` checker" that "does not compose with the
algebraic witnesses". It is not: that file is `structure Generic (F : Type*)` carrying
`q w : Fin 15 → F`, one `constraints : List R` over `[CommRing R]`, `Holds`/`holds_iff`,
`ok`/`ok_iff`, `map` and `withPublic`. Neither `Array Int` nor a bare `Assignment` occurs anywhere
in the tree (`grep -rnw`, `.lake` excluded → 0 for both). Nothing needed designing; the split
composed out of declarations that had been sitting beside each other since iter-011.
`CLAUDE.md`'s description was corrected in the same pass, including its framing that the two gate
idioms differ by concrete-vs-algebraic — the real difference is runnable-demo vs proof-oriented.

Counts moved by **addition**: the kimchi axiom gate **60 → 69** (all nine new public declarations
pinned in `kimchi/scripts/check_axioms.lean`, existence as well as axioms) and dead code **0 of 1606
at 180 roots → 0 of 1615 at 185 roots** (`roots.txt` gains the five terminals; `Chain128` and
`Chain128.range` are live through `lowest128Bits_sound`, `Chain128.exists_of_lt` through
`lowest128Bits_complete`, `splitRow` through `splitRow_holds_iff`), with `docs/architecture.md`'s
live root clause updated in the same pass. Unmoved and re-verified: axiom gates bulletproof-pcs 53 /
poseidon 19 / pasta 13 / snarky 5, both locked-target gates green **without** `--regen` (24
bulletproof-pcs / 6 kimchi exhibits), `runLinter` clean for `Kimchi` and `Bulletproof` with
`nolints.json` ungrown, `shake` clean, `kernel-replay.sh` clean, sorry census 0, authored `axiom`
declarations 0, and the build log still exactly the five `#eval` lines. The eleven-driver fixture
sweep was again deliberately **not** re-run: the change adds declarations to a gate-semantics file
and reaches no fixture, wire layer or executable path.

**The scope boundary of the split model.** Three things it does not cover, all carried as the scope
limits of `§ What the range check does not cover` in the file itself. The theorems are
field-generic: `p` odd and `2¹²⁸ ≤ p < 2²⁵⁶` are hypotheses of `lowest128Bits_split_not_unique`, not
facts discharged at `CompElliptic.Fields.Pasta.{Fp,Fq}` — that instantiation is the next milestone
and needs the characteristic literal and `CharP` plumbing this file does not import today.
[**Correction, iter-020.** Both halves of that last clause are false. The instantiation landed at
iter-019 — `fp_/fq_lowest128Bits_sound` and `fp_/fq_split_not_unique` discharge all three field
hypotheses at `Fp` and `Fq`; see the iter-019 route-1-phase-3 entry below. And the `CharP` pricing
was wrong: `Fp`/`Fq` are `abbrev`s down to `ZMod`, so `ZMod.charP` is found by instance search and
nothing had to be imported or threaded. The sentence is left standing, as with H-8b, so the
history is not rewritten.] The model
states the relation the emitted rows jointly assert, not the backend's reduction of that assertion:
`Reduction.purs`'s `reduceAffineExpression` allocates an internal variable per multi-term affine
expression, each pinned by its own generic row, and none of that allocation or row packing is
modelled. And what `lo` is used for downstream — it becomes the challenge fed to
`EndoScalar`/`EndoMul` — is outside this file.

**Iter-019 — M3′ half 1: the conditional average axis exists, beside the worst-case one.** Iters 017
and 018 landed nothing (017's plan phase died before writing objectives; 018's prover was killed
five minutes in, before it wrote a file), so this follows iter-016 directly. O-1b's remaining half
is the endpoint plumbing, and the user-approved route for it is **M3′**: adopt ironwood's joint
`Coins` axis *additively* rather than swapping ours. Four public declarations in
`Bulletproof/Forking/KnowledgeSoundness.lean`, under a new `### The conditional average axis`
subsection. `DeployedFamily.KimchiForkSpreadFamily` is `KimchiForkSpread` at every basis of one
family, at exactly the instantiation `DeployedFamily.attemptRuns` runs.
`DeployedFamily.attemptRuns_sum_le_of_forkSpreadFamily` sums the call count over table *and* tape
jointly: `(σ₀−1)^(k+1)·∑ ≤ (6·2¹²⁸)^(k+1)·|tables × tapes|`, upstream's
`recursiveAlgebraicFork_oracle_tape_sum_runs_le_unconditional` (`Recursive.lean:698`) shape.
`DeployedFamily.ReductionEfficientAvg` reads that sum as an efficiency gate — ironwood's
`ReductionEfficient` (`Algebraic.lean:1407`) term for term at our types. And
`DeployedFamily.reductionEfficientAvg_of_forkSpreadFamily` is the bridge between them, without which
the predicate would float. The mathematics is pure Fubini over the M2 corollary
`kimchiExtractRuns_sum_le_of_forkSpread`: **no quantifier commute anywhere in it**, no pigeonhole
over tapes, no witness tape chosen.

**Nothing here weakens the per-tape branch, and nothing here discharges an endpoint.** `Coins`,
`ReductionEfficient`, `relationFinder`, both `ipa{Vesta,Pallas}_knowledge_sound` and all five O-1a
declarations are untouched (audit item A-4): the `(2·2¹²⁸+1)^(k+1)` bound still holds for *every*
complete tape, which the average form cannot state, and it is still what both endpoints read.
Twinning the endpoints against `ReductionEfficientAvg` is half 2, and it is **not done**. Two costs
are stated rather than hidden. `KimchiForkSpreadFamily` has **no family-level witness at all** —
`exists_kimchiForkSpread_two_le_of_rounds` lives at the abstract layer over `Pre = Fin 5` and does
not instantiate `DeployedFamily`, whose prechallenge alphabet has 2¹²⁸ elements — and it quantifies
over the `DecodesFromPrefixes` witness rather than naming the deployed one, which is `private` to
`Forking/Deployed.lean`; that strengthens the hypothesis and so weakens everything derived from it.
The regime caveat travels with the number: `(6/δ)^(k+1)` at `k = 15` is ≈2⁵⁴ calls at `δ = 1/2` but
≈2³³⁹ at `δ = 2⁻²⁰`, worse than solving discrete log outright.

**One proof-engineering finding worth not re-deriving.** The Fubini and constant-sum-collapse steps
must stay at variables. Written inline at the concrete `Coins C k × tape` types they cost ~29 GB of
elaborator memory and five minutes — enough to OOM-kill a 30 GB build — because `Finset.sum_le_sum`
and `ring` then compare `Fintype.card` atoms whose instance terms carry the whole `IpaNode`
structure. Factored into the private `sum_prod_le_of_forall` over abstract `α`, `β` and `f`, the
file elaborates in 6.6 s at 6.5 GB, matching the baseline cost to within a tenth of a second. The
rationale is recorded at that declaration.

Counts moved by **addition**: the bulletproof-pcs axiom gate **53 → 57** (all four public
declarations pinned in `bulletproof-pcs/scripts/check_axioms.lean`, existence as well as axioms),
and `roots.txt` gains **one** entry, `reductionEfficientAvg_of_forkSpreadFamily`, from which the
walk reaches the other three — the minimal generating set the gate itself named. Dead code measured
**0 of 1626 at 192 roots** (192 resolved, 0 missing), and `docs/architecture.md`'s live root clause
was updated to 192 in the same pass. That total is **not this lane's alone**: objective 2's
concurrent `EndoScalar` lane had already landed 6 roots and 6 declarations when it was measured, so
185 + 1 is this lane's share and the split is the planner's to reconcile. The kimchi axiom gate
reads **75** for the same reason and did not move here.
[**Correction, iter-020.** The declaration half of that attribution is right and the root half is
wrong by 3. Measured split of `185 → 192`: the kimchi `EndoScalar` lane **+3** roots (5 added, 2
subsumed) and 6 declarations; **the user's concurrent `snarky/` work +3** roots
(`Snarky.equals_sound`, `Snarky.equals_complete`, `Snarky.sum_eval`, written inside the same
prover window and owned by neither lane); this lane **+1** root and 5 declarations.
`185 + 3 + 3 + 1 = 192` ✓, corroborated by this lane's own first `deadcode.sh` run reading 191.
The general rule this makes explicit: **`roots.txt` has three concurrent writers**, so the
workspace total is never attributable to one lane — reconcile per package with
`grep -vcE '^\s*(--|#|$)' <pkg>/roots.txt`, and check `snarky/` before crediting a residue to a
sibling. This is the stale-count defect class appearing *inside the correction that was guarding
against it*, which is worth saying plainly rather than quietly fixing the arithmetic.]
Unmoved and re-verified: axiom gates
poseidon 19 / pasta 13 / snarky 5, both locked-target gates green **without** `--regen` (24
bulletproof-pcs / 6 kimchi exhibits), `runLinter Bulletproof` clean with `nolints.json` ungrown,
`shake` clean, `check-style.sh` green, sorry census 0, authored `axiom` declarations 0, and the
build log still exactly the five `#eval` lines. The eleven-driver fixture sweep was again
deliberately **not** re-run: the change adds declarations to the forking counting layer and reaches
no fixture, wire layer or executable path.

**Iter-019 — route 1 phase 3: the lowest-128-bits split at the deployed Pasta fields.** (Written by
that lane, which was outside this file's write set; merged here at iter-020, verbatim but for the
final sentence, which item R5 and iter-020's step F2 have since overtaken.) `roots: 185 + 3` —
`r = 3`: five added (`lowest128Bits_sound_ofRow`, `fp_lowest128Bits_sound`,
`fq_lowest128Bits_sound`, `fp_split_not_unique`, `fq_split_not_unique`), two removed
(`lowest128Bits_sound`, `splitRow_holds_iff`, both subsumed by the first of those).
`EndoScalar.lean` gains six declarations, all axiom-clean. `lowest128Bits_sound_ofRow` reads the
split's affine relation off the generic row `splitRow` rather than assuming it; it is the first
statement in the tree whose hypotheses name both a `Generic` row and an `EndoScalar` `Witness`,
which turns `CLAUDE.md`'s composition claim from prose into a checked theorem (that sentence now
points at it). `split_not_unique_everywhere` lifts the refutation of the split's uniqueness from the
single value `x = 0` to every value that is a natural cast below `p`, by pairing `n` with `n + p`;
the cost is `p < 2²⁵⁶ → 2p ≤ 2²⁵⁶`, which both Pasta primes (≈2²⁵⁴) pay. `x` is a sponge squeeze,
so this is the difference between a reader answering "a squeeze is never 0" and having no answer at
all. The new final section `§ The split at the deployed Pasta fields` then discharges every field
hypothesis at `Fp` and `Fq` — `(2 : Fp) ≠ 0` / `(3 : Fp) ≠ 0` by `decide`, the three card facts by
`norm_num`, and no `CharP` threading at all (the earlier "needs `CharP` plumbing" pricing was wrong
and is corrected): `fp_lowest128Bits_sound` / `fq_lowest128Bits_sound` state the split's `< 2¹²⁸`
bound on each half, and `fp_split_not_unique` / `fq_split_not_unique` state that at **every**
element of either field the circuit still admits two accepted pairs with different low halves.
Together that is the deployed statement: `lowest128Bits` bounds each half and determines neither.
Scope limit 3 of `§ What the range check does not cover` ("not discharged at the deployed Pasta
fields") is retired accordingly — and at iter-020 it was **deleted** rather than kept as a marked
placeholder, with 4→3 and 5→4 renumbered, once this document's citation of it was rewritten
number-free (item R5). Nothing now cites a scope limit by number except limits 1 and 2, which did
not move.

**Iter-020 — M3′ half 2: the twin average endpoints, and the joint axis closes O-1b's plumbing.**
`Bulletproof/Forking/KnowledgeSoundness.lean` gains a new final section `§ 11. The joint (table ×
tape) axis` — 15 declarations, 9 of them public — plus two public counting companions in `§ 9`: 17
in all, 11 public, every one axiom-clean. It is the probability half of the conditional branch
iter-019's counting half opened, on
ironwood's own coin axis: upstream's `ComputedAlgebraicFSFamily` bundles `Coins = table × tape` and
measures its endpoint over `(basis) × Coins`, so the fork tape is **sampled inside the probability
space** rather than fixed as a parameter. `relationFinderAvg` and `DerivedUDLAdvantageLEAvg` restate
the finder and the residual at that coin type; `derivedUDLAvg_iff_residual_measure`,
`three_way_cover_avg`, the three summands and
`deployedExtract_noOpening_measure_le_of_textbookDL_avg` rebuild the cover and the terminal over it;
`DiscreteLogRelationHardForAvg` gates hardness by `ReductionEfficientAvg`; and
`ipaVesta_knowledge_sound_avg` / `ipaPallas_knowledge_sound_avg` are the twin endpoints, with the
**same** right-hand side `(Q + k + 1)·3/2¹²⁸ + (2ᵏ + 1)·ε + δ`.

**`hcoins` is discharged structurally rather than assumed.** No statement on the joint axis carries
`coins.Complete`: the one place the per-tape branch spends it — the presence summand's call to the
locked `deployedExtract_failure_measure_le` — gets it from
`Zcash.Snark.RecursiveForkTape.toCoins_complete`, which holds for *every* tape. What is paid for
that is the space: a bad fork tape is now charged to the failure probability rather than excluded by
hypothesis. **Neither endpoint implies the other**, and the per-tape branch is untouched — `Coins`,
`ReductionEfficient`, `relationFinder`, both `ipa{Vesta,Pallas}_knowledge_sound` and all five O-1a
declarations keep their statements verbatim (audit item A-4), and the primary endpoints still read
the worst-case branch. The average branch has its **own unconditional satisfiability companion**,
`DeployedFamily.reductionEfficientAvg_of_worstCase`, so `ReductionEfficientAvg` is not a predicate
reachable only through an unwitnessed hypothesis; `one_le_of_reductionEfficientAvg` rules out an
`R = 0` gate on that axis as `one_le_of_reductionEfficient` does on the per-tape one. But the
*interesting* `R` is still conditional: `KimchiForkSpreadFamily` has **no witness at any layer**,
the `σ₀ = 4` exhibit being abstract and over `Pre = Fin 5`, and the regime caveat travels with the
number — `(6/δ)^(k+1)` at `k = 15` is ≈2⁵⁴ calls at `δ = 1/2` but ≈2³³⁹ at `δ = 2⁻²⁰`, worse than
solving discrete log outright. There is **no quantifier commute** anywhere in the lane: the cover is
pointwise in the tape and no witness tape is chosen.

Two proof-engineering notes. The double-fibre measure step is `private
uniform_prod_prod_fiber_bound`, stated at abstract `{A ρ₁ ρ₂}` for the reason iter-019 recorded at
`sum_prod_le_of_forall` — it is two upstream lemmas composed
(`uniformOfFintype_prod_fiber_bound_right` at `B := ρ₁ × ρ₂`, whose fibre obligation is
`uniformOfFintype_prod_fiber_bound`), and inlining it at the concrete triple product is the shape
that cost 29 GB last iteration. Measured with `/usr/bin/time -v` after each declaration landed, the
file went **6.83 s / 6.77 GB → 7.78 s / 6.78 GB**; nothing needed bisecting.

Counts moved by **addition**. `roots.txt`: bulletproof-pcs **57 → 61** (+4 — the two twin endpoints,
from which the walk reaches the whole probability half, plus the two average-branch anti-vacuity
companions, which the endpoints cannot reach because they *assume* the gate); kimchi **79 → 80**
(+1, the droppable tail below). Workspace **192 → 197 at dead 0 of 1645**, and
`docs/architecture.md`'s live root clause was updated to 197 **with the per-package split spelled
out**, per the R1 correction above. Axiom gates: bulletproof-pcs **57 → 68** (every new public
declaration pinned, existence as well as axioms), kimchi **75 → 77**. Unmoved and re-verified:
poseidon 19 / pasta 13 / snarky 5, both locked-target gates green **without** `--regen` (24
bulletproof-pcs / 6 kimchi exhibits), `runLinter Bulletproof` and `runLinter Kimchi` clean with
`nolints.json` ungrown (its one diff is the user's `Snarky.*` entry, renamed by their concurrent
work), `shake` clean over all eight libraries, `check-style.sh` green, `kernel-replay.sh` clean,
sorry census 0, authored `axiom` declarations 0, and the build log still exactly the five `#eval`
lines at 8633 jobs. The eleven-driver fixture sweep was again deliberately **not** re-run: the
change adds declarations to the forking probability layer and the gate-semantics layer and reaches
no fixture, wire layer or executable path. This lane adds no module and no import, so
`docs/module-deps.{dot,svg}` are unchanged and no regeneration is owed.

**The droppable kimchi tail, landed.** `fp_lowest128Bits_sound_ofRow` /
`fq_lowest128Bits_sound_ofRow` give the row-reading form of the split's soundness a *deployed* entry
point: until they landed, only the field-generic `lowest128Bits_sound_ofRow` read the affine
relation off the generic row, so the per-curve statements still assumed it. Net **+1** root rather
than the predicted +0 — the two plain `fp_/fq_lowest128Bits_sound` do **not** become reachable
through the `_ofRow` pair (different proof terms), so what dropped out of the minimal set was
`lowest128Bits_sound_ofRow` itself, now reached from both new terminals and still pinned in
`kimchi/scripts/check_axioms.lean`.

**Iter-021 — route 1 phase 4: the Poseidon gate chain meets the production sponge permutation.**
Every other modelled gate's `Gate/Semantics/` development ends at an *external* oracle; Poseidon's
ended at itself — `sound` said a satisfying row's `s5` is `perm M w.s0 rc`, and `perm` is defined
three declarations above it in the same namespace. `Gate/Semantics/Poseidon.lean` grows from 62
lines to a full development (24 declarations, 22 public) whose terminals are
`fq_/fp_poseidonChain_blockCipher`: **eleven satisfying gate rows compute `Poseidon.blockCipher`**
at the deployed `fq_kimchi` / `fp_kimchi` parameters. That is the 55-round `mina_poseidon`
permutation (`permutation.rs` `poseidon_block_cipher`) the duplex sponge runs on every rate
crossing, which `Poseidon.FqSponge` drives to produce every Fiat–Shamir challenge the verifier
reads, and which `poseidon/scripts/check_sponge_vectors.sh` validates against recorded production
traces — so the oracle is fixture-checked data, not another Lean definition of this tree's own.
`55 = 11 × 5` exactly (`fqParams_size` / `fpParams_size`, proved off the array *spine* through
`Array.size_map`, so no 254-bit numeral is ever evaluated), so the chain is eleven rows with no
ragged tail; the shape is read from the PureScript that emits it —
`Constraint/Kimchi/Poseidon.purs` splits the first 55 states into eleven chunks of five, one
`PoseidonGate` row each, and appends a `Zero` row carrying the final state.

The engineering is one bridge and one fold. `round_eq_fullRound` is the whole of the mathematics:
the two round functions are the same map — same `x^7` S-box, same MDS row indexing, constants added
after the MDS pass on both sides, no initial ARK on either — differing only in argument order and
in how the matrix is packaged, so `ring` closes it componentwise. `rounds` is the ℕ-indexed iterate
that the gate's five-at-a-time `perm` and the sponge's whole-table `Array.foldl` both refine to;
`blockCipher_eq_rounds` is the fold bridge, proved by `Array.foldl_toList` into a `List.foldl` and
then by induction from the front, splicing the head off with `rounds_add` at `a = 1` (the iterate
peels from the end, a left fold from the front, so one of the two has to be turned around).
`List.reverseRecOn` was the planned route and was not needed. Round constants enter as `paramsRc`,
`Array.getD` at an explicit `(0, 0, 0)` — chosen over `a[i]!` deliberately, because `getD` takes its
default as an argument and so needs no `Inhabited F` instance on a bare field.

**What is assumed, stated in the theorems' own docstrings.** The MDS matrix and the round constants
enter as **data**: the statements are at `mdsOfParams fqParams` and at constants agreeing with
`paramsRc fqParams` below 55. That the index a real proof carries holds those same values is an
ingestion-layer fact this lane does not prove, and the `Chain` hypothesis is what a satisfying
witness table supplies. Nothing is claimed about the absorb/squeeze automaton, the rate/capacity
discipline or the challenge derivation — only the permutation — and nothing about security: this is
a faithfulness result, not a hardness one. **The anti-vacuity companion is not optional and landed
with it**: `buildChain` / `buildChain_chain` / `buildChain_blockCipher` and the per-curve
`fq_/fp_poseidonChain_complete` say that for every input state an eleven-row satisfying chain
*exists* and computes the permutation of that state, so `Chain` is not a predicate nobody has
inhabited.

**The deployed column layout, landed rather than dropped.** `Kimchi/Lift.lean` gains
`fq_/fp_block_blockCipher`, the same statement over a witness *table* read through the existing
`cellMap` / `rcMap` — the permuted `s0 s4 s1 s2 s3` register order with the output state on the next
row. The chain's `link` hypothesis is **`rfl`** there, because `cellMap` reads `s5` off the next
table row: the deployed layout *enforces* the chain rather than assuming it, and only "every row
holds" and "the coefficient rows carry the deployed constants" survive as hypotheses. Stated at an
ℕ-indexed table, so no `Fin n` cyclic-successor bookkeeping is spent.

Counts moved by **addition**, with one visibility change. Step A dropped `private` from
`Poseidon.sbox` / `fullRound` / `blockCipher` (the theorem is *about* `blockCipher`, so it must be
nameable; the ∀-quantification trick that saved iter-019 does not apply when the private name
appears in the statement) — measured alone, that moved **nothing**: dead **0 of 1645 at 197 roots**
before and after, the three already being reachable from `squeeze` / `absorb1`. The declarations
then moved it to **0 of 1671 at 203 roots** (+26 = 24 in `Gate/Semantics/Poseidon.lean`, 22 of them
public, plus the two public `Lift.lean` corollaries). `roots.txt`: kimchi **80 → 86** (+6 — the four
per-curve chain terminals and the two layout corollaries, from which the walk reaches all the chain
machinery); bulletproof-pcs 61, pasta 27, poseidon 18 and snarky 11 **unmoved**, which is the
per-package reconciliation. Axiom gates: kimchi **77 → 101** (+24, every new public declaration
pinned, existence as well as axioms); bulletproof-pcs 68 / pasta 13 / poseidon 19 / snarky 5
unmoved. Every new closure is exactly `[propext, Classical.choice, Quot.sound]` — **no**
`native_decide` certificate is reached at all, the Pasta parameters entering as data rather than
through a certified count. `runLinter Kimchi` and `runLinter Poseidon` clean with `nolints.json`
ungrown, `shake` clean over all eight libraries, `check-style.sh` green at 115 files, both
locked-target gates green **without** `--regen` (24 bulletproof-pcs / 6 kimchi exhibits), sorry
census 0, authored `axiom` declarations 0, `kernel-replay.sh` clean over 96 modules, and the build
log still exactly the five `#eval` lines — `Semantics/Poseidon.lean`'s moved from line 60 to 77 and
still prints `true`. File elaboration,
measured with `/usr/bin/time -v`: `Gate/Semantics/Poseidon.lean` **9.04 s / 6.48 GB** (the lane's
final measurement; an earlier draft of this paragraph carried the mid-lane 6.8 s / 6.70 GB) and
`Kimchi/Lift.lean` **15.1 s / 6.69 GB**, both far under the 60 s / 15 GB trigger, so nothing needed
factoring.

**Two of the twelve fixture drivers were re-run, and deliberately only two.** (Twelve, not eleven:
`ls */scripts/check_*.sh` minus `check_axioms` / `check_locked_target` = 12. The count does not
change the two-of-N decision, which was correct.)
`check_sponge_vectors.sh` (7/7 over both Pasta base fields) and `check_fq_sponge.sh` (40/40 + 40/40
op traces, 8/8 + 8/8 group-map vectors) — because step A edits the very file they validate, and
because the new theorem's whole claim to meaning is that `blockCipher` is production-checked. The
other nine are out of this diff's reach: no wire layer, no executable verifier path, no IPA fixture,
no index or permutation fixture.

**`docs/module-deps.{dot,svg}` were regenerated, and the regeneration IS owed this time** — this
lane adds the module edge `Kimchi.Gate.Semantics.Poseidon → Poseidon.Basic` and turns
`Kimchi.Lift → Kimchi.Gate.Poseidon` into `Kimchi.Lift → Kimchi.Gate.Semantics.Poseidon` (shake
demands the swap rather than both, and `Kimchi → Kimchi.Gate.Semantics.Poseidon` then drops out as
transitively implied). But **most of the regenerated diff is not this lane's — measured against
`git diff`, i.e. against the repository's single initial commit**: 20 of its 23 changed lines are
the user's concurrent `snarky/` module rename (`Snarky.Monad` → `Snarky.Circuit.DSL.Monad` and the
rest of that restructuring), and two more are stale-graph residue — `Semantics.EndoScalar →
Pasta.CompElliptic` and `→ Kimchi.Gate.Generic`, edges that landed at iter-019 while iter-020
correctly owed no regeneration. Against the **iteration** baseline
(`archon[021/plan] → archon[021/prover]`) the artifact delta is **2 of 2 lines, all this lane's**,
so the two readings are exactly opposite and the sentence is only true of the first.
**The general rule, which is why the baseline has to be named:** this repository has a single
commit over an empty tree, so any counter this loop reports against bare `git diff` is a
*project-lifetime* delta, not an iteration delta; use the archon git-dir
(`archon[NNN/plan] → archon[NNN/prover]`) for iteration attribution. Node and edge totals are
unchanged at 86 and 132. Do not read that artifact's diff as this lane's footprint.

**One docstring was falsified by this lane and is corrected; one outside the write set is flagged.**
`kimchi/Kimchi/Gate/Poseidon.lean`'s file docstring said "Unlike the elliptic-curve gates there is
no external Mathlib spec: the gate *defines* the permutation" — true of the *row* level only, now
that
the eleven-row chain has an external, fixture-validated spec one layer up; corrected in prose, no
declaration in that file touched. `CLAUDE.md`'s faithfulness-pattern section, which describes every
gate's progression as ending at Mathlib's group law, is stale in the same way — **flagged, not
edited**: it is outside this lane's write set. *(Corrected at iter-022, which put `CLAUDE.md`
in its write set for that one clause.)*

**Iter-022 — the kimchi joint-axis twin, half 1: the conditional-average counting layer.**
*(Provenance note, added at iter-023: **iter-022's review phase never ran** —
`.archon/proof-journal/sessions/session_22/` holds `milestones.jsonl` and nothing else, and there
is no `iter/iter-022/review.md`. So every counter in this block except the roots and the axiom
pins is the lane's own self-report rather than a review re-measurement. The iter-023 plan phase
re-verified by hand what is cheap to re-verify: the 13 declarations exist, the tree is sorry-free,
`roots.txt` counts per package, and the five new axiom pins.)* The
standing user-set target is conditional-average twins of `vesta_/pallas_kimchi_knowledge_sound`,
built by lifting to kimchi the M3′ technique that landed on the bulletproof side at iters 019–020.
This is a two-iteration arc and this is its first half — the counting half. It adds, at the end of
the `KimchiFamily` block that already holds `attemptRuns` / `ReductionEfficient` /
`DiscreteLogRelationHardFor`, a new section *The conditional average axis*: six public
declarations and one private arithmetic helper, standing **beside** the per-tape block and
replacing nothing in it.

**What it states.** `KimchiFamily.ReductionEfficientAvg R` says the extractor's call count, summed
over the product `Coins C nc k × Zcash.Snark.RecursiveForkTape Prechallenge (k + 1)` — the oracle
table and the fork tape *jointly*, which is upstream's own coin axis — is at most `R` times the
cardinality of that product, at every basis. It is reachable two ways.
`reductionEfficientAvg_of_forkSpreadFamily` reaches it at the conditional
`(6 · 2 ^ 128 / (σ₀ − 1)) ^ (k + 1)`, from `attemptRuns_sum_le_of_forkSpreadFamily` (the joint sum
bound: `Bulletproof.Forking.kimchiExtractRuns_sum_le_of_forkSpread` at each fixed table, then
Fubini) divided through by `(σ₀ − 1) ^ (k + 1)`. `reductionEfficientAvg_of_worstCase` reaches it
**unconditionally** at `(2 · 2 ^ 128 + 1) ^ (k + 1)`, with no tape chosen and no completeness side
condition, because `RecursiveForkTape.toCoins_bounded` bounds every tape's node degree.
`one_le_of_reductionEfficientAvg` is the floor: no `R` below 1 satisfies the gate, so it cannot be
met by a number advertising a zero-call reduction.

**The one genuine difference from the bulletproof twin.** `DeployedFamily.claim` depends on the
basis alone; **kimchi's claim is adversary output**, so both the claim and the SRS the extractor
runs against — `runSrs` is `srsOfBasis` with `U` replaced by the WARM post-`ζ` base the run's own
sponge squeezes — are functions of the oracle table too. `KimchiForkSpreadFamily` is therefore
indexed by `(basis, table)`, demanding the spread at every warm base the family can reach. That is
neither a weakening nor a strengthening of the bulletproof predicate; it is what this
instantiation requires. In the other direction this port **improves** on its model in one place:
the bulletproof twin ∀-quantifies its `DecodesFromPrefixes` witness because the deployed one is
`private` to another module, whereas `kimchiDecodesFromPrefixes` is `private` to *this* file and so
is named outright — a weaker hypothesis, hence strictly stronger consequences.

**What is still assumed, and the regime caveat that travels with the number.**
`KimchiForkSpreadFamily` has **no witness at any layer**.
`Bulletproof.Forking.exists_kimchiForkSpread_two_le_of_rounds` exhibits a spread at `σ₀ = 4` over
`Pre = Fin 5`, at the abstract layer, instantiating no family whose prechallenge alphabet has
`2 ^ 128` elements — the exhibit does not transfer, and this is the substance half of O-1b, still
open. Only the conditional number is interesting, and it says something only for adversaries whose
per-round good-challenge density is not tiny: `(6/δ) ^ (k + 1)` at `k = 15` is about `2 ^ 54` calls
at `δ = 1/2` and about `2 ^ 339` at `δ = 2 ^ (−20)`, worse than solving discrete log outright.
Hence the unconditional companion, which is what keeps the branch from being a predicate only an
unwitnessed hypothesis can satisfy.

**The per-tape branch is untouched, and half 2 is not here.** `Coins`, `ReductionEfficient`,
`relationFinder`, `attemptRuns`, `reductionEfficient_of_bounded`,
`exists_complete_reductionEfficient`, `one_le_of_reductionEfficient`, `DiscreteLogRelationHardFor`
and both locked endpoints are the **worst-case** branch and stand verbatim; neither branch implies
the other, and no endpoint's `hEff` is discharged by anything added here. Two docstrings gained one
pointer clause each (`Coins`, and `exists_complete_reductionEfficient` — the conditional average
branch is a *separate statement*, not a consequence of that `R`); the two endpoint docstrings were
**not** touched, since repointing their "no table-averaged bound follows from it" sentence is half
2's job, when the twins exist. **Nothing in this iteration reaches a knowledge-soundness
statement** — half 2 (the averaged relation finder, the averaged four-way cover, the four summands
over the enlarged space, and the two twin endpoints) is the next iteration, and lands whole
because every declaration below those endpoints is non-terminal and rooting plumbing is what makes
a dead-code gate vacuous.

**The Lift-layer anti-vacuity debt from iter-021, paid.** `Kimchi/Lift.lean`'s
`fq_/fp_block_blockCipher` shipped gated on `hrows` + `hq` over a **free** witness/coefficient
table pair, with nothing in the tree exhibiting a satisfying table — against this tree's own rule
that a new gate predicate ships with its companion in the same commit. `fq_/fp_block_complete` now
exhibit the pair at every starting state, over four private assemblies (`buildTab`/`buildQTab` and
their Fp twins) that write `buildChain`'s states into the permuted `s0 s4 s1 s2 s3` register order.
The Gate-layer `fq_poseidonChain_complete` does not transfer for free — `cellMap` is a *specific*
permuted layout — but at that layout
`cellMap (buildTab rc s0 i) (buildTab rc s0 (i + 1)) = buildChain … i` is `rfl`, which is what
makes the row conjunct the chain's own `holds` field. Still **not** claimed, and still the `hq`
hypothesis of the theorem above: that a real `Kimchi.Index` carries `paramsRc fqParams` in its
Poseidon coefficient columns. That is the ingestion layer, and it is untouched.

Counts moved by **addition only** — 13 declarations, 0 modified, 0 renamed, 0 signatures touched;
the only edits to pre-existing text are the two docstring pointer clauses above. Dead code
**0 of 1671 at 203 roots → 0 of 1684 at 208 roots** (208 resolved, 0 missing). `roots.txt`: kimchi
**86 → 91** (+5 — the two `*_block_complete`, from which the walk reaches the four assemblies, and
the three average-branch terminals, from which it reaches `KimchiForkSpreadFamily`,
`attemptRuns_sum_le_of_forkSpreadFamily`, `ReductionEfficientAvg` and the Fubini helper);
bulletproof-pcs 61, pasta 27, poseidon 18 and snarky 11 **unmoved**, which is the per-package
reconciliation (61 + 91 + 27 + 18 + 11 = 208, so the whole +5 is this lane's). Axiom gates: kimchi
**101 → 109** (+8, every new public declaration pinned, existence as well as axioms);
bulletproof-pcs 68 / pasta 13 / poseidon 19 / snarky 5 unmoved. Every new closure is exactly
`[propext, Classical.choice, Quot.sound]` — **no** `native_decide` certificate is reached, on
either file.

`runLinter Kimchi` clean with `nolints.json` ungrown, `shake` clean over all eight libraries — it
demanded **no** direct `Bulletproof.Forking.Game` import, the names being reachable transitively
through `Bulletproof.Forking.KnowledgeSoundness`, so **no module-graph regeneration is owed** and
`docs/module-deps.{dot,svg}` are unchanged — `check-style.sh` green at 115 files, both
locked-target gates green **without** `--regen` (24 bulletproof-pcs / 6 kimchi exhibits; the kimchi
one reads this lane's lead file by path and none of its five pinned texts moved), sorry census 0,
authored `axiom` declarations 0, `kernel-replay.sh` clean over 96 modules, and the build log
exactly the five `#eval` lines with no `warning:`, no `error:` and no `Try this:`. The job count
reads **8633** against the iter-021 baseline's 8637; this lane adds no module and no import edge,
so the −4 is **not attributable here** — it is consistent with the concurrent `snarky/` work,
whose library contributes 17 jobs beyond the shared closure today (8616 without it). File
elaboration, `/usr/bin/time -v`, and **measured against the same box's own pre-edit baseline
rather than against the recorded one**, because the recorded figures were taken elsewhere and a
cross-box comparison would misprice this diff by an order of magnitude:
`Verifier/KnowledgeSoundness.lean` **49.07 s / 7.48 GB before → 51.15 s / 7.49 GB after** (+2.1 s,
+11 MB) — the recorded 29.5 s baseline is a *different machine*, not a 21 s regression — and
`Kimchi/Lift.lean` **9.30 s / 6.83 GB → 9.94 s / 6.88 GB** (+0.6 s, +47 MB) against a recorded
15.1 s. Both are far under the 90 s / 20 GB split trigger, so the recorded decision — **this file
is not split** — is unchanged; the reversal signal stands for half 2's measure chain. The general
form of this, worth carrying: an elaboration figure is only a delta against a baseline re-measured
on the same box in the same session.

**Three of the twelve fixture drivers were re-run, and only because step 0 edits
`Kimchi/Lift.lean`.** `check_linearization.sh` and `check_index_fixture.sh` are the two that
actually reach that module
(`Kimchi.Protocol.Linearization` and `Kimchi.Index.Satisfies` both `import Kimchi.Lift`);
`check_perm_fixture.sh` was run with them and does **not** — it goes through
`Kimchi.Permutation.Wiring → Permutation.Copy`, so it was out of reach and is reported as such. All
three green. The other nine were skipped and the skip is deliberate: this diff reaches no wire
layer, no executable verifier path, no IPA fixture and no sponge fixture.

**Iter-023 — the kimchi joint-axis twin, half 2: the probability layer and the two twin
endpoints. This closes the user's kimchi joint-axis route.** Half 1 (iter-022) built the counting
layer; this half is the probability layer over
`(setup scalars) × (Coins × RecursiveForkTape)` and the twins that read it. Thirteen declarations
— 7 public, 6 private — all in `kimchi/Kimchi/Verifier/KnowledgeSoundness.lean`, in a new `§ 18
The joint (table × tape) axis` at the **end** of the file, after `§ 17`'s locked endpoints. That
placement is a correctness condition, not a style one: `kimchi/scripts/check_locked_target.sh`
renders each pinned block from the **first** line matching its start regex, and three of the five
patterns (`^theorem vesta_kimchi_knowledge_sound`, `^theorem pallas_kimchi_knowledge_sound`,
`^noncomputable def relationFinder`) are **prefixes** of names this lane adds, so a twin placed
before its primary would silently re-pin the wrong declaration and diff-fail.

**What the twins state.** `vesta_kimchi_knowledge_sound_avg` and
`pallas_kimchi_knowledge_sound_avg` measure the same event as the primaries — the verifier accepts
while the extractor fails to hand back a satisfying witness table — but over
`(SetupIndex (2^k) → ScalarField) × (Coins × RecursiveForkTape Prechallenge (k+1))`, the fork tape
sampled *inside* the probability space rather than fixed as a parameter. The right-hand side is
**byte-identical** to the primaries': the same four summands
`(Q + k + 1)·3/2¹²⁸ + (2ᵏ + 1)·ε + δ + (Q + 1)·szBudget/2¹²⁸`, the same constants. The hypothesis
list is the primaries' **minus `coins`, minus `hcoins`**, with the two gates replaced by
`DiscreteLogRelationHardForAvg` and `ReductionEfficientAvg`.

**`hcoins` is discharged structurally rather than assumed, and that is the branch's one genuine
improvement.** Every per-tape statement carries `coins.Complete` as a hypothesis. Here the tape is
`q.2.2.toCoins` for a *sampled* `q.2.2`, and `Zcash.Snark.RecursiveForkTape.toCoins_complete`
holds for **every** tape, so the obligation is a theorem about the sampled tape rather than an
assumption about an externally fixed one. It is spent at exactly one place,
`acceptExtractionFailure_measure_prod_le_avg`, and no statement in the section carries a
completeness argument. What is paid for it: the measured event lives over a larger space, so a
fork tape on which the extractor does badly is **charged** to the failure probability rather than
assumed away. **Neither endpoint implies the other.**

**The route, and why bulletproof's did not transfer.** The IPA twin's `presence_summand_avg` is a
double-fibre bound over a per-`(s, τ)` statement, resting on
`Bulletproof.Forking.deployedExtract_failure_measure_le` — a bound over `Coins` alone. Kimchi has
no reachable counterpart: `kimchiExtract_failure_measure_le_of_stableBase` and `…_of_stable` are
**`private` to `Game.lean`**, and the public non-product `kimchiExtract_failure_measure_le` is the
fixed-base, fixed-claim form, which does not apply to kimchi's WARM post-`ζ` base. The route
actually taken is the **`S`-slot trick** on the public product lemma
`kimchiExtract_failure_measure_prod_le_of_stableBase`, which is generic in an index type `S` and
takes its fork tape as an `S`-indexed *family*: instantiating
`S := (setup scalars) × RecursiveForkTape` puts the tape inside the sampled index, and one new
private measure transport `uniform_prod_assoc_swap` carries the resulting bound over
`((setup × tape) × Coins)` to the `(setup × (Coins × tape))` the section measures. That one helper
serves arm (4) as well, which is why it was preferred over de-privatizing upstream — a
`bulletproof-pcs` edit that would *still* have needed a local copy of the equally-private
`uniform_prod_prod_fiber_bound`.

**One proof-engineering finding worth not re-deriving.** Instantiating the `S`-generic product
bound directly at `bs s := augOfSetup (scalarBasis B s.1)` repeats that term in twenty argument
slots, and the `hstable` slot then has to unify the family's own claim map against the abstract
`κ` by whnf through all of them: measured here, it overruns the 200000-heartbeat budget outright
(`(deterministic) timeout at whnf` at the `claimStable_runClaimTriple` argument). The fix is the
same shape as iter-019's Fubini finding and iter-022's `sum_prod_le_of_forall`: a separate private
rung, `acceptExtractionFailure_measure_prod_le_index`, holding the basis map and the coin family
as **opaque variables** over an arbitrary finite nonempty `S`. At an opaque `bs` each slot is one
application and the same unification lands far inside the budget. A second instance of the same
trigger, from the other direction: passing `bs := fun s => …s.1…` while `S` is still a
metavariable makes the projection `s.1` unresolvable and times out identically — pin `S` by name
at the call site. **No `maxHeartbeats` or `maxRecDepth` was raised** (both are forbidden here).

**Nothing weakens the per-tape branch, and there is no quantifier commute anywhere.** `Coins`,
`ReductionEfficient`, `relationFinder`, `attemptRuns`, `DiscreteLogRelationHardFor`,
`reductionEfficient_of_bounded`, `exists_complete_reductionEfficient`,
`one_le_of_reductionEfficient` and **both locked endpoints** stand verbatim — the per-tape branch
is the worst-case branch, and `acceptExtractionFailure_measure_prod_le` was **copied**, not
generalized, precisely so the primaries' proof path does not move. The four-way cover is proved
**pointwise in the tape** (`four_way_cover` is already stated at an arbitrary `coins`); no witness
tape is ever chosen, no `∃ tape, ∀ basis` statement is formed, and nothing is summed over bases.
Three docstrings gained one pointer clause each — the two primary endpoints, whose "no
table-averaged bound follows from it (external-audit O-1b, open)" sentence now names the averaged
twin as a *separate statement, not a consequence*, and `DiscreteLogRelationHardFor`. Those edits
are legal against the lock because extraction starts at the `theorem`/`def` line and a docstring
precedes it; both `check_locked_target.sh` were re-run immediately after and pass **without**
`--regen`.

**What is still assumed, unchanged from half 1.** `KimchiForkSpreadFamily` has **no witness at any
layer**: `Bulletproof.Forking.exists_kimchiForkSpread_two_le_of_rounds` exhibits `σ₀ = 4` over
`Pre = Fin 5` at the abstract layer and instantiates no family whose prechallenge alphabet has
`2¹²⁸` elements. The regime caveat travels with the number: `(6/δ)^(k+1)` at `k = 15` is about
`2⁵⁴` calls at `δ = 1/2` and about `2³³⁹` at `δ = 2⁻²⁰` — worse than solving discrete log
outright. And the anti-vacuity guards `honestKimchiFamily_wins` / `honestKimchiFamily_failure_set`
are stated on the per-tape space and are **not** restated here; the win conjunct does not read the
tape, so nothing about them is weakened, but no averaged restatement is proved and none is
claimed. O-1b's substance remains open; only its plumbing closed, at iter-020.

Counts moved by **addition only** — 13 declarations, 0 renamed, 0 signatures touched; the only
edits to pre-existing text are the three docstring pointer clauses above. Dead code **0 of 1684 at
208 roots → 0 of 1697 at 210 roots** (210 resolved, 0 missing). `roots.txt`: kimchi **91 → 93**
(+2 — the two twin endpoints, and only those; the walk from them reaches the whole probability
layer, so no plumbing is rooted, which is the move that would have made the gate vacuous);
bulletproof-pcs 61, pasta 27, poseidon 18 and snarky 11 **unmoved**, which is the per-package
reconciliation (61 + 93 + 27 + 18 + 11 = 210, so the whole +2 is this lane's). Axiom gates: kimchi
**109 → 116** (+7, every new public declaration pinned, existence as well as axioms);
bulletproof-pcs 68 / pasta 13 / poseidon 19 / snarky 5 unmoved. Measured closures: the five
curve-generic public declarations (`relationFinderAvg`, `DerivedUDLAdvantageLEAvg`,
`relation_summand_avg`, `residual_summand_avg`, `DiscreteLogRelationHardForAvg`) are exactly
`[propext, Classical.choice, Quot.sound]`; the two per-curve twins additionally reach CompElliptic's
certified `native_decide` witnesses for the Pasta constants (`vestaBase`/`pallasBase` `ax_1`,
`ax_2` and the respective `_nsmul_Gpt` anchor) — the admitted set, and the same one the primaries
carry.

`runLinter Kimchi` clean with `nolints.json` ungrown, `shake` clean over all eight libraries — it
demanded **no** direct `Bulletproof.Forking.Game` import, the names being reachable transitively
through `Bulletproof.Forking.KnowledgeSoundness`, so **no module-graph regeneration is owed** and
`docs/module-deps.{dot,svg}` are unchanged — `check-style.sh` green at 115 files, both
locked-target gates green **without** `--regen` (24 bulletproof-pcs / 6 kimchi exhibits), sorry
census 0, authored `axiom` declarations 0, `kernel-replay.sh` clean over 96 modules, and the build
log exactly the five `#eval` lines with no `warning:`, no `error:` and no `Try this:`. The job
count reads **8633**, the same as iter-022's; this lane adds no module and no import edge, and the
count has three concurrent writers, so it is reported as a verdict and not as a delta. File
elaboration, `/usr/bin/time -v`, measured against **this box's own pre-edit copy in the same
session** rather than any recorded figure: `Verifier/KnowledgeSoundness.lean` **49.24 s / 7.14 GiB
before → 60.98 s / 7.19 GiB after** (+11.7 s, +51 MiB). Far under the 90 s / 20 GB split trigger,
so the recorded decision — **this file is not split** — is unchanged, and difference-3 above is a
second, independent reason a pinned declaration must not move.

**All twelve fixture drivers were skipped, deliberately.** This diff is confined to a proof layer
at the very top of the kimchi stack: it reaches no executable verifier path, no wire layer, no
fixture decoder, no IPA or sponge fixture, and no `Kimchi.Lift`, `Kimchi.Index` or
`Kimchi.Permutation` module. Both `check_locked_target.sh` **were** in scope and were run twice
each (after the endpoints landed, and again after the docstring clauses).

**Iter-024 — no Lean landed, and that is why the counters above are confirmed twice.** That
iteration's plan phase died to an API error before rewriting `PROGRESS.md`, so the dispatcher
re-read the previous iteration's objectives and re-assigned a lane that had already landed; the
prover diagnosed it in minutes, wrote no Lean, and converted the run into a measurement pass, after
which the review re-ran every gate itself — which is what gave iter-023's numbers their first
independent confirmation.

**Iter-025 — route 1 phase 5a: the Poseidon ingestion link, from a free coefficient table to a real
index.** *(REMOVED at PR review, 2026-08-01, together with iter-021's Lift-layer block theorems
(`fq_/fp_block_blockCipher`, the generic `block_blockCipher`) and their `fq_/fp_block_complete`
companions — the user's scoping decision: the gate-semantics endpoint
(`Gate/Semantics/Poseidon.lean`, where every other modelled gate also stops) is the right resting
point until the verifier↔circuit translation layer exists and names what it needs; the layout and
ingestion layers were preparation for an interface not yet designed. Recover them from PR #287's
history on a need-to basis. The fixture driver's four ingestion checks left with them; the
paragraphs below stand as the record of what was built.)* Iter-021 proved that eleven satisfying
Poseidon rows compute the production sponge
permutation, but only *given* `hq` — that the coefficient rows carry the deployed round constants —
over a **free** `qTab`, and said so in its own docstring: *"what is not claimed here is that a real
`Kimchi.Index` carries these constants in its Poseidon coefficient columns — that is the ingestion
layer, and it remains the `hq` hypothesis."* This lane makes it a statement about a real index, and
discharges its whole hypothesis set on recorded production data.

Six declarations and one `deriving`, all additive; no statement was weakened and no signature moved.
`Kimchi.Lift.Gate.Poseidon.block_blockCipher` is the parameter-set-and-length-generic form of the
two deployed block theorems, which are now one-line corollaries of it with **byte-identical
statements**. `Kimchi.Index.CarriesPoseidonBlock` is the ingestion predicate: the index's `mds`
field is `Gate.Poseidon.mdsOfParams p`, and each of the eleven rows named by `row` is a `.poseidon`
row whose coefficient cells carry that row's own five round constants at the `rcMap` layout
(`coeff (3j + t) = p.roundConstants[5i + j][t]`, which is what `Constraint/Kimchi/Poseidon.purs`
writes). `Kimchi.Index.poseidon_holds_of_rowSatisfies` projects the `.poseidon` branch out of
`rowSatisfies`'s dispatch, kept separate so a `match`-elaboration surprise would cost one small
lemma rather than the main proof; `blockCipher_of_satisfies` is the index-layer theorem; and
`fq_index_poseidonBlock` / `fp_index_poseidonBlock` are the two deployed corollaries.
`Kimchi.Gate.Poseidon.Mds` gains `deriving DecidableEq` — one word, and the reason the predicate
decides.

**The `Fin n` reindexing, where the obvious route is a trap.** `Satisfies` lives over `Fin n` with a
cyclic `i + 1` (`rowWitness wTab i = cellMap (wTab i) (wTab (i + 1))`) while the block theorem lives
over `ℕ`. The bridge is an explicit `row : ℕ → Fin n` carried together with
`hrow : ∀ i, row (i + 1) = row i + 1`, **not** an `((i : ℕ) : Fin n)` coercion. `Fin`'s
`AddMonoidWithOne` and `CommRing` are `def`s carrying `attribute [scoped instance]` in Mathlib
(`Mathlib/Algebra/Group/Fin/Basic.lean`, `Mathlib/Data/ZMod/Defs.lean`) precisely because the
ℕ→`Fin n` coercion loop makes `x < n` elaborate as `x < ↑n`, *"silently introducing wraparound
arithmetic"*. With `row`/`hrow` no `Fin` algebra and no `< n` side condition appears anywhere, and
`hrow` is used in exactly one place — identifying the block theorem's next row `row (i + 1)` with
the cyclic successor `row i + 1` that `rowWitness` reads. The cyclic reading is *correct* here
rather than merely tolerated, because `rowWitness` is cyclic in the same sense.

**Which table goes with which curve, because the naming is a genuine trap.** `Fq` is the Vesta
*base* field and `Fp` the Pallas base field, so `fq_kimchi` / `fp_kimchi` are indexed by the field a
table lives over — but a Vesta-commitment proof's circuit is native to `Fp`, so
`Bulletproof.IpaVesta.curve.frParams = fpParams` and `IpaPallas.curve.frParams = fqParams`
(`Bulletproof/Wire.lean`). The new corollaries are therefore named by the **parameter table** and
not by a curve: `fq_index_poseidonBlock` is the one a *Pallas*-commitment proof's index satisfies
and is decided on `index_pallas_nc2`; `fp_index_poseidonBlock` is the *Vesta* one and is decided on
`index_vesta` and `index_vesta_nc2`. The existing block theorems' "Vesta-side" gloss is the field
axis, is defensible, and was deliberately left as it stands rather than re-glossed here.

**Scope, stated in the theorems' own docstrings.** Ingestion now covers the *permutation*: the
index's Poseidon coefficient rows carry the deployed round constants, its `mds` field is the
deployed matrix, and a satisfying witness table therefore carries row `row 0`'s state cells to
`Poseidon.blockCipher` of them at row `row 11` — the appended `.zero` row, kimchi's convention being
that a Poseidon row's output state is read off the next row. It covers **nothing** about the duplex
sponge built on that permutation: not the absorb/squeeze automaton, not the rate/capacity split, not
the challenge derivation `Poseidon.FqSponge` performs. That axis ("route 1 phase 5b") was
**descoped by the user (2026-08-01)**: beyond the block, a sponge run is only the starting state
of each 55-round sequence — initial state, rate-position absorption adds between blocks, squeezed
reads — ordinary generic-row facts a consumer proves locally when it interprets a concrete
hashing circuit, where it knows the circuit structurally. A kimchi-side sponge-run predicate over
raw index data would pattern-match that structure back out of a gate table. The kimchi Poseidon
tower is therefore complete at the ingestion layer, and no docstring here gestures past it.

**Anti-vacuity is the production decision, and the toy exhibit was deliberately not built — which
settles a question `STRATEGY.md` had left open.** The tree's rule is that a new gate predicate ships
an anti-vacuity companion in the same commit. For `CarriesPoseidonBlock` that companion is
`kimchi/scripts/check_index_fixture.lean`, and that is a decision rather than a shortcut: a toy
exhibit would construct its own `Poseidon.Params` and then satisfy the predicate by construction,
witnessing a *different* statement — that some index carries *some* constants — not the one that
could be vacuous, which is the deployed corollary at `fqParams` / `fpParams`. The
satisfiable-at-real-parameters content already exists one layer down as
`Lift.Gate.Poseidon.fq_/fp_block_complete`, which exhibit a `(wTab, qTab)` pair meeting both
hypotheses at every starting state. So the answer to the open question is yes, with a scope: for a
predicate whose content is *"a real production index does this"*, the fixture layer **is** the
anti-vacuity companion, and only recorded data can be one.

The driver gained four checks per fixture, on all three (`index_vesta`, `index_vesta_nc2`,
`index_pallas_nc2`, all `n = 32`): the ingestion decision
`decide (CarriesPoseidonBlock idx C.frParams (row 3))`, which is the corollary's full hypothesis set
beside `Satisfies`; the corollary's **conclusion** re-derived on the data — the state cells of row
14 equal `Poseidon.blockCipher C.frParams` of the state cells of row 3, 55 rounds run in the kernel;
and two negatives, a shifted start (`row 4`) and the other curve's round-constant table, each
required to be *rejected*. All twelve pass. The wrong-table control needed one driver-local helper,
`paramsOfTable`: the two deployed `Params` values live over *different* fields, so the control
cannot name the other curve's `Params` directly and reads that curve's raw generated constants into
this curve's scalar field instead.

**Step 0, banked first: the two averaged honest guards.**
`Verifier.Forking.vesta_/pallas_honest_extraction_failure_measure_le_avg` are the joint
`(table × tape)` twins of the per-tape guards beside them, now against the
`*_kimchi_knowledge_sound_avg` endpoints. They must live in `Verifier/Forking/Honest.lean` because
`honestKimchiFamily`, both per-curve families and both `*HonestFamily_wins` lemmas are `private` to
that file. `hcoins` is **gone** from them — the averaged endpoint discharges it structurally through
`RecursiveForkTape.toCoins_complete` — so each carries one fewer hypothesis than its per-tape twin,
and neither per-tape statement was touched. `Verifier/KnowledgeSoundness.lean`'s § 18 sentence *"no
averaged restatement is proved, and none is claimed"* is now a pointer to these two; that one clause
is the whole of this diff's edit to that file, it sits outside all five locked-target blocks, and
both locked-target gates passed **without** `--regen`.

Counts. Dead code **0 of 1697 at 210 roots → 0 of 1707 at 228 roots** (228 resolved, 0 missing); the
+10 audited declarations are exactly this lane's six, its two decidability instances, and the two
averaged guards. `roots.txt`: kimchi **93 → 99** (+6 — the two deployed ingestion corollaries, the
two averaged guards, and the two instances, whose only consumer is the out-of-library driver; the
walk from the corollaries reaches everything else, so no plumbing is rooted); bulletproof-pcs 61,
pasta 27 and poseidon 18 **unmoved**; snarky **11 → 23** (+12), which is the user's concurrent
PureScript-alignment work and **not** this lane's — the per-package reconciliation is exactly what
attributes it (61 + 99 + 27 + 18 + 23 = 228). Axiom gates: kimchi **116 → 126** (+10, every new
public declaration pinned, existence as well as axioms); bulletproof-pcs 68 / pasta 13 / poseidon 19
unmoved; snarky 5 → 20, again the user's.

Measured closures, not predicted. All eight ingestion-layer pins are within
`[propext, Classical.choice, Quot.sound]`, three of them narrower still — `CarriesPoseidonBlock`,
its `Decidable` instance and `poseidon_holds_of_rowSatisfies` at `[propext, Quot.sound]`, and
`Gate.Poseidon.instDecidableEqMds` at no axioms at all — and **no CompElliptic certificate appears
anywhere in them**, which is what a curve-generic layer whose deployed corollaries name only
parameter tables should look like. The two averaged guards reach the same set as the endpoints they
wrap: the standard three plus the Pasta `native_decide` witnesses (`vestaBase` / `pallasBase` `ax_1`
and `ax_2`, and the respective `_nsmul_Gpt` anchor).

Gates. `runLinter` clean over all eight libraries with `nolints.json` ungrown; `shake` clean over
the same eight and demanding **no** new import, so no module-graph regeneration is owed and
`docs/module-deps.{dot,svg}` are unchanged; `check_shape_literals.sh` green over 42 files; sorry
census 0; authored `axiom` declarations 0. The build log is the five `#eval` lines and nothing else
— no `warning:`, no `error:`, no `Try this:` — at **8637** jobs over the CI target list
(`make lean-build`'s seven plus `KimchiFixture`). That number has three concurrent writers and is
reported as a verdict, not a delta.

The concurrent-writer caveat that the root, job and style counts have always carried reached the
build log itself for the first time this iteration, and is recorded rather than smoothed. Five
minutes after the green build above, the user — mid-restructure of `snarky/` — saved
`snarky/Snarky/Circuit/DSL/Boolean.lean`, and the target list that includes `Snarky` began failing
there; ten minutes later that file built and `snarky/Snarky/Laws.lean` was failing instead. Every
error in both runs was inside `snarky/`, and re-running the same list **minus `Snarky`** (8620 jobs)
is green with the identical five `#eval` lines and zero diagnostics — so the failure is a live human
edit inside a package this lane must not touch and is not attributable to this diff. Every gate that
loads `Snarky`'s oleans — `scripts/deadcode.sh`, the eight-library `runLinter` and `shake` runs, and
`snarky/scripts/check_axioms.sh` — was run against the state that built green, and `deadcode.sh`
does fail on the later state, with the single error `object file … Snarky/Laws.olean … does not
exist`. Nothing in that dependency reaches a kimchi declaration, and no `.lean` file outside
`snarky/` moved between the two. `check-style.sh` is likewise a verdict and not a delta: **green**,
reading 115 files at 07:53 and 116 at 08:03, the difference being a `snarky/` module the user added
in between.

All **seven** kimchi fixture drivers were run and all are green; the five skips are the
bulletproof-pcs and poseidon ones, deliberately, since no declaration in those packages changes and
`Mds` is a kimchi type. `check_index_fixture.sh` is this lane's own deliverable and carries the
twelve new checks described above. `check_perm_fixture.sh` (8.6 s), `check_ps_witness.sh` (10.6 s),
`check_linearization.sh` (14.3 s) and `check_shape_literals.sh` all read the index/lift layer this
diff touches. Two are expensive enough that the cost is worth recording so nobody re-prices
them: `check_kimchi_verifier.sh` at **716 s / 6.7 GiB peak**, and `check_vk_correspond.sh` at
**3 h 37 min** on this box — the latter run against the identical tree earlier in the same
session (no `.lean` file under `kimchi/`, `pasta/`, `poseidon/` or `bulletproof-pcs/` changed after
it started, and `Snarky` is not in its import closure), which is why it was not re-run a second
time. `kernel-replay.sh` is
clean over 97 modules at lean4checker `91a7f0e8`, with 0 stale oleans pruned.

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

Two deferrals still stand (O-1b and O-3) — O-1b now only in the sense §O-1b spells out: its
milestone chain and endpoint plumbing are closed, its conditional bound is reachable only from an
unwitnessed hypothesis.

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
* **O-1b — the conditional average `(6/δ)^k`. Its milestone chain and its endpoint plumbing are
  CLOSED as of iter-020; what remains open is the substance** — the spread hypothesis at deployed
  parameters is unwitnessed, so the conditional number is reachable by nothing in this tree, and ε
  is still posited rather than derived. See §O-1b for the three clauses that travel with the word
  "closed".

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

1. `Bulletproof/Forking/Game.lean` `kimchiForkFrom_runs_le` — an `n`-bounded coin tape makes
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
It is bracketed below as well as above: `one_le_kimchiExtractRuns` (`Game.lean`) pins the
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

#### O-1b — the endpoint plumbing is CLOSED; the conditional bound remains hypothetical

**Status, reconciled at iter-020.** Milestones **M1–M5 are closed** (iters 012–015): the whole
fork-spread counting layer in `Forking/Game.lean`, up to the tape-averaged bound at the extractor
and its satisfiability exhibit at every round count. The **endpoint plumbing** — route **M3′** — is
now closed too: half 1 (the family spread and the joint table-and-tape bound) landed at iter-019 and
half 2 (the probability layer and the twin average endpoints) at iter-020. Read the M3 paragraph
below for the route and the correction that produced it; earlier revisions of this file said both
"all of O-1b closed" and a bare "OPEN", and neither was right.

**What "closed" means here, and the three clauses that travel with the word.** It means the two
averaging axes now **join, conditionally**, on upstream's joint (table × tape) axis:
`ipa{Vesta,Pallas}_knowledge_sound_avg` state the same bound over a space in which the fork tape is
sampled, gated by `ReductionEfficientAvg`, which `reductionEfficientAvg_of_forkSpreadFamily`
discharges from a family fork spread at `(6·2¹²⁸/(σ₀−1))^(k+1)`. It does **not** mean the item's
substance is delivered:

1. **The locked endpoints still read the worst-case branch.** `ipa{Vesta,Pallas}_knowledge_sound`
   and the kimchi endpoints are unchanged and are gated by the per-tape `ReductionEfficient`. The
   twins stand beside them; neither implies the other.
2. **The spread at deployed parameters is still an unwitnessed hypothesis.**
   `DeployedFamily.KimchiForkSpreadFamily` has no family-level witness at any layer, and the
   abstract `σ₀ = 4` exhibit over `Pre = Fin 5` does not transfer. Without it the average gate is
   reachable only at the worst-case `(2·2¹²⁸+1)^(k+1)`
   (`reductionEfficientAvg_of_worstCase`) — non-vacuous, but no better than O-1a's number.
3. **The regime caveat is unchanged.** `(6/δ)^(k+1)` at `k = 15` is ≈2⁵⁴ calls at `δ = 1/2` and
   ≈2³³⁹ at `δ = 2⁻²⁰`. What *closing it fully* would buy is below, and is still bought by nothing
   in this tree: ε derivable from a time bound rather than posited.

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
| The run counter itself | `Bulletproof/Forking/Game.lean` `kimchiExtractRuns` — a *projection* of the extractor's own recursion, deliberately never a separate definition |
| Our worst-case bound (O-1a) | `Game.lean` `kimchiExtractRuns_le` → `Deployed.lean:863` `deployedExtractRuns_le` → the two families' `reductionEfficient_of_bounded` / `exists_complete_reductionEfficient` |
| Its anti-vacuity companion | `Game.lean` `one_le_kimchiExtractRuns` — the counter is `≥ 1` on every table and every tape |
| The same floor at the level the endpoints read | the two families' `one_le_of_reductionEfficient` (`Bulletproof/Forking/KnowledgeSoundness.lean:746`, `Kimchi/Verifier/KnowledgeSoundness.lean:1811`) — no `R` below `1` satisfies `ReductionEfficient`, so `hEff` cannot be met by a number advertising a zero-call reduction. Via `Deployed.lean:877` `one_le_deployedExtractRuns` on the IPA side |
| Upstream's worst-case bound | ironwood `Recursive.lean`, "Worst-case run bound": `≤ (2·|F| + 1)^k`, plus `reductionEfficient_exponential` (`Algebraic.lean:1440`) — about *upstream's* recursion, which is why O-1a had to be proved rather than cited |
| **M1** the spread hypothesis | `Game.lean` `KimchiForkSpread` — two clauses (node + leaf); **nothing in this tree proves one at deployed parameters**, by design. Narrowed to the diagonal `p = A.run O` at iter-013 (M4′), which makes it exactly upstream's, and to tape-derived coins at iter-014 (M4″) |
| **M1** the named scan attempts | `Game.lean` `kimchiScanCandidate` (upstream `ExpectedRuns.lean:426`), `Game.lean` `kimchiLeafCandidate` (no upstream analogue) — definitionally the inline lambdas of `kimchiForkFrom`'s two arms |
| **M1** the good sets | `Game.lean` `kimchiGoodChallenges` (upstream `:440`), `Game.lean` `kimchiLeafGoodChallenges` |
| **M1** the pointwise bounds | `Game.lean` `kimchiForkFrom_node_runs_le` (upstream `:448`, minus the abort unit), `Game.lean` `kimchiForkFrom_leaf_runs_le` (novel) |
| **M1** the depth-0 tape sum | `Game.lean` `kimchiForkFrom_sum_runs_le_leaf` — `(σ₀−1)·∑_tape runs ≤ 6·\|Pre\|·\|tapes\|`, the base case of M2's induction |
| **M4′** the diagonal narrowing | `Game.lean` `KimchiForkSpread` (both clauses at `p = A.run O`), with `kimchiForkFrom_sum_runs_le_leaf` restated there; its degeneracy pins are `kimchiLeafGoodChallenges_eq_empty_of_unstable` and `kimchiForkSpread_eq_zero_of_leaf_unstable` |
| **M2** the depth induction | `Game.lean` `kimchiForkFrom_sum_runs_le_of_forkSpread` (upstream `:590–897`, `d ↦ e + 1`, two summands, no `2 ≤ σ₀`), over the normal form `kimchiScanCandidate_runs_cases` (upstream `:557`) |
| **M2** the root corollary | `Game.lean` `kimchiExtractRuns_sum_le_of_forkSpread` — `(σ₀−1)^(k+1)·∑_tape runs ≤ (6·\|Pre\|)^(k+1)·\|tapes\|`, beside the unconditional `kimchiExtractRuns_le` and superseding nothing. **As shipped at iter-013 it was vacuous for every `σ.k ≥ 1`**; M4″ below is what makes it contentful |
| **M4″** the coin-axis narrowing | `Game.lean` `KimchiForkSpread`'s node clause at `child : Pre → RecursiveForkTape Pre (e + 1)`; its degeneracy pins are `kimchiGoodChallenges_eq_empty_of_order_nil` and `kimchiNodeFloor_eq_zero_of_forall_coins` (stated at the un-narrowed clause, so the fix does not erase its own justification) |
| **M4″** the satisfiability exhibit | `Game.lean` `exists_kimchiForkSpread_two_le` (`KimchiForkSpread … 4` at `σ.k = 0`, `Pre = Fin 5`, `F = G = ℚ`) — **leaf clause only** at that round count, the node clause being vacuous there; M5 below generalizes it |
| **M5** the every-round-count exhibit | `Game.lean` `spreadExhibit_forkSpread` (**both** clauses at `σ₀ = 4`, at every `σ.k`) over the fork-success induction `spreadExhibit_forkFrom_isSome`, with the headline `exists_kimchiForkSpread_two_le_of_rounds` (the `σ.k = K` conjunct is what makes it say more), the applied bound `spreadExhibit_extractRuns_sum_le` (`3^(k+1)·∑ ≤ 30^(k+1)·\|tapes\|`) and its anti-vacuity companion `spreadExhibit_card_le_extractRuns_sum` (`\|tapes\| ≤ ∑`). The exhibit family is the iter-014 one **generalized in place**, so every `σ.k = 0` statement survives as its instance at `0` |
| **M1** the genericity evidence | `bulletproof-pcs/scripts/check_ironwood_generic.lean` §9 — the rank / marginalization / scan-bound / tape layer at `Pre` by literal `exact` |

**Iter-012 — milestone M1 of this route landed.** Eight public declarations in
`Bulletproof/Forking/Game.lean`, in a new *The conditional average under fork spread* subsection,
all reducing to `[propext, Classical.choice, Quot.sound]`: the two named scan attempts, the two
good sets, `KimchiForkSpread`, the two pointwise run bounds, and the depth-0 tape-sum lemma (see
the table rows above for locations). Two facts this iteration established, both of which change how
the remaining route should be scoped:

1. **Upstream's counting layer is alphabet-generic, so O-1b ports two sections rather than a file.**
   `ExpectedRuns.lean`'s §`RankCounting`, §`Marginalization`, §`PaidScan`, §`Positions`,
   §`SumHelper` and §`ScanRankBound`, together with `Recursive.lean`'s `RecursiveForkTape` layer,
   carry only `[Zero]`/`[DecidableEq]`/`[Fintype]` on the challenge alphabet — no `Field`, no
   `Module`. Each instantiates at `Pre` by a literal `exact`, and that is now pinned by
   compilation in `check_ironwood_generic.lean` §9. Only §`NodeBound` (`:426–568`) and
   §`SpreadTheorem` (`:583–910`) mention `recursiveAlgebraicForkFrom` and must be restated.
2. **Our recursion reads the round prefix off the passed proof, so the spread predicate needed a
   diagonal — done at iter-013 (M4′).** Upstream quantifies over oracle tables and reads the
   reprogrammed round's prefix off `A.run O`; ours threads a proof `p` and reads `prefixes p j`, so
   the good sets carry `p`. M1 stated the predicate at *arbitrary* pairs `(O, p)` and its docstring
   called that "deliberately stronger". **That reading was wrong, and the statement is now
   corrected.** Off the diagonal the predicate is not stronger but plausibly *degenerate*: at a
   prefix `t = prefixes p j` the adversary never lands on, no reprogrammed run can return to `t`,
   the good set is empty, and `σ₀ ≤ 0` — so all three M1 bounds would have read `0 ≤ …`. `A`, `Pf`
   and `prefixes` are unconstrained parameters, so that is not an exotic corner;
   `kimchiLeafGoodChallenges_eq_empty_of_unstable` is the compiled exhibit. Iter-013 narrowed both
   clauses to `p = A.run O`, which **costs nothing** — the `first` arm passes `(O, p)` through, the
   scan arm rebuilds `p' := A.run O'`, and `kimchiExtractRuns` enters at `(O, A.run O)`, so the
   diagonal is the only pair the recursion visits — and which makes `KimchiForkSpread` **exactly**
   upstream's `ForkSpread`. Read the two predicates as equivalent; what remains strong is upstream's
   own ∀-table floor, which is the recorded ε → σ₀ open research below.

The depth-0 case is where our recursion stops being a transcription. Upstream's base case costs a
bare `1`; ours is the Schnorr fork, which runs a scan keeping *two* of three branches, so it needs a
spread floor and a rank argument of its own — hence `KimchiForkSpread`'s second clause, and hence
`kimchiForkFrom_leaf_runs_le`, which has no upstream counterpart. The `6` in the depth-0 bound has
slack: the honest total is `3·N·CP·|tapes₀|^N` (unit costs `≤ N·CP·|tapes₀|^N` from `σ₀ ≤ N`, scans
`2·N·CP·|tapes₀|^N` from `card_scanRank_lt_mul_le`). Upstream's `2 ≤ σ₀` is **not** needed at depth
0 and is deliberately absent from that statement. The one place a *statement* differs from
upstream's is the node bound, which drops upstream's leading `1 +`: that unit pays for an abort arm
on a zero incumbent challenge, and `kimchiForkFrom`'s `e + 1` case has no such arm.

**M2 and M4′ landed at iter-013, but M2's bound was vacuous until M4″ (iter-014).** M4′ is the
narrowing in (2); M2 is the `e + 1` induction
`kimchiForkFrom_sum_runs_le_of_forkSpread` (upstream `:590–897`) plus the public corollary
`kimchiExtractRuns_sum_le_of_forkSpread` at `kimchiExtractRuns`. Three deviations from upstream's
induction, all in our favour and all recorded on the theorem itself: the exponents shift by one (`d
↦ e + 1`, the induction variable staying `e`); the base case is `kimchiForkFrom_sum_runs_le_leaf`
rather than a one-line computation, because our depth-0 leaf scans; and there are two summands
rather than three, since our node bound has no abort unit — which leaves the closing arithmetic at
`5·N·(6N)^(e+1) ≤ (6N)^(e+2)`, a factor of slack, so the `6` is kept rather than tightened.
Upstream's `2 ≤ σ₀` is **not** a hypothesis here: its only role upstream is to supply `1 ≤ |F|`, and
`[Zero Pre]` gives `Nonempty Pre` outright — so our statement is weaker in hypotheses, not merely
re-indexed. Nothing existing was restated to make M1, M2 or M4′ fit — `ReductionEfficient`, both
families' endpoints and all of O-1a's declarations are untouched, which is the one failure mode this
route must not have (audit item A-4). The single permitted correction is one sentence in
`kimchiExtractRuns_le`'s docstring, which had denied that the conditional average exists in this
tree.

**A spread floor quantified over arbitrary coin trees is degenerate too — fact (2)'s mistake on
the other axis, found at iter-014 and fixed by M4″.** `RecursiveForkCoins Pre (d + 1)` carries an
arbitrary `order : List Pre`, and `nextForkChallenge attempt seen [] = { output := none,
runs := 0 }`. Both scanning arms of `kimchiForkFrom` therefore return `none` unconditionally on
`.node [] _`, so at certificate depth `0` and round `σ.k − 1` — legal exactly when `1 ≤ σ.k` — the
node good set is empty and the clause forces `σ₀ = 0`. **M2's bound as shipped at iter-013 therefore
read `0 ≤ …` at every `σ.k ≥ 1`**, which is every deployed parameter set: the conditional block was
an implication out of a hypothesis satisfiable only at the degenerate floor. The compiled pins are
`kimchiGoodChallenges_eq_empty_of_order_nil` and `kimchiNodeFloor_eq_zero_of_forall_coins`, the
latter deliberately stated at the *un-narrowed* clause so the fix cannot erase its own
justification. M4″ narrows the clause to tape-derived coins, whose order is `List.ofFn ⇑order` for
an equivalence and hence a full enumeration; the induction's only two uses already instantiated it
there, so the repair cost two call sites. The other direction is now pinned as well:
`exists_kimchiForkSpread_two_le` exhibits a satisfying instance at `σ.k = 0` with `σ₀ = 4`,
exercising the **leaf** clause only. Node-clause satisfiability at `σ.k ≥ 1` was left as the next
milestone, and this text priced it as a genuinely harder argument whose hard part was the *third*
scan finding an eligible challenge in the residual list `rest` — which is **false**, and M5
(iter-015) is the correction: see the M5 row above and the iter-015 register paragraph.

**Dependency-side note: upstream has the same defect, one depth later.** ironwood's own `ForkSpread`
(`ExpectedRuns.lean:583`) quantifies over `childC : F → RecursiveForkCoins F d` in exactly the same
way. Its certificate depth-`0` arm takes `.leaf`, the only constructor of `RecursiveForkCoins F 0`,
and costs a bare `1` with no scan, so upstream is safe at `d = 0` and degenerate from `d ≥ 1`, i.e.
from `k ≥ 2`. Ours collapsed one step earlier because **our** depth-0 leaf scans. `zcash/ironwood`
is a pinned git dependency we do not own: this is recorded, not patched, and no fork of the package
is planned.

Counts moved by **addition** only, and the invariant's real content (*dead 0*, *all roots resolved*)
holds: the bulletproof-pcs axiom gate **33 → 41** (all eight new declarations pinned, existence as
well as axioms), and dead code **0 of 1573 at 173 roots → 0 of 1581 at 175 roots**. The two new
`roots.txt` entries are the minimal generating set the gate itself named — the node bound and the
tape-sum lemma — and they sat in a group **explicitly labelled temporary**: they were M2's
scaffolding, and the group was deleted at iter-013 when M2's corollary consumed them, exactly as
its own comment instructed.
`docs/architecture.md`'s live root clause was updated in the same pass. Unmoved and re-verified:
axiom gates kimchi 60 / poseidon 19 / pasta 13 / snarky 5, both locked-target gates green
**without** `--regen` (24 bulletproof-pcs / 6 kimchi exhibits), `check_extractor_computes.sh`,
`check-style.sh` 115 files, `runLinter` clean for `Kimchi` and `Bulletproof`, `shake` clean, sorry
census 0, authored `axiom` declarations 0, and the build log still exactly the five `#eval` lines at
8633 jobs. The eleven-driver fixture sweep was again deliberately **not** re-run: the change adds
declarations to the forking game's counting layer and touches no existing statement, no fixture, no
wire layer and no executable path.

**The actual obstacle, so nobody mistakes it for plumbing.** The averaging axes differ. Upstream
sums over **tapes** for a fixed oracle table; our `ReductionEfficient` sums over **tables** for a
fixed tape. Bridging them is the work. Note the endpoints are ∀-tape, so a consumer is free to
instantiate at a favourable tape — the same probabilistic-method shape the upstream bound has,
which is the natural route.

**M3 is deferred — a decision taken at iter-014 and re-taken at iter-015, not a pending item.** Its
original reason has expired: it sat behind node-clause satisfiability, and M5 supplies that at
every round count. The decision does not change, because the ∃/∀ obstacle stands on its own and
was always the substantive one:
`ReductionEfficient` is `∀ basis, ∑_O … ≤ R · |tables|` and the endpoints consume
`∃ coins, Complete ∧ ReductionEfficient coins R`, so the goal shape is `∃ tape, ∀ basis`, while
pigeonholing a tape-sum bound yields only `∀ basis, ∃ tape` — `attemptRuns basis O coins` depends on
`basis` through both the claim and the adversary. Of the three routes: **(1)** summing over bases is
ruled out, since it inflates `R` by `|bases|`; **(2)** a basis-uniform spread plus a
basis-independent witness tape is the only route that reaches the endpoints, and it is research;
**(3)** shipping `∀ basis, ∃ tape` labelled as *not* `ReductionEfficient` is cheap and honest but
buys nothing at the endpoints. The unconditional route dodges the obstacle only because
`kimchiExtractRuns_le` is pointwise and basis-uniform.

**Sharpening the diagnosis, and superseding route (2)'s verdict — corrected at iter-019.** The
paragraph above is right that the axis swap is blocked, but too coarse about *what* blocks it. The
obstacle is the **per-tape predicate shape** and nothing else: `ReductionEfficient` fixes one tape
∀ basis, that tape is hardwired into `relationFinder fam coins`, and the reduction samples its own
basis (`scalarBasis B q.1`). So the `∃ tape, ∀ basis` the endpoints need would cost a union bound
over |bases| ≈ 2^(255·(2^k+2)) — astronomically past the worst case it was meant to improve on.
Route (2)'s verdict — that a basis-uniform spread plus a basis-independent witness tape "is the only
route that reaches the endpoints, and it is research" — is **superseded**, because upstream has no
such obstacle at all: its `Coins` is table × tape (`Algebraic.lean:857`), its `ReductionEfficient`
averages both jointly (`:1407`), and its endpoint samples the tape inside the probability space
(`:1464`). The adopted route is therefore **M3′**, which *adds* that shape rather than swapping
ours. Half 1 — the family spread and the tape-averaged joint bound, pure Fubini over the M2
corollary with no quantifier commute — landed at iter-019 (see that paragraph in the per-iteration
region above). Half 2 is the twin average endpoints with a tape-sampling `relationFinder`, templated
on ironwood `Algebraic.lean:1464`, and it is **phase-sized, not research**.

**Quantitative regime, if plumbed.** `(6/δ)^k` at `k = 15`: `δ = 1/2` → ≈ `2^54` adversary calls
(fine for a reduction); `δ = 2^-20` → ≈ `2^339`, worse than solving DL outright. The exponent in
`k` is real, so any resulting claim must be scoped to adversaries whose per-round good-challenge
density is not tiny. Say so wherever the number is quoted.

**Also open upstream.** `ExpectedRuns.lean`'s own file docstring: "An unconditional polynomial AFK
bound remains open." Do not expect to find it there.

**Successor.** With M5 the O-1b **milestone chain M1–M5 is closed**, and what remains of the item is
the endpoint plumbing, which is now the scheduled route **M3′** (see the correction above). Half 1
landed at iter-019; half 2 — the twin average endpoints reading `ReductionEfficientAvg`, with a
`relationFinder` that samples the tape inside the probability space — is scheduled and not started.
Route 1's second phase, the lowest-128-bits split landed at iter-016, ran in parallel with all of
this; it is a kimchi gate-semantics lane and touches nothing here.

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

   **The obligation follows a provenance quote out of this tree.** A clause describing what a
   PureScript or Rust source *does* — a signature, a call graph, which argument a function
   constrains — is a claim about **that** tree, and is checked against it by opening the file,
   exactly as a coordinate into `formal/` is. Iters 005–008 swept doc coordinates against the
   **Lean** tree; the first iteration to quote the `.purs` sources put its residue there instead
   (two false clauses about `RangeCheck.purs`'s `lowest128Bits'`, corrected at iter-011 — see the
   per-iteration paragraph above). A provenance citation is exactly as checkable, and exactly as
   trusted-without-checking, as a line number into a document here.

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
