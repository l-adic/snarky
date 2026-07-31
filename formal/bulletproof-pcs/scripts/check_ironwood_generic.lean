import Bulletproof.Forking.Game
import Zcash.Snark.Soundness.Forking.Adversary.ExpectedRuns

/-!
# The reuse seam: our fork game IS ironwood's, at a prechallenge alphabet

`Forking/Game.lean` proves its escape and counting layer over an abstract
`variable {T Pre Pf : Type*}` block — an alphabet with no instances at all. This file records what
the *deployed* alphabet buys: `Fin (2 ^ 128)` carries `Zero`, `DecidableEq`, `Fintype` and
`Nonempty`, and with those, ironwood's own scanner, escape set, counting bound and coin-tree
traversal apply by literal `exact`. So the corresponding blocks of `Game.lean` are duplicates of
upstream, not forced ports.

Two further facts are pinned here because the whole abstraction rests on them:

* the frozen `Wins` (`Game.lean`'s `def Wins`) *is* `Zcash.Snark.fsWinsFull` (Adaptive.lean:30) at
  `m = 0`, by `Iff.rfl` — so one game statement serves bare IPA (`m = 0`) and kimchi (`m > 0`), and
  the win condition stays `VerifierAcceptsAt`, the wire verifier, with no bridging lemma;
* the error divides by `Fintype.card Pre = 2 ^ 128`, never by a field cardinality.

Every example below is discharged by `exact`ing an upstream declaration. Nothing is proved here,
and no patch is applied to the pinned ironwood (83a98f7f).
-/

namespace Bulletproof.Forking.IronwoodGeneric

open Bulletproof Zcash.Snark
open scoped ENNReal

/-- The deployed challenge alphabet: `squeezeChallenge` squeezes 128 bits, then endo-expands. -/
abbrev Pre : Type := Fin (2 ^ 128)

theorem card_pre : Fintype.card Pre = 2 ^ 128 := Fintype.card_fin _

/-! ## 1. `Pre` is not a field, yet carries every instance upstream's escape layer asks for. -/

example : Zero Pre := inferInstance
example : DecidableEq Pre := inferInstance
example : Fintype Pre := inferInstance
example : Nonempty Pre := inferInstance

/-! ## 2. Transcript decoding asks nothing of the alphabet.

`PrefixDecode` (Adaptive.lean:15) is pure round/chain bookkeeping — no arithmetic, no instances. -/

example (T P : Type) (k : ℕ) (prefixes : P → Fin k → T)
    (roundOf : T → ℕ) (chainAt : T → Fin k → T)
    (h1 : ∀ p (j : Fin k), roundOf (prefixes p j) = (j : ℕ))
    (h2 : ∀ p (j i : Fin k), (i : ℕ) ≤ (j : ℕ) → chainAt (prefixes p j) i = prefixes p i)
    (h3 : ∀ t (i : Fin k), (i : ℕ) < roundOf t → chainAt t i ≠ t) :
    PrefixDecode T k prefixes :=
  ⟨roundOf, chainAt, h1, h2, h3⟩

/-! ## 3. The upstream scanner, at `Pre`, by `exact`.

Literal instantiations of the upstream scan names `Game.lean` *consumes* rather than re-proves:
`nextForkChallenge_runs_le` and `nextForkChallenge_output_rest_length_le` in
`kimchiForkFrom_runs_le`, `nextForkChallenge_two_more` in `nextFork_fst_ne_none` /
`nextFork_snd_ne_none`, `nextForkChallenge_isSome_of_good` and
`nextForkChallenge_other_good_mem_rest` in the spread exhibit's `spreadExhibit_forkFrom_isSome`,
and `nextForkChallenge_output_fresh` / `_output_attempt` in `kimchiForkFrom_realizes` —
`_output_fresh` also in `kimchiForkFrom_leaf_runs_le` and in `spreadExhibit_forkFrom_isSome`. The
point of the pins below is that each such name typechecks at `Pre` by `exact`, so none of those
consumers needed an alphabet-specific restatement. -/

theorem pre_scan_isSome {α : Type*} (attempt : Pre → RecursiveForkAttempt α)
    (seen : List Pre) {q : Pre} {order : List Pre}
    (hmem : q ∈ order) (hq0 : q ≠ 0) (hseen : q ∉ seen)
    (hgood : (attempt q).output.isSome) :
    (nextForkChallenge attempt seen order).output.isSome :=
  nextForkChallenge_isSome_of_good attempt seen hmem hq0 hseen hgood

theorem pre_scan_two_more {α : Type*} (attempt : Pre → RecursiveForkAttempt α)
    (order : List Pre) (hcomplete : ∀ q : Pre, q ∈ order) (first : Pre)
    (hthree : ThreeForkSuccess fun q => (attempt q).output.isSome) :
    ∃ q₂ c₂ rest seen,
      (nextForkChallenge attempt [first] order).output = some ((q₂, c₂), (rest, seen)) ∧
        (nextForkChallenge attempt seen rest).output.isSome :=
  nextForkChallenge_two_more attempt order hcomplete first hthree

/-- The `hcomplete` premise above is discharged upstream-side by the uniform tape. -/
theorem pre_tape_complete {d : ℕ} (tape : RecursiveForkTape Pre d) : tape.toCoins.Complete :=
  RecursiveForkTape.toCoins_complete tape

/-! ## 4. The upstream escape set is three points, so it costs `3 / 2 ^ 128` per round. -/

theorem pre_escape_measure_le (good : Pre → Prop) :
    (PMF.uniformOfFintype Pre).toOuterMeasure (recursiveForkEscape good)
      ≤ 3 / (2 ^ 128 : ℝ≥0∞) := by
  obtain ⟨a, b, hsub⟩ := recursiveForkEscape_subset_triple good
  have h := uniformOfFintype_toOuterMeasure_triple_le (α := Pre) hsub
  rw [card_pre] at h
  exact le_trans h (le_of_eq (by norm_num))

/-! ## 5. The counting layer takes the alphabet as a bare finite type.

`escapesDuringC_measure_le'` (OracleComp.lean:728) binds `{T F} [Fintype T] [DecidableEq T]
[Fintype F] [Nonempty F]`: that `F` is the oracle codomain, and it is not a field. -/

example {T : Type} [Fintype T] [DecidableEq T] {α : Type}
    (esc : T → (T → Pre) → Set Pre)
    (hblind : ∀ (t : T) (O : T → Pre) (v : Pre), esc t (Function.update O t v) = esc t O)
    {A : OracleComp T Pre α} {Q : ℕ} (hQ : A.QueryBound Q)
    (hesc : ∀ t O, (PMF.uniformOfFintype Pre).toOuterMeasure (esc t O)
      ≤ 3 / (2 ^ 128 : ℝ≥0∞)) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure {O : T → Pre | A.escapesDuringC esc O}
      ≤ Q * (3 / (2 ^ 128 : ℝ≥0∞)) :=
  escapesDuringC_measure_le' esc hblind hesc hQ

/-! ## 6. THE HEADLINE: the endpoint bound shape, at arbitrary `m`, from upstream names only.

`good t O q` is the per-round "the reprogrammed candidate extracts" predicate — the only thing we
write. `hforce` is the escape-or-extract dichotomy our fork recursion supplies
(`kimchiExtract_isSome_of_not_escape_of_stableBase`). Note where `m` does and does not appear: the
pre-IPA reads enter `fsWinsFull` and cost nothing in the bound, because only the `N` forked prefixes
are completed. This is the exact shape of `kimchiExtract_failure_measure_le` with the escape layer
replaced by upstream's. -/

theorem shared_failure_measure_le {T Pf : Type*} [Fintype T] [DecidableEq T] {m N Q : ℕ}
    (A : OracleComp T Pre Pf) (accept : Pf → (Fin m → Pre) → (Fin N → Pre) → Prop)
    (prefixesPre : Pf → Fin m → T) (prefixes : Pf → Fin N → T)
    (good : T → (T → Pre) → Pre → Prop)
    (hgood : ∀ (t : T) (O : T → Pre) (v : Pre), good t (Function.update O t v) = good t O)
    (extracts : (T → Pre) → Prop)
    (hforce : ∀ O, fsWinsFull A accept prefixesPre prefixes O → ¬ extracts O →
      ∃ j : Fin N, O (prefixes (A.run O) j)
        ∈ recursiveForkEscape (good (prefixes (A.run O) j) O))
    (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → Pre)).toOuterMeasure
        {O | fsWinsFull A accept prefixesPre prefixes O ∧ ¬ extracts O}
      ≤ ((Q + N : ℕ) : ℝ≥0∞) * (3 / (2 ^ 128 : ℝ≥0∞)) := by
  set esc : T → (T → Pre) → Set Pre := fun t O => recursiveForkEscape (good t O) with hesc
  have hblind : ∀ (t : T) (O : T → Pre) (v : Pre), esc t (Function.update O t v) = esc t O := by
    intro t O v; simp only [hesc, hgood]
  have hsub : {O : T → Pre | fsWinsFull A accept prefixesPre prefixes O ∧ ¬ extracts O}
      ⊆ {O : T → Pre | (A.completing prefixes).escapesDuringC esc O} := by
    rintro O ⟨hwin, hfail⟩
    obtain ⟨j, hj⟩ := hforce O hwin hfail
    exact OracleComp.escapesDuringC_completing esc prefixes hj
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  exact escapesDuringC_measure_le' esc hblind (fun t O => pre_escape_measure_le _)
    (OracleComp.queryBound_completing prefixes hQ)

/-! ## 7. Why one game serves both stacks: the frozen `Wins` IS `fsWinsFull` at `m = 0`.

No bridging lemma — `Iff.rfl`. So the win condition stays `VerifierAcceptsAt`, the wire verifier,
and widening to `m > 0` for kimchi widens the `accept` slot rather than restating the game. -/

example {F G T Pf : Type} [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (expand : Pre → F)
    (proofOf : Pf → OpeningProof F G σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (A : OracleComp T Pre Pf) (O : T → Pre) :
    Wins σ b v P expand proofOf prefixes O (A.run O)
      ↔ fsWinsFull A
          (fun p _ν (χ : Fin (σ.k + 1) → Pre) =>
            VerifierAcceptsAt σ (proofOf p) P
              (Bulletproof.innerProduct
                (bPolyCoefficients fun i : Fin σ.k => expand (χ i.castSucc)) b)
              v (expand (χ (Fin.last σ.k))) (fun i : Fin σ.k => expand (χ i.castSucc)))
          (fun _ => Fin.elim0) prefixes O :=
  Iff.rfl

/-! ## 8. The coin-tree traversal carries no instance binders at all.

`Recursive.lean`'s section line (:1057) binds `[Field F]`, but Lean includes a section variable in
a `def` only by use, and these defs never touch the algebra — the `omit` at :1072 is for the
adjacent theorem. Instantiating them at an alphabet with no algebra, not even `DecidableEq`, is
what licenses `Game.lean` to *consume* `RecursiveForkReached`, `recursiveForkReached_child` and
`RecursiveRunHistory` directly rather than re-state them — which is what its "Reached tape nodes"
and run-history preambles say it does. -/

structure Bare where
  /-- Any payload at all: this alphabet deliberately has no algebraic structure. -/
  val : Fin 5

example (T P : Type) (k d m : ℕ) (hmk : m + (d + 1) = k) (pfx : P → Fin k → T)
    (root : RecursiveForkCoins Bare k) (O : T → Bare) (p : P) (order : List Bare)
    (child : Bare → RecursiveForkCoins Bare d)
    (hreach : RecursiveForkReached k pfx root m hmk O p (.node order child)) :
    RecursiveForkReached k pfx root (m + 1) (by omega) O p (child (O (pfx p ⟨m, by omega⟩))) :=
  recursiveForkReached_child k pfx root hmk O p order child hreach

example (T P : Type) (k m : ℕ) (h : m ≤ k) (pfx : P → Fin k → T) (O : T → Bare) (p : P)
    (hist : Fin m → T × Bare) : Prop :=
  RecursiveRunHistory k m h pfx O p hist

/-! ## 9. The rank / marginalization / scan-bound / tape layer is alphabet-generic too.

The layer O-1b's *conditional* average-run bound is built on. Upstream states all of it under
`variable {F : Type*} [DecidableEq F]`, adding `[Zero F]` where the scanner appears and
`[Fintype F]` where a cardinality does — **no `Field`, no `AddCommGroup`, no `Module`** — so each
declaration below instantiates at the prechallenge alphabet by a literal `exact`.

That is the evidence for the shape of the O-1b port: only §`NodeBound` (`ExpectedRuns.lean:426–568`)
and §`SpreadTheorem` (`:583–910`) mention `recursiveAlgebraicForkFrom`, so only those two must be
restated for *our* recursion (`kimchiForkFrom`, which differs in its depth indexing and in doing
real work at the leaf). Both now are: `kimchiForkFrom_node_runs_le` /
`kimchiForkFrom_leaf_runs_le` for §`NodeBound`, and `kimchiForkFrom_sum_runs_le_of_forkSpread` with
its root corollary `kimchiExtractRuns_sum_le_of_forkSpread` for §`SpreadTheorem`. Everything below
`:426` is instantiated, not ported. A failure in this section
means that reuse claim no longer holds and the corresponding block of `Game.lean` has become a
forced port. -/

/-- A challenge's zero-based rank in a sampling order (`ExpectedRuns.lean:18`). -/
example (order : Fin (Fintype.card Pre) ≃ Pre) (A : Finset Pre) (q : Pre) : ℕ :=
  scanRank order A q

/-- At most `j` members of `A` have rank below `j` (`ExpectedRuns.lean:39`). -/
theorem pre_card_filter_scanRank_lt_le (order : Fin (Fintype.card Pre) ≃ Pre) (A : Finset Pre)
    (j : ℕ) :
    (A.filter (fun q => scanRank order A q < j)).card ≤ j :=
  card_filter_scanRank_lt_le order A j

open Classical in
/-- A member of `A` has rank below `j` in at most a `j/|A|` fraction of the sampling orders
(`ExpectedRuns.lean:139`). This is the counting step that turns "twice the rank-`< 2` candidates"
into a `1/|good set|` density, and it is the one that makes the `6` land. -/
theorem pre_card_scanRank_lt_mul_le (A : Finset Pre) {q : Pre} (hq : q ∈ A) (j : ℕ) :
    A.card * (Finset.univ.filter
        (fun order : Fin (Fintype.card Pre) ≃ Pre => scanRank order A q < j)).card
      ≤ j * Fintype.card (Fin (Fintype.card Pre) ≃ Pre) :=
  card_scanRank_lt_mul_le A hq j

/-- Marginalizing one coordinate of a finite function space (`ExpectedRuns.lean:164`). Used to
factor a sum over child tapes into `|tapes|^(N-1)` copies of a sum over one child
(here at `α := Pre`, the alphabet indexing a node's children). -/
theorem pre_sum_eval_pi {β : Type*} [Fintype β] (q : Pre) (g : β → ℕ) :
    ∑ f : Pre → β, g (f q) = Fintype.card β ^ (Fintype.card Pre - 1) * ∑ b : β, g b :=
  sum_eval_pi q g

open Classical in
/-- A scan pays only candidates preceded by fewer than two good challenges
(`ExpectedRuns.lean:368`) — the pointwise ingredient of both of O-1b's per-row bounds. -/
theorem pre_nextForkChallenge_runs_le_rank_sum {α : Type*}
    (attempt : Pre → RecursiveForkAttempt α) (order : Fin (Fintype.card Pre) ≃ Pre)
    (M : Finset Pre) (hM : ∀ q ∈ M, q ≠ 0 ∧ (attempt q).output.isSome)
    (seen l₀ l' : List Pre) (hdec : List.ofFn (⇑order) = l₀ ++ l')
    (hMseen : ∀ q ∈ M, q ∈ seen → q ∈ l₀)
    (hMl₀ : (M.filter (· ∈ l₀)).card ≤ 1) :
    (nextForkChallenge attempt seen l').runs
      ≤ ∑ q ∈ Finset.univ.filter (fun q : Pre => scanRank order (insert q M) q < 2),
          (attempt q).runs :=
  nextForkChallenge_runs_le_rank_sum attempt order M hM seen l₀ l' hdec hMseen hMl₀

/-! The uniform tape (`Recursive.lean:23`) and its coin erasure. `orderList` is definitionally
`List.ofFn`, which is what lets a tape node be handed straight to the rank lemmas above; and
`equivSucc` is what turns a depth-`d+1` tape sum into a sum over `(order, children)` pairs. -/

/-- The tape space at the prechallenge alphabet is finite and inhabited (`Recursive.lean:23`). -/
example (d : ℕ) : Fintype (RecursiveForkTape Pre d) := inferInstance

/-- A tape node's sampling order erases to `List.ofFn` on the nose (`Recursive.lean:32`, `:37`). -/
theorem pre_toCoins_node {d : ℕ} (order : Fin (Fintype.card Pre) ≃ Pre)
    (child : Pre → RecursiveForkTape Pre d) :
    (RecursiveForkTape.node order child).toCoins
      = .node (List.ofFn (⇑order)) (fun q => (child q).toCoins) :=
  rfl

/-- A positive-depth tape is one order and one child tape per challenge (`Recursive.lean:63`), so
its cardinality factors — the shape every depth-`d+1` tape sum is transported along. -/
theorem pre_card_tape_succ (d : ℕ) :
    Fintype.card (RecursiveForkTape Pre (d + 1))
      = Fintype.card (Fin (Fintype.card Pre) ≃ Pre)
          * Fintype.card (RecursiveForkTape Pre d) ^ Fintype.card Pre := by
  have h := Fintype.card_congr (RecursiveForkTape.equivSucc (F := Pre) d)
  rwa [Fintype.card_prod, Fintype.card_fun] at h

end Bulletproof.Forking.IronwoodGeneric
