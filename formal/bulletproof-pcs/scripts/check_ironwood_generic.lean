import Bulletproof.Forking.Game

/-!
# The reuse seam: our fork game IS ironwood's, at a prechallenge alphabet

`Forking/Game.lean` proves its escape and counting layer over an abstract `variable {T Pre Pf}`
(Game.lean:114) — an alphabet with no instances at all. This file records what the *deployed*
alphabet buys: `Fin (2 ^ 128)` carries `Zero`, `DecidableEq`, `Fintype` and `Nonempty`, and with
those, ironwood's own scanner, escape set, counting bound and coin-tree traversal apply by literal
`exact`. So the corresponding blocks of `Game.lean` are duplicates of upstream, not forced ports.

Two further facts are pinned here because the whole abstraction rests on them:

* the frozen `Wins` (Game.lean:129) *is* `Zcash.Snark.fsWinsFull` (Adaptive.lean:30) at `m = 0`,
  by `Iff.rfl` — so one game statement serves bare IPA (`m = 0`) and kimchi (`m > 0`), and the win
  condition stays `VerifierAcceptsAt`, the wire verifier, with no bridging lemma;
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

Literal instantiations of the upstream names that Game.lean:248/373/518 re-prove. -/

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
write. `hforce` is the escape-or-extract dichotomy our fork recursion supplies (Game.lean:950).
Note where `m` does and does not appear: the pre-IPA reads enter `fsWinsFull` and cost nothing in
the bound, because only the `N` forked prefixes are completed. This is the exact shape of
`kimchiExtract_failure_measure_le` (Game.lean:1447) with the escape layer replaced by upstream's. -/

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
adjacent theorem. Instantiating them at an alphabet with no algebra, not even `DecidableEq`, shows
Game.lean:612/623/1052 are duplicates rather than forced ports. -/

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

end Bulletproof.Forking.IronwoodGeneric
