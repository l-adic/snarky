import Snarky.Kimchi.Backend.Direct

/-!
# The wired fragment

The source constraints whose lowering wires: any `Basic` constraint over affine operands, and
a complete addition whose operands in the unwired columns are bare variables. Their reduction
allocates intermediates, pins constants through the cache and fuses classes, so the union-find,
the constant cache and the generic queue all move; the direct fragment is the special case in
which none of them does.

A satisfying table determines a valuation by class: a variable reads the value in any cell of
its root's class, the permutation forcing those cells to agree. A fusion the log records, a
merge or a cache hit, then holds by construction once its two variables share a root at the end
of the lowering, and a cache hit's constant is pinned by the row some step emitted for it.

## Main definitions

- `CVar.termVars`, `KimchiConstraint.termVars`: the variables an operand's affine form names,
  with repetition.
- `KimchiConstraint.Wired`, `KimchiConstraint.Wired.Scoped`: membership in the fragment, and
  the scoping condition on a source list, its public variables and the counter: every
  constraint wired, every named variable below the counter, and every operand of an unwired
  column occurring once.

## Main results

- `fusion_root_eq`: every fusion any step of the lowering logs shares a root in the roots the
  assembly wires through.
- `pinned_of_cached`: every cache hit any step logs names a pin some step logs.

## Implementation notes

The fold over the recorded steps threads the union-find invariant of `Snarky.Kimchi.UnionFind`
from the empty structure, each step's effect being the replay of its own faithful log; the
cache fold starts from the empty cache, so a hit's constant is never inherited.
-/

open Kimchi

namespace Snarky

variable {F : Type}

section Fragment

variable [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]

/-- The variables an operand's affine form names, in term order. -/
def CVar.termVars (x : CVar F) : List Variable :=
  x.reduceToAffineExpression.terms.map Prod.fst

namespace Kimchi

/-- The variables a constraint's operands name, with repetition: every term of every affine
operand. -/
def KimchiConstraint.termVars : KimchiConstraint F → List Variable
  | .basic (.r1cs a b c) => a.termVars ++ b.termVars ++ c.termVars
  | .basic (.equal a b) => a.termVars ++ b.termVars
  | .basic (.square a b) => a.termVars ++ b.termVars
  | .basic (.boolean x) => x.termVars
  | .addComplete c => c.operands.toList.flatMap CVar.termVars
  | _ => []

/-- A constraint the lowering wires: any `Basic` constraint, or a complete addition whose
operands in the unwired columns `7` to `10` are bare variables. -/
def KimchiConstraint.Wired : KimchiConstraint F → Prop
  | .basic _ => True
  | .addComplete c => ∀ x ∈ c.operands.toList.drop permCols, x.var?.isSome
  | _ => False

instance KimchiConstraint.decidableWired (c : KimchiConstraint F) : Decidable c.Wired := by
  unfold KimchiConstraint.Wired
  split <;> infer_instance

/-- Every variable the source and the public variables name, with repetition. -/
private def occurrences (source : List (KimchiConstraint F)) (publicVars : List Variable) :
    List Variable :=
  source.flatMap KimchiConstraint.termVars ++ publicVars

/-- The scoping condition under which any table satisfying the fragment's index determines
a valuation: every constraint is wired, every named variable is below the counter, and every
operand of an unwired column occurs exactly once among the term occurrences and the public
variables. -/
structure KimchiConstraint.Wired.Scoped (nv : Variable) (source : List (KimchiConstraint F))
    (publicVars : List Variable) : Prop where
  /-- Every constraint is in the fragment. -/
  wired : ∀ c ∈ source, c.Wired
  /-- Every variable the source or the public input names is below the counter. -/
  below : ∀ v ∈ occurrences source publicVars, v < nv
  /-- Every operand of an unwired column occurs exactly once among the term occurrences and
  the public variables. -/
  unwiredOnce : ∀ c ∈ source, ∀ v ∈ c.unwiredVars, (occurrences source publicVars).count v = 1

instance (nv : Variable) (source : List (KimchiConstraint F)) (publicVars : List Variable) :
    Decidable (KimchiConstraint.Wired.Scoped nv source publicVars) :=
  decidable_of_iff
    ((∀ c ∈ source, c.Wired) ∧ (∀ v ∈ occurrences source publicVars, v < nv) ∧
      ∀ c ∈ source, ∀ v ∈ c.unwiredVars, (occurrences source publicVars).count v = 1)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

end Kimchi

end Fragment

namespace Kimchi

variable [Field F] [DecidableEq F]

/-! ## The classes and the cache at the end of the lowering -/

/-- Along the recorded fold from an invariant union-find: the invariant holds at the end, no
class splits, and every fusion any step logs is one class at the end. -/
private theorem recordGates_classes (source : List (KimchiConstraint F)) (nv : Variable)
    (aux : AuxState F) (hinv : UnionFind.Inv aux.wireState.unionFind) :
    UnionFind.Inv (recordGates source nv aux).aux.wireState.unionFind ∧
      (∀ v w, aux.wireState.unionFind.Same v w →
        (recordGates source nv aux).aux.wireState.unionFind.Same v w) ∧
      ∀ s ∈ (recordGates source nv aux).steps, ∀ p ∈ fusions s.events,
        (recordGates source nv aux).aux.wireState.unionFind.Same p.1 p.2 := by
  induction source generalizing nv aux with
  | nil => exact ⟨hinv, fun _ _ h => h, fun _ h => (List.not_mem_nil h).elim⟩
  | cons con cons ih =>
    have hrep : (recordReduction nv aux con.reduce).aux =
        (replay ⟨[], nv, aux⟩ (recordReduction nv aux con.reduce).events).aux := by
      show (recordReduction nv aux con.reduce).finish.aux = _
      exact congrArg BuilderReductionState.aux (record_constraint_replays nv aux con)
    have hdec := record_constraint_decides nv aux con
    have hinv' : UnionFind.Inv (recordReduction nv aux con.reduce).aux.wireState.unionFind := by
      rw [hrep]
      exact inv_replay hinv hdec
    obtain ⟨ih1, ih2, ih3⟩ := ih (recordReduction nv aux con.reduce).nextVariable
      (recordReduction nv aux con.reduce).aux hinv'
    refine ⟨ih1, fun v w h => ih2 v w ?_, fun s hs p hp => ?_⟩
    · rw [hrep]
      exact same_replay_mono hinv hdec h
    · rcases List.mem_cons.mp hs with rfl | hs
      · refine ih2 p.1 p.2 ?_
        rw [hrep]
        exact same_replay hinv hdec hp
      · exact ih3 s hs p hp

/-- Every fusion any step of the lowering logs shares a root in the roots the assembly wires
through. -/
theorem fusion_root_eq (source : List (KimchiConstraint F)) (nv : Variable)
    {s : RecordedStep F} (hs : s ∈ (lowering source nv).steps) {p : Variable × Variable}
    (hp : p ∈ fusions s.events) :
    (directRoots source nv).getD p.1 p.1 = (directRoots source nv).getD p.2 p.2 := by
  obtain ⟨hinv, -, hsame⟩ :=
    recordGates_classes source nv initialAuxState UnionFind.empty_inv
  rw [directRoots_eq, UnionFind.rootOf_getD_eq hinv, UnionFind.rootOf_getD_eq hinv]
  exact hsame s hs p hp

/-- Along the recorded fold: every cache hit any step logs names a pin some step logs, or a
pair of the starting cache. -/
private theorem recordGates_cache (source : List (KimchiConstraint F)) (nv : Variable)
    (aux : AuxState F) :
    ∀ s ∈ (recordGates source nv aux).steps, ∀ {c : EqualsConstraint F} {l v : Variable} {k : F},
      ReductionEvent.equal c (.cached l v k) ∈ s.events →
        (∃ s' ∈ (recordGates source nv aux).steps, ∃ c' g,
          ReductionEvent.equal c' (.pinned v k g) ∈ s'.events) ∨
        (k, v) ∈ aux.wireState.cachedConstants := by
  induction source generalizing nv aux with
  | nil => exact fun _ hs => (List.not_mem_nil hs).elim
  | cons con cons ih =>
    intro s hs c l v k he
    have hrep : (recordReduction nv aux con.reduce).aux =
        (replay ⟨[], nv, aux⟩ (recordReduction nv aux con.reduce).events).aux := by
      show (recordReduction nv aux con.reduce).finish.aux = _
      exact congrArg BuilderReductionState.aux (record_constraint_replays nv aux con)
    have hdec := record_constraint_decides nv aux con
    have hcache : (recordReduction nv aux con.reduce).aux.wireState.cachedConstants =
        pinsOf (recordReduction nv aux con.reduce).events ++ aux.wireState.cachedConstants := by
      rw [hrep]
      exact cache_replay hdec
    rcases List.mem_cons.mp hs with rfl | hs
    · rcases cached_mem hdec he with h | h
      · obtain ⟨c', g, hg⟩ := mem_pinsOf h
        exact Or.inl ⟨_, List.mem_cons_self .., c', g, hg⟩
      · exact Or.inr h
    · rcases ih (recordReduction nv aux con.reduce).nextVariable
        (recordReduction nv aux con.reduce).aux s hs he with ⟨s', hs', c', g, hg⟩ | h
      · exact Or.inl ⟨s', List.mem_cons_of_mem _ hs', c', g, hg⟩
      · rw [hcache] at h
        rcases List.mem_append.mp h with h | h
        · obtain ⟨c', g, hg⟩ := mem_pinsOf h
          exact Or.inl ⟨_, List.mem_cons_self .., c', g, hg⟩
        · exact Or.inr h

/-- Every cache hit any step of the lowering logs names a pin some step logs: the lowering
starts from the empty cache. -/
theorem pinned_of_cached (source : List (KimchiConstraint F)) (nv : Variable)
    {s : RecordedStep F} (hs : s ∈ (lowering source nv).steps) {c : EqualsConstraint F}
    {l v : Variable} {k : F} (he : ReductionEvent.equal c (.cached l v k) ∈ s.events) :
    ∃ s' ∈ (lowering source nv).steps, ∃ c' g,
      ReductionEvent.equal c' (.pinned v k g) ∈ s'.events := by
  rcases recordGates_cache source nv initialAuxState s hs he with h | h
  · exact h
  · exact (List.not_mem_nil h).elim

/-! ## The valuation -/

/-- The value at a cell of the variable's class, else at the variable's own cell, else `0`.
The class is keyed by the variable's root, so fused variables read alike; a variable outside
every class, an unwired operand, reads its one cell. -/
private noncomputable def recoverClass (roots : Array Variable) (rows : List (KimchiRow F))
    (val : Nat × Nat → F) (v : Variable) : F :=
  match classCells roots rows (roots.getD v v) with
  | c :: _ => val c
  | [] => recover rows val v

omit [DecidableEq F] in
/-- Every labelled cell reads its variable's recovered value, when the cells of a class agree
and an unwired label is outside every class and unique. -/
private theorem recoverClass_spec (roots : Array Variable) (rows : List (KimchiRow F))
    (val : Nat × Nat → F)
    (hclass : ∀ k, ∀ c ∈ classCells roots rows k, ∀ c' ∈ classCells roots rows k, val c = val c')
    (huniq : ∀ (r j : Nat) (hr : r < rows.length) (hj : j < wCols) (v : Variable), 7 ≤ j →
      rows[r].vars[j] = some v → classCells roots rows (roots.getD v v) = [] ∧
        ∀ (r' j' : Nat) (hr' : r' < rows.length) (hj' : j' < wCols),
          rows[r'].vars[j'] = some v → r' = r ∧ j' = j)
    (r j : Nat) (hr : r < rows.length) (hj : j < wCols) (v : Variable)
    (hv : rows[r].vars[j] = some v) : val (r, j) = recoverClass roots rows val v := by
  unfold recoverClass
  rcases hcs : classCells roots rows (roots.getD v v) with _ | ⟨c, cs⟩
  · simp only
    by_cases h7 : j < 7
    · have hmem := mem_classCells_of_label (roots := roots) hr h7 hv
      rw [hcs] at hmem
      exact (List.not_mem_nil hmem).elim
    · obtain ⟨-, huniq'⟩ := huniq r j hr hj v (Nat.le_of_not_lt h7) hv
      have hex : ∃ c : Fin rows.length × Fin wCols, rows[c.1].vars[c.2] = some v :=
        ⟨(⟨r, hr⟩, ⟨j, hj⟩), hv⟩
      simp only [recover, dif_pos hex]
      have hc := Classical.choose_spec hex
      generalize Classical.choose hex = c at hc ⊢
      obtain ⟨h1, h2⟩ := huniq' c.1 c.2 c.1.isLt c.2.isLt hc
      rw [h1, h2]
  · simp only
    by_cases h7 : j < 7
    · refine hclass _ _ (mem_classCells_of_label hr h7 hv) c ?_
      rw [hcs]
      exact List.mem_cons_self ..
    · obtain ⟨hempty, -⟩ := huniq r j hr hj v (Nat.le_of_not_lt h7) hv
      rw [hcs] at hempty
      cases hempty

omit [DecidableEq F] in
/-- Two variables with one root read alike, when neither labels an unwired cell. -/
private theorem recoverClass_eq_of_root_eq (roots : Array Variable) (rows : List (KimchiRow F))
    (val : Nat × Nat → F) {v w : Variable} (hroot : roots.getD v v = roots.getD w w)
    (hv : ∀ (r j : Nat) (hr : r < rows.length) (hj : j < wCols), rows[r].vars[j] = some v →
      j < 7)
    (hw : ∀ (r j : Nat) (hr : r < rows.length) (hj : j < wCols), rows[r].vars[j] = some w →
      j < 7) :
    recoverClass roots rows val v = recoverClass roots rows val w := by
  unfold recoverClass
  rw [hroot]
  rcases hcs : classCells roots rows (roots.getD w w) with _ | ⟨c, cs⟩
  · simp only
    have hnv : ¬ ∃ c : Fin rows.length × Fin wCols, rows[c.1].vars[c.2] = some v := by
      rintro ⟨c, hc⟩
      have hmem :=
        mem_classCells_of_label (roots := roots) c.1.isLt (hv c.1 c.2 c.1.isLt c.2.isLt hc) hc
      rw [hroot, hcs] at hmem
      exact List.not_mem_nil hmem
    have hnw : ¬ ∃ c : Fin rows.length × Fin wCols, rows[c.1].vars[c.2] = some w := by
      rintro ⟨c, hc⟩
      have hmem :=
        mem_classCells_of_label (roots := roots) c.1.isLt (hw c.1 c.2 c.1.isLt c.2.isLt hc) hc
      rw [hcs] at hmem
      exact List.not_mem_nil hmem
    simp only [recover, dif_neg hnv, dif_neg hnw]
  · rfl

end Kimchi

end Snarky
