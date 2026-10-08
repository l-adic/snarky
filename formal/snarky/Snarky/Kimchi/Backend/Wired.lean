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
of the lowering, and a cache hit's constant is pinned by the row some step emitted for it. An
operand of an unwired column is outside the permutation, so it reads its one cell instead: its
only occurrence in the source is that bare operand, which logs nothing, so no event names it
and no other cell carries it.

## Main definitions

- `KimchiConstraint.Wired`, `KimchiConstraint.Wired.Scoped`: membership in the fragment, and
  the scoping condition on a source list, its public variables and the counter: every
  constraint wired, every named variable below the counter, and every operand of an unwired
  column occurring once.

## Main results

- `fusion_root_eq`: every fusion any step of the lowering logs shares a root in the roots the
  assembly wires through.
- `pinned_of_cached`: every cache hit any step logs names a pin some step logs.
- `unwired_not_named`, `unwired_of_cell`, `unwired_cell_unique`: an operand of an unwired
  column is named by no event, every cell of an unwired column carries such an operand, and
  such an operand labels one cell only.
- `KimchiConstraint.Wired.holds_of_satisfies`: any table satisfying an index of the
  fragment's lowering yields a valuation satisfying every source constraint and reading the
  public variables as the public input.

## Implementation notes

The folds over the recorded steps thread the union-find invariant of `Snarky.Kimchi.UnionFind`
from the empty structure and the queue invariant from the empty queue, each step's effect being
the replay of its own faithful log; the cache fold starts from the empty cache, so a hit's
constant is never inherited. Provenance is membership only: the names of a step's events are
terms of its operands or its allocations, by `basic_names` and `addComplete_names`, and an
unwired operand's one occurrence is a bare operand, so a second naming would be a second
occurrence.
-/

open Kimchi

namespace Snarky.Kimchi

open Snarky

variable {F : Type}

section Fragment

variable [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]

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

end Fragment

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

/-! ## Where the rows come from -/

/-- Replaying faithful events whose queued equations have the property, from a queue with it:
every new row packs two such equations, and the queue keeps it. -/
private theorem replay_queued (P : GenericPlonkConstraint F → Prop) :
    ∀ (es : List (ReductionEvent F)) (s : BuilderReductionState F), OutcomesFaithful s es →
      (∀ e ∈ es, ∀ g, e.queued? = some g → P g) → QueueFrom P s.aux →
      (∀ row ∈ (replay s es).constraints,
        row ∈ s.constraints ∨ ∃ q g, P q ∧ P g ∧ row = emitDoubleGateRow q g) ∧
      QueueFrom P (replay s es).aux
  | [], _, _, _, hq => ⟨fun _ h => Or.inl h, hq⟩
  | e :: es, s, hf, hes, hq => by
    obtain ⟨hf1, hf2⟩ := outcomesFaithful_cons hf
    obtain ⟨h1, h2⟩ := replayEvent_queue s e hf1
    have hstep : replay s (e :: es) = replay (replayEvent s e) es := rfl
    rw [hstep]
    have hes' := fun e' he' => hes e' (List.mem_cons_of_mem _ he')
    cases hqe : e.queued? with
    | none =>
      simp only [hqe] at h1 h2
      obtain ⟨r1, r2⟩ := replay_queued P es (replayEvent s e) hf2 hes'
        (fun g' hg' => hq g' (h1 ▸ hg'))
      refine ⟨fun row hrow => ?_, r2⟩
      rcases r1 row hrow with h | h
      · rw [h2] at h
        exact Or.inl h
      · exact Or.inr h
    | some g =>
      have hg := hes e (List.mem_cons_self ..) g hqe
      cases hqs : s.aux.queuedGenericGate with
      | none =>
        simp only [hqe, hqs] at h1 h2
        obtain ⟨r1, r2⟩ := replay_queued P es (replayEvent s e) hf2 hes' fun g' hg' => by
          rw [h1, Option.some.injEq] at hg'
          exact hg' ▸ hg
        refine ⟨fun row hrow => ?_, r2⟩
        rcases r1 row hrow with h | h
        · rw [h2] at h
          exact Or.inl h
        · exact Or.inr h
      | some q =>
        simp only [hqe, hqs] at h1 h2
        obtain ⟨r1, r2⟩ := replay_queued P es (replayEvent s e) hf2 hes' fun _ h => by
          rw [h1] at h
          cases h
        refine ⟨fun row hrow => ?_, r2⟩
        rcases r1 row hrow with h | h
        · rw [h2] at h
          rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr ⟨q, g, hq q hqs, hg, rfl⟩
          · exact Or.inl h
        · exact Or.inr h

/-- A constraint's recorded reduction from a queue with the property, when every equation its
events queue has it: every flushed row packs two such equations, the queue handed back keeps
it, and the counter does not decrease. -/
private theorem record_rows_queued (P : GenericPlonkConstraint F → Prop)
    {c : KimchiConstraint F} (nv : Variable) (aux : AuxState F)
    (hP : ∀ e ∈ (recordReduction nv aux c.reduce).events, ∀ g, e.queued? = some g → P g)
    (hq : QueueFrom P aux) :
    (∀ r ∈ (recordReduction nv aux c.reduce).rows,
      ∃ q g, P q ∧ P g ∧ r.row = emitDoubleGateRow q g) ∧
    QueueFrom P (recordReduction nv aux c.reduce).aux ∧
    nv ≤ (recordReduction nv aux c.reduce).nextVariable := by
  have hrep := record_constraint_replays nv aux c
  obtain ⟨h1, h2⟩ := replay_queued P _ ⟨[], nv, aux⟩ (record_constraint_decides nv aux c) hP hq
  have h3 := (allocs_ge (record_constraint_allocates nv aux c)).2
  rw [← hrep] at h1 h2 h3
  simp only [RecordedReduction.finish] at h1 h2 h3
  refine ⟨fun r hr => ?_, h2, h3⟩
  rcases h1 r.row (by simp only [List.mem_reverse, List.mem_map]; exact ⟨r, hr, rfl⟩) with h | h
  · exact (List.not_mem_nil h).elim
  · exact h

/-- The recorded fold from a queue with the property and a counter at or above a bound, when
every equation any step queues from such a counter has it: each step is one constraint's
recording from a queue with the property and a counter at or above the bound, and the queue
handed back keeps it. -/
private theorem recordGates_queued (P : GenericPlonkConstraint F → Prop)
    (source : List (KimchiConstraint F)) (nv₀ : Variable)
    (hP : ∀ c ∈ source, ∀ nv aux, nv₀ ≤ nv →
      ∀ e ∈ (recordReduction nv aux c.reduce).events, ∀ g, e.queued? = some g → P g) :
    ∀ nv aux, nv₀ ≤ nv → QueueFrom P aux →
      (∀ p (hp : p < source.length), ∃ nv' aux', nv₀ ≤ nv' ∧ QueueFrom P aux' ∧
        (recordGates source nv aux).steps[p]'((length_steps source nv aux).symm ▸ hp) =
          ⟨(recordReduction nv' aux' source[p].reduce).rows,
            (recordReduction nv' aux' source[p].reduce).result,
            (recordReduction nv' aux' source[p].reduce).events⟩) ∧
      QueueFrom P (recordGates source nv aux).aux := by
  induction source with
  | nil => exact fun nv aux _ hq => ⟨fun p hp => absurd hp (Nat.not_lt_zero _), hq⟩
  | cons con cons ih =>
    intro nv aux hnv hq
    have hP' := fun c hc => hP c (List.mem_cons_of_mem _ hc)
    obtain ⟨-, hq', hnv'⟩ :=
      record_rows_queued P nv aux (hP con (List.mem_cons_self ..) nv aux hnv) hq
    obtain ⟨ih1, ih2⟩ := ih hP' _ _ (Nat.le_trans hnv hnv') hq'
    refine ⟨fun p hp => ?_, ih2⟩
    cases p with
    | zero => exact ⟨nv, aux, hnv, hq, rfl⟩
    | succ p =>
      obtain ⟨nv', aux', hnv'', hq'', hstep⟩ := ih1 p (Nat.lt_of_succ_lt_succ hp)
      exact ⟨nv', aux', hnv'', hq'', hstep⟩

/-- Where each row of the lowering comes from: a public row, a packed pair of queued equations
with the property, the flushed equation with it, or a complete addition's row at its step's gate
span, recorded from a counter at or above the start. -/
private theorem wiredRows_cases (P : GenericPlonkConstraint F → Prop)
    {source : List (KimchiConstraint F)} {publicVars : List Variable} {nv : Variable}
    (hw : ∀ c ∈ source, c.Wired)
    (hP : ∀ c ∈ source, ∀ nv' aux, nv ≤ nv' →
      ∀ e ∈ (recordReduction nv' aux c.reduce).events, ∀ g, e.queued? = some g → P g)
    (r : Nat) (hr : r < (directRows source publicVars nv).length) :
    (∃ (h : r < publicVars.length), (directRows source publicVars nv)[r] =
        (makePublicInputRows (F := F) publicVars)[r]'(by simpa [makePublicInputRows] using h)) ∨
    (∃ q g, P q ∧ P g ∧ (directRows source publicVars nv)[r] = emitDoubleGateRow q g) ∨
    (∃ g, P g ∧ (directRows source publicVars nv)[r] = flushRow g) ∨
    (∃ (p : Nat) (hp : p < source.length) (c : AddComplete F) (nv' : Variable)
      (aux' : AuxState F), nv ≤ nv' ∧ source[p] = .addComplete c ∧
      r = gateRowOf source publicVars nv p hp ∧
      (directRows source publicVars nv)[r] = (recordReduction nv' aux' c.reduce).result.row)
    := by
  have hlen : (makePublicInputRows (F := F) publicVars).length = publicVars.length := by
    simp [makePublicInputRows]
  have hfold := recordGates_queued P source nv hP nv initialAuxState (Nat.le_refl _)
    (fun _ h => by simp [initialAuxState] at h)
  by_cases hpub : r < publicVars.length
  · exact Or.inl ⟨hpub, List.getElem_append_left (hlen ▸ hpub)⟩
  right
  have hk : r - publicVars.length < (lowering source nv).allRows.length := by
    simp only [directRows, List.length_append, hlen] at hr
    omega
  have e : (directRows source publicVars nv)[r] =
      (lowering source nv).allRows[r - publicVars.length] := by
    simp only [directRows]
    rw [List.getElem_append_right (hlen ▸ Nat.le_of_not_lt hpub)]
    simp only [hlen]
  rw [e]
  by_cases hb : r - publicVars.length < (lowering source nv).bodyRows.length
  · have e2 : (lowering source nv).allRows[r - publicVars.length] =
        (lowering source nv).bodyRows[r - publicVars.length] :=
      List.getElem_append_left hb
    rw [e2]
    obtain ⟨i, hi, hc⟩ := bodyRows_placed (lowering source nv) (r - publicVars.length) hb
    have hi' : i < source.length := (length_steps source nv initialAuxState) ▸ hi
    have hip : i < (lowering source nv).placements.length := by
      rw [RecordedGates.length_placements]; exact hi
    obtain ⟨nv', aux', hnv', hq', hstep⟩ := hfold.1 i hi'
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [placements_genericRows_count _ _ hi] at h2
      have h1' : ((lowering source nv).placements[i]'hip).genericRows.first ≤
        r - publicVars.length := h1
      have h2' : r - publicVars.length <
        ((lowering source nv).placements[i]'hip).genericRows.first +
          (lowering source nv).steps[i].rows.length := h2
      have hj : r - publicVars.length - ((lowering source nv).placements[i]'hip).genericRows.first <
        (lowering source nv).steps[i].rows.length := by omega
      have hrow := getElem_bodyRows_generic (lowering source nv) i hi _ hj
        (show ((lowering source nv).placements[i]'hip).genericRows.first +
          (r - publicVars.length - ((lowering source nv).placements[i]'hip).genericRows.first) <
          (lowering source nv).bodyRows.length by omega)
      have eidx : ((lowering source nv).placements[i]'hip).genericRows.first +
          (r - publicVars.length - ((lowering source nv).placements[i]'hip).genericRows.first) =
          r - publicVars.length := by omega
      have hstep' : (lowering source nv).steps[i] =
          ⟨(recordReduction nv' aux' source[i].reduce).rows,
            (recordReduction nv' aux' source[i].reduce).result,
            (recordReduction nv' aux' source[i].reduce).events⟩ := hstep
      rw [(getElem_congr_idx eidx).symm.trans hrow]
      simp only [hstep']
      obtain ⟨hrows, -, -⟩ :=
        record_rows_queued P nv' aux' (hP _ (List.getElem_mem hi') nv' aux' hnv') hq'
      exact hrows _ (List.getElem_mem _)
    · right; right
      rw [placements_customRows_count _ _ hi] at h2
      have h1' : ((lowering source nv).placements[i]'hip).customRows.first ≤
        r - publicVars.length := h1
      have h2' : r - publicVars.length <
        ((lowering source nv).placements[i]'hip).customRows.first +
          (lowering source nv).steps[i].gateRows.length := h2
      have hwd := hw _ (List.getElem_mem hi')
      unfold KimchiConstraint.Wired at hwd
      split at hwd
      · exfalso
        have hgr : (lowering source nv).steps[i].gateRows = [] := by
          rw [hstep, ‹source[i] = _›]
          rfl
        rw [hgr] at h2'
        simp at h2'
        omega
      · obtain ⟨c, hsrc⟩ : ∃ c, source[i] = KimchiConstraint.addComplete c := ⟨_, ‹source[i] = _›⟩
        have hgr : (lowering source nv).steps[i].gateRows =
            [(recordReduction nv' aux' c.reduce).result.row] := by
          rw [hstep, hsrc]
          rfl
        rw [hgr, List.length_singleton] at h2'
        refine ⟨i, hi', c, nv', aux', hnv', hsrc, ?_, ?_⟩
        · show r = publicVars.length + ((lowering source nv).placements[i]'hip).customRows.first
          omega
        · have hrow := getElem_bodyRows_gate (lowering source nv) i hi 0 (by simp [hgr])
            (show ((lowering source nv).placements[i]'hip).customRows.first + 0 <
              (lowering source nv).bodyRows.length by omega)
          have eidx : ((lowering source nv).placements[i]'hip).customRows.first + 0 =
              r - publicVars.length := by omega
          rw [(getElem_congr_idx eidx).symm.trans hrow]
          simp only [hgr, List.getElem_cons_zero]
      · exact hwd.elim
  · right; left
    cases hq : (lowering source nv).aux.queuedGenericGate with
    | none =>
      exfalso
      simp [RecordedGates.allRows, finalizeGateQueue, hq] at hk
      omega
    | some g =>
      refine ⟨g, hfold.2 g hq, ?_⟩
      have e3 : (lowering source nv).allRows = (lowering source nv).bodyRows ++ [flushRow g] := by
        simp only [RecordedGates.allRows, finalizeGateQueue, hq, Option.map_some,
          Option.toList_some]
        rfl
      simp only [e3]
      rw [List.getElem_append_right (Nat.le_of_not_lt hb)]
      simp only [e3, List.length_append, List.length_singleton] at hk
      have : r - publicVars.length - (lowering source nv).bodyRows.length = 0 := by omega
      simp only [this, List.getElem_cons_zero]

omit [Field F] [DecidableEq F] in
/-- A label in a packed row is in its first six cells and is a cell of one of its equations. -/
private theorem label_double' {q g : GenericPlonkConstraint F} (j : Nat) (hj : j < wCols)
    (w : Variable) (h : (emitDoubleGateRow q g).vars[j] = some w) :
    j < 6 ∧ (w ∈ q.vars ∨ w ∈ g.vars) := by
  have h' : ([g.vl, g.vr, g.vo, q.vl, q.vr, q.vo] ++ List.replicate 9 none)[j]'(by
    simpa using hj) = some w := h
  obtain ⟨hj', h''⟩ := label_of_append_replicate (by simpa using hj) h'
  simp only [List.length_cons, List.length_nil] at hj'
  refine ⟨by omega, ?_⟩
  simp only [GenericPlonkConstraint.vars, List.mem_append, Option.mem_toList]
  interval_cases j <;> simp_all

omit [Field F] [DecidableEq F] in
/-- A label in the flushed row is in its first three cells and is a cell of its equation. -/
private theorem label_flush' {g : GenericPlonkConstraint F} (j : Nat) (hj : j < wCols)
    (w : Variable) (h : (flushRow g).vars[j] = some w) : j < 3 ∧ w ∈ g.vars := by
  have h' : ([g.vl, g.vr, g.vo] ++ List.replicate 12 none)[j]'(by simpa using hj) = some w := h
  obtain ⟨hj', h''⟩ := label_of_append_replicate (by simpa using hj) h'
  simp only [List.length_cons, List.length_nil] at hj'
  refine ⟨by omega, ?_⟩
  simp only [GenericPlonkConstraint.vars, List.mem_append, Option.mem_toList]
  interval_cases j <;> simp_all

/-! ## The unwired operands -/

omit [Field F] [DecidableEq F] in
private theorem addComplete_of_unwired {c : KimchiConstraint F} {v : Variable}
    (hv : v ∈ c.unwiredVars) : ∃ c', c = .addComplete c' := by
  cases c with
  | addComplete c' => exact ⟨c', rfl⟩
  | _ => exact (List.not_mem_nil hv).elim

private theorem termVars_var (v : Variable) : (CVar.var v : CVar F).termVars = [v] := rfl

omit [Field F] [DecidableEq F] in
/-- An unwired operand sits at an unwired column as a bare operand. -/
private theorem unwired_index {c : AddComplete F} {v : Variable}
    (hv : v ∈ (KimchiConstraint.addComplete c).unwiredVars) :
    ∃ (j : Nat) (hj : j < c.operands.toList.length), 7 ≤ j ∧ c.operands.toList[j]'hj = .var v := by
  simp only [KimchiConstraint.unwiredVars, List.mem_filterMap] at hv
  obtain ⟨x, hx, hxv⟩ := hv
  obtain ⟨u, rfl⟩ := CVar.var?_isSome (x := x) (by rw [hxv]; rfl)
  simp only [CVar.var?, Option.some.injEq] at hxv
  subst hxv
  obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hx
  have hk' : k < 4 := by
    simp only [List.length_drop, Vector.length_toList] at hk
    omega
  refine ⟨7 + k, by simp only [Vector.length_toList]; omega, by omega, ?_⟩
  rw [← hkx]
  exact List.getElem_drop.symm

/-- An unwired operand's variable is a term of its constraint. -/
private theorem mem_termVars_of_unwired {c : AddComplete F} {v : Variable}
    (hv : v ∈ (KimchiConstraint.addComplete c).unwiredVars) :
    v ∈ (KimchiConstraint.addComplete c).termVars := by
  obtain ⟨j, hj, -, hjv⟩ := unwired_index hv
  exact List.mem_flatMap.mpr ⟨_, List.getElem_mem hj, by
    rw [hjv, termVars_var]
    exact List.mem_singleton_self _⟩

/-- An unwired operand's variable occurs once: among the terms once, and never as a public
variable. -/
private theorem unwired_count {source : List (KimchiConstraint F)} {publicVars : List Variable}
    {nv : Variable} (hscope : KimchiConstraint.Wired.Scoped nv source publicVars)
    {c : KimchiConstraint F} (hc : c ∈ source) {v : Variable} (hv : v ∈ c.unwiredVars) :
    (source.flatMap KimchiConstraint.termVars).count v + publicVars.count v = 1 := by
  have := hscope.unwiredOnce c hc v hv
  simpa [occurrences, List.count_append] using this

/-- No event of any step names an unwired operand: its one occurrence is a bare operand, which
logs nothing, and allocations are fresh. -/
private theorem unwired_not_named_step {source : List (KimchiConstraint F)}
    {publicVars : List Variable} {nv : Variable}
    (hscope : KimchiConstraint.Wired.Scoped nv source publicVars) {q : Nat} (hq : q < source.length)
    {c : AddComplete F} (hsrc : source[q] = .addComplete c) {v : Variable}
    (hv : v ∈ (KimchiConstraint.addComplete c).unwiredVars) (p : Nat) (hp : p < source.length)
    (nv' : Variable) (aux' : AuxState F) (hnv : nv ≤ nv') :
    ∀ e ∈ (recordReduction nv' aux' source[p].reduce).events, v ∉ e.names := by
  intro e he hname
  have hvterm := mem_termVars_of_unwired hv
  have hcount := unwired_count hscope (hsrc ▸ List.getElem_mem hq) hv
  have hvocc : v ∈ occurrences source publicVars :=
    List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, List.getElem_mem hq, hsrc ▸ hvterm⟩)
  have hvlt : v < nv := hscope.below v hvocc
  have hfresh : ∀ w ∈ allocs (recordReduction nv' aux' source[p].reduce).events, nv' ≤ w :=
    (allocs_ge (record_constraint_allocates nv' aux' source[p])).1
  have hnotfresh : v ∉ allocs (recordReduction nv' aux' source[p].reduce).events := fun h =>
    Nat.lt_irrefl v (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hvlt hnv) (hfresh v h))
  obtain ⟨j, hj, -, hjv⟩ := unwired_index hv
  have hwd := hscope.wired _ (List.getElem_mem hp)
  obtain ⟨cp, hsp⟩ : ∃ cp, source[p] = cp := ⟨_, rfl⟩
  rw [hsp] at he hwd hnotfresh
  cases cp with
  | basic b =>
    rcases basic_names nv' aux' b e he v hname with hn | hn
    · have hne : p ≠ q := fun h => by
        subst h
        rw [hsp] at hsrc
        cases hsrc
      have := two_le_count_flatMap KimchiConstraint.termVars hp hq hne (hsp ▸ hn)
        (hsrc ▸ hvterm)
      omega
    · exact hnotfresh hn
  | addComplete c' =>
    obtain ⟨hn, -⟩ := addComplete_names nv' aux' c'
    rcases hn e he v hname with hn | ⟨x, hx, hxv, hxne⟩
    · exact hnotfresh hn
    · by_cases hpq : p = q
      · subst hpq
        rw [hsp] at hsrc
        cases hsrc
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have hne : i ≠ j := fun h => by
          subst h
          exact hxne hjv
        have h2 := two_le_count_flatMap CVar.termVars hi hj hne hxv
          (by rw [hjv, termVars_var]; exact List.mem_singleton_self _)
        have h3 := two_le_count_flatMap_same KimchiConstraint.termVars hq (by rw [hsp]; exact h2)
        omega
      · have := two_le_count_flatMap KimchiConstraint.termVars hp hq hpq
          (by rw [hsp]; exact List.mem_flatMap.mpr ⟨x, hx, hxv⟩) (hsrc ▸ hvterm)
        omega
  | poseidon _ => exact hwd.elim
  | varBaseMul _ => exact hwd.elim
  | endoScalar _ => exact hwd.elim
  | endoMul _ => exact hwd.elim
  | pad _ => exact hwd.elim

/-- An operand of an unwired column is named by no event of the lowering. -/
theorem unwired_not_named {source : List (KimchiConstraint F)} {publicVars : List Variable}
    {nv : Variable} (hscope : KimchiConstraint.Wired.Scoped nv source publicVars)
    {c : KimchiConstraint F} (hc : c ∈ source) {v : Variable} (hv : v ∈ c.unwiredVars) :
    ∀ s ∈ (lowering source nv).steps, ∀ e ∈ s.events, v ∉ e.names := by
  intro s hs e he
  obtain ⟨c', rfl⟩ := addComplete_of_unwired hv
  obtain ⟨q, hq, hsrc⟩ := List.mem_iff_getElem.mp hc
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hs
  have hp' : p < source.length := (length_steps source nv initialAuxState) ▸ hp
  obtain ⟨nv', aux', hnv', -, hstep⟩ := (recordGates_queued (fun _ => True) source nv
    (fun _ _ _ _ _ _ _ _ _ => trivial) nv initialAuxState (Nat.le_refl _)
    (fun _ _ => trivial)).1 p hp'
  rw [hstep] at he
  exact unwired_not_named_step hscope hq hsrc hv p hp' nv' aux' hnv' e he

/-- A complete addition's row read at a cell: the cell is one of the eleven operands' variables,
which is a term of its operand or fresh, and is the operand when that is bare. -/
private theorem addComplete_cell (nv' : Variable) (aux' : AuxState F) (c : AddComplete F)
    (j : Nat) (hj : j < wCols) (w : Variable)
    (hw : (recordReduction nv' aux' c.reduce).result.row.vars[j] = some w) :
    ∃ hj' : j < 11,
      (w ∈ (c.operands.toList[j]'(by simp [AddComplete.operands]; omega)).termVars ∨
        w ∈ allocs (recordReduction nv' aux' c.reduce).events) ∧
      ∀ u, c.operands.toList[j]'(by simp [AddComplete.operands]; omega) = .var u → w = u := by
  obtain ⟨-, vs, hvs, hall⟩ := addComplete_names nv' aux' c
  have hidx : j < (recordReduction nv' aux' c.reduce).result.row.vars.toList.length := by
    rw [Vector.length_toList]
    exact hj
  have hw' : (recordReduction nv' aux' c.reduce).result.row.vars.toList[j]'hidx = some w := by
    rw [Vector.getElem_toList]
    exact hw
  have hw'' := (List.getElem_of_eq hvs hidx).symm.trans hw'
  obtain ⟨hlen, hR⟩ := List.forall₂_iff_get.mp hall
  have hvl : vs.length = 11 := by
    rw [hlen]
    simp [AddComplete.operands]
  have hj11 : j < 11 := by
    by_contra h
    rw [List.getElem_append_right (by simp only [List.length_map]; omega),
      List.getElem_replicate] at hw''
    cases hw''
  rw [List.getElem_append_left (by simp only [List.length_map]; omega), List.getElem_map,
    Option.some.injEq] at hw''
  obtain ⟨hmem, hbare⟩ := hR j (by omega) (by simp [AddComplete.operands]; omega)
  simp only [List.get_eq_getElem] at hmem hbare
  refine ⟨hj11, ?_, fun u hu => ?_⟩
  · rw [← hw'']
    exact hmem
  · rw [← hw'']
    exact hbare u hu

/-- A cell of an unwired column carries an operand of an unwired column of some complete
addition of the source. -/
theorem unwired_of_cell {source : List (KimchiConstraint F)} {publicVars : List Variable}
    {nv : Variable} (hscope : KimchiConstraint.Wired.Scoped nv source publicVars) {r j : Nat}
    (hr : r < (directRows source publicVars nv).length) (hj : j < wCols) (h7 : 7 ≤ j)
    {w : Variable} (hw : (directRows source publicVars nv)[r].vars[j] = some w) :
    ∃ c ∈ source, w ∈ c.unwiredVars := by
  rcases wiredRows_cases (fun _ => True) hscope.wired (fun _ _ _ _ _ _ _ _ _ => trivial) r hr
    with ⟨hp, e⟩ | ⟨q, g, -, -, e⟩ | ⟨g, -, e⟩ | ⟨p, hp, c, nv', aux', -, hsrc, -, e⟩
  · rw [e] at hw
    have := (label_public publicVars r hp j hj w hw).1
    omega
  · rw [e] at hw
    have := (label_double' j hj w hw).1
    omega
  · rw [e] at hw
    have := (label_flush' j hj w hw).1
    omega
  · rw [e] at hw
    obtain ⟨hj11, -, hbare⟩ := addComplete_cell nv' aux' c j hj w hw
    have hwd := hscope.wired _ (List.getElem_mem hp)
    rw [hsrc] at hwd
    have hx : (c.operands.toList[j]'(by simp [AddComplete.operands]; omega)).var?.isSome :=
      hwd _ (List.mem_iff_getElem.mpr ⟨j - 7, by
        simp only [List.length_drop, Vector.length_toList]
        omega, by
        rw [List.getElem_drop]
        exact getElem_congr_idx (by omega)⟩)
    obtain ⟨u, hu⟩ := CVar.var?_isSome hx
    refine ⟨_, hsrc ▸ List.getElem_mem hp, ?_⟩
    rw [hbare u hu]
    simp only [KimchiConstraint.unwiredVars, List.mem_filterMap]
    refine ⟨.var u, List.mem_iff_getElem.mpr ⟨j - 7, by
      simp only [List.length_drop, Vector.length_toList]
      omega, by
      rw [List.getElem_drop, ← hu]
      exact getElem_congr_idx (by omega)⟩, rfl⟩

/-- Any cell an unwired operand labels is its own: the unwired column of its addition's row. -/
private theorem unwired_cell_at {source : List (KimchiConstraint F)} {publicVars : List Variable}
    {nv : Variable} (hscope : KimchiConstraint.Wired.Scoped nv source publicVars) {q : Nat}
    (hq : q < source.length) {c : AddComplete F} (hsrc : source[q] = .addComplete c)
    {v : Variable} (hv : v ∈ (KimchiConstraint.addComplete c).unwiredVars) {j₀ : Nat}
    (hj₀ : j₀ < c.operands.toList.length) (hj₀v : c.operands.toList[j₀]'hj₀ = .var v)
    (r j : Nat) (hr : r < (directRows source publicVars nv).length) (hj : j < wCols)
    (hrow : (directRows source publicVars nv)[r].vars[j] = some v) :
    r = gateRowOf source publicVars nv q hq ∧ j = j₀ := by
  have hcount := unwired_count hscope (hsrc ▸ List.getElem_mem hq) hv
  have hvterm := mem_termVars_of_unwired hv
  have hvlt : v < nv := hscope.below v
    (List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, List.getElem_mem hq, hsrc ▸ hvterm⟩))
  have hP : ∀ (c' : KimchiConstraint F), c' ∈ source → ∀ (nv' : Variable) (aux : AuxState F),
      nv ≤ nv' → ∀ e ∈ (recordReduction nv' aux c'.reduce).events, ∀ g, e.queued? = some g →
        v ∉ g.vars := by
    intro c' hc' nv' aux hnv e he g hg hvg
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hc'
    exact unwired_not_named_step hscope hq hsrc hv p hp nv' aux hnv e he (queued?_vars hg v hvg)
  rcases wiredRows_cases (fun g => v ∉ g.vars) hscope.wired hP r hr
    with ⟨hp, e⟩ | ⟨q', g, hq', hg, e⟩ | ⟨g, hg, e⟩ | ⟨p, hp, c', nv', aux', hnv', hsrc', hgr, e⟩
  · rw [e] at hrow
    have hpub := (label_public publicVars r hp j hj v hrow).2
    have h1 : 1 ≤ (source.flatMap KimchiConstraint.termVars).count v :=
      List.one_le_count_iff.mpr (List.mem_flatMap.mpr ⟨_, List.getElem_mem hq, hsrc ▸ hvterm⟩)
    have h2 : 1 ≤ publicVars.count v := List.one_le_count_iff.mpr hpub
    omega
  · rw [e] at hrow
    rcases (label_double' j hj v hrow).2 with h | h
    · exact (hq' h).elim
    · exact (hg h).elim
  · rw [e] at hrow
    exact (hg (label_flush' j hj v hrow).2).elim
  · rw [e] at hrow
    obtain ⟨hj11, hmem, -⟩ := addComplete_cell nv' aux' c' j hj v hrow
    have hfresh :=
      (allocs_ge (record_constraint_allocates nv' aux' (KimchiConstraint.addComplete c'))).1
    rcases hmem with hmem | hmem
    · by_cases hpq : p = q
      · subst hpq
        rw [hsrc'] at hsrc
        cases hsrc
        refine ⟨hgr, ?_⟩
        by_contra hne
        have h2 := two_le_count_flatMap CVar.termVars
          (by simp only [Vector.length_toList]; omega : j < c.operands.toList.length) hj₀ hne hmem
          (by rw [hj₀v, termVars_var]; exact List.mem_singleton_self _)
        have h3 := two_le_count_flatMap_same KimchiConstraint.termVars hq (by rw [hsrc']; exact h2)
        omega
      · have := two_le_count_flatMap KimchiConstraint.termVars hp hq hpq
          (by
            rw [hsrc']
            exact List.mem_flatMap.mpr
              ⟨_, List.getElem_mem (by rw [Vector.length_toList]; exact hj11), hmem⟩)
          (hsrc ▸ hvterm)
        omega
    · exact absurd (hfresh v hmem) (Nat.not_le.mpr (Nat.lt_of_lt_of_le hvlt hnv'))

/-- An operand of an unwired column labels one cell only. -/
theorem unwired_cell_unique {source : List (KimchiConstraint F)} {publicVars : List Variable}
    {nv : Variable} (hscope : KimchiConstraint.Wired.Scoped nv source publicVars)
    {c : KimchiConstraint F} (hc : c ∈ source) {v : Variable} (hv : v ∈ c.unwiredVars)
    (r j : Nat) (hr : r < (directRows source publicVars nv).length) (hj : j < wCols)
    (r' j' : Nat) (hr' : r' < (directRows source publicVars nv).length) (hj' : j' < wCols)
    (h1 : (directRows source publicVars nv)[r].vars[j] = some v)
    (h2 : (directRows source publicVars nv)[r'].vars[j'] = some v) : r = r' ∧ j = j' := by
  obtain ⟨c', rfl⟩ := addComplete_of_unwired hv
  obtain ⟨q, hq, hsrc⟩ := List.mem_iff_getElem.mp hc
  obtain ⟨j₀, hj₀, -, hj₀v⟩ := unwired_index hv
  obtain ⟨e1, e2⟩ := unwired_cell_at hscope hq hsrc hv hj₀ hj₀v r j hr hj h1
  obtain ⟨e3, e4⟩ := unwired_cell_at hscope hq hsrc hv hj₀ hj₀v r' j' hr' hj' h2
  exact ⟨e1.trans e3.symm, e2.trans e4.symm⟩

/-! ## The valuation -/

/-- The value at the variable's own unwired cell, else at a cell of its class, else `0`. The
unwired cell takes precedence, so an unwired operand reads its one cell whatever its class
holds; any other variable reads its root's class, so fused variables read alike. -/
private noncomputable def recoverClass (roots : Array Variable) (rows : List (KimchiRow F))
    (val : Nat × Nat → F) (v : Variable) : F :=
  if h : ∃ c : Fin rows.length × Fin wCols, 7 ≤ c.2.val ∧ rows[c.1].vars[c.2] = some v then
    val ((Classical.choose h).1, (Classical.choose h).2)
  else
    match classCells roots rows (roots.getD v v) with
    | c :: _ => val c
    | [] => 0

omit [DecidableEq F] in
/-- Every labelled cell reads its variable's recovered value, when the cells of a class agree
and an unwired label is unique. -/
private theorem recoverClass_spec (roots : Array Variable) (rows : List (KimchiRow F))
    (val : Nat × Nat → F)
    (hclass : ∀ k, ∀ c ∈ classCells roots rows k, ∀ c' ∈ classCells roots rows k, val c = val c')
    (huniq : ∀ (r j : Nat) (hr : r < rows.length) (hj : j < wCols) (v : Variable), 7 ≤ j →
      rows[r].vars[j] = some v → ∀ (r' j' : Nat) (hr' : r' < rows.length) (hj' : j' < wCols),
        rows[r'].vars[j'] = some v → r' = r ∧ j' = j)
    (r j : Nat) (hr : r < rows.length) (hj : j < wCols) (v : Variable)
    (hv : rows[r].vars[j] = some v) : val (r, j) = recoverClass roots rows val v := by
  by_cases hex : ∃ c : Fin rows.length × Fin wCols, 7 ≤ c.2.val ∧ rows[c.1].vars[c.2] = some v
  · simp only [recoverClass, dif_pos hex]
    have hc := Classical.choose_spec hex
    generalize Classical.choose hex = c at hc ⊢
    obtain ⟨h7, hc⟩ := hc
    obtain ⟨e1, e2⟩ := huniq c.1 c.2 c.1.isLt c.2.isLt v h7 hc r j hr hj hv
    rw [e1, e2]
  · simp only [recoverClass, dif_neg hex]
    have h7 : j < 7 := by
      by_contra h
      exact hex ⟨(⟨r, hr⟩, ⟨j, hj⟩), Nat.le_of_not_lt h, hv⟩
    have hmem := mem_classCells_of_label (roots := roots) hr h7 hv
    rcases hcs : classCells roots rows (roots.getD v v) with _ | ⟨c, cs⟩
    · rw [hcs] at hmem
      exact (List.not_mem_nil hmem).elim
    · simp only
      refine hclass _ _ hmem c ?_
      rw [hcs]
      exact List.mem_cons_self ..

omit [DecidableEq F] in
/-- Two variables with one root read alike, when neither labels an unwired cell. -/
private theorem recoverClass_eq_of_root_eq (roots : Array Variable) (rows : List (KimchiRow F))
    (val : Nat × Nat → F) {v w : Variable} (hroot : roots.getD v v = roots.getD w w)
    (hv : ∀ (r j : Nat) (hr : r < rows.length) (hj : j < wCols), rows[r].vars[j] = some v →
      j < 7)
    (hw : ∀ (r j : Nat) (hr : r < rows.length) (hj : j < wCols), rows[r].vars[j] = some w →
      j < 7) :
    recoverClass roots rows val v = recoverClass roots rows val w := by
  have hnv : ¬ ∃ c : Fin rows.length × Fin wCols, 7 ≤ c.2.val ∧ rows[c.1].vars[c.2] = some v := by
    rintro ⟨c, h7, hc⟩
    exact absurd (hv c.1 c.2 c.1.isLt c.2.isLt hc) (Nat.not_lt.mpr h7)
  have hnw : ¬ ∃ c : Fin rows.length × Fin wCols, 7 ≤ c.2.val ∧ rows[c.1].vars[c.2] = some w := by
    rintro ⟨c, h7, hc⟩
    exact absurd (hw c.1 c.2 c.1.isLt c.2.isLt hc) (Nat.not_lt.mpr h7)
  simp only [recoverClass, dif_neg hnv, dif_neg hnw, hroot]


/-! ## The theorem -/

/-- Every step of the lowering is some constraint's recording from a counter at or above the
start. -/
private theorem step_shape {source : List (KimchiConstraint F)} {nv : Variable}
    {s : RecordedStep F} (hs : s ∈ (lowering source nv).steps) :
    ∃ (p : Nat) (hp : p < source.length) (nv' : Variable) (aux' : AuxState F), nv ≤ nv' ∧
      s = ⟨(recordReduction nv' aux' source[p].reduce).rows,
        (recordReduction nv' aux' source[p].reduce).result,
        (recordReduction nv' aux' source[p].reduce).events⟩ := by
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hs
  have hp' : p < source.length := (length_steps source nv initialAuxState) ▸ hp
  obtain ⟨nv', aux', hnv', -, hstep⟩ := (recordGates_queued (fun _ => True) source nv
    (fun _ _ _ _ _ _ _ _ _ => trivial) nv initialAuxState (Nat.le_refl _)
    (fun _ _ => trivial)).1 p hp'
  exact ⟨p, hp', nv', aux', hnv', hstep⟩

/-- Every equation any step of the lowering queues carries no coefficient on an absent cell. -/
private theorem step_absentZero {source : List (KimchiConstraint F)} {nv : Variable}
    (hw : ∀ c ∈ source, c.Wired) {s : RecordedStep F} (hs : s ∈ (lowering source nv).steps) :
    ∀ e ∈ s.events, ∀ g, e.queued? = some g → g.AbsentZero := by
  obtain ⟨p, hp, nv', aux', -, rfl⟩ := step_shape hs
  have hwd := hw _ (List.getElem_mem hp)
  obtain ⟨cp, hsp⟩ : ∃ cp, source[p] = cp := ⟨_, rfl⟩
  rw [hsp] at hwd
  show ∀ e ∈ (recordReduction nv' aux' source[p].reduce).events, _
  rw [hsp]
  cases cp with
  | basic b => exact basic_absentZero nv' aux' b
  | addComplete c => exact addComplete_absentZero nv' aux' c
  | poseidon _ => exact hwd.elim
  | varBaseMul _ => exact hwd.elim
  | endoScalar _ => exact hwd.elim
  | endoMul _ => exact hwd.elim
  | pad _ => exact hwd.elim

omit [Field F] [DecidableEq F] in
private theorem fusions_of_merge {es : List (ReductionEvent F)} {c : EqualsConstraint F}
    {l r : Variable} (h : ReductionEvent.equal c (.merge l r) ∈ es) : (l, r) ∈ fusions es := by
  induction es with
  | nil => exact (List.not_mem_nil h).elim
  | cons e es ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · have h' := ih h
      cases e with
      | alloc _ _ => exact h'
      | generic _ => exact h'
      | equal _ o => cases o <;> first | exact h' | exact List.mem_cons_of_mem _ h'

omit [Field F] [DecidableEq F] in
private theorem fusions_of_cached {es : List (ReductionEvent F)} {c : EqualsConstraint F}
    {l v : Variable} {k : F} (h : ReductionEvent.equal c (.cached l v k) ∈ es) :
    (l, v) ∈ fusions es := by
  induction es with
  | nil => exact (List.not_mem_nil h).elim
  | cons e es ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · have h' := ih h
      cases e with
      | alloc _ _ => exact h'
      | generic _ => exact h'
      | equal _ o => cases o <;> first | exact h' | exact List.mem_cons_of_mem _ h'

omit [Field F] [DecidableEq F] in
/-- A fusion's endpoints are names of its event, except a cache hit's cached variable. -/
private theorem mem_fusions_names {es : List (ReductionEvent F)} {p : Variable × Variable}
    (hp : p ∈ fusions es) :
    ∃ e ∈ es, p.1 ∈ e.names ∧
      (p.2 ∈ e.names ∨ ∃ c k, e = ReductionEvent.equal c (.cached p.1 p.2 k)) := by
  induction es with
  | nil => exact (List.not_mem_nil hp).elim
  | cons e es ih =>
    have step : p ∈ fusions es → ∃ e' ∈ e :: es, p.1 ∈ e'.names ∧
        (p.2 ∈ e'.names ∨ ∃ c k, e' = ReductionEvent.equal c (.cached p.1 p.2 k)) := fun h =>
      let ⟨e', he', h'⟩ := ih h
      ⟨e', List.mem_cons_of_mem _ he', h'⟩
    cases e with
    | alloc _ _ => exact step hp
    | generic _ => exact step hp
    | equal c o =>
      cases o with
      | merge l r =>
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨_, List.mem_cons_self .., by simp [ReductionEvent.names, EqualOutcome.names],
            Or.inl (by simp [ReductionEvent.names, EqualOutcome.names])⟩
        · exact step hp
      | cached l v k =>
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨_, List.mem_cons_self .., by simp [ReductionEvent.names, EqualOutcome.names],
            Or.inr ⟨c, k, rfl⟩⟩
        · exact step hp
      | pinned _ _ _ => exact step hp
      | row _ => exact step hp
      | trivial => exact step hp

/-- A queued equation of the lowering holds at a valuation that reads every labelled cell: its
receipt locates it in a generic row the table satisfies. -/
private theorem queued_holds {n : ℕ} [NeZero n] {source : List (KimchiConstraint F)}
    {publicVars : List Variable} {nv : Variable} {idx : Index F n}
    (hindex : IndexOf source publicVars nv idx) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (hsat : idx.Satisfies pub wTab) (V : Valuation F)
    (hval : ∀ (r j : Nat) (hr : r < (directRows source publicVars nv).length) (hj : j < wCols)
      (v : Variable), (directRows source publicVars nv)[r].vars[j] = some v →
        wTab ⟨r, lt_of_lt_of_le hr hindex.rows_le⟩ ⟨j, hj⟩ = V v)
    {s : RecordedStep F} (hs : s ∈ (lowering source nv).steps) {e : ReductionEvent F}
    (he : e ∈ s.events) {g : GenericPlonkConstraint F} (hg : e.queued? = some g)
    (habsent : g.AbsentZero) : genericValue V g = 0 := by
  have hrows_le := hindex.rows_le
  have hlenPub : (makePublicInputRows (F := F) publicVars).length = publicVars.length := by
    simp [makePublicInputRows]
  have hq0 : (initialAuxState : AuxState F).queuedGenericGate = none := rfl
  obtain ⟨rc, hrc, hrcg⟩ := receipts_complete source nv initialAuxState hq0 s hs g ⟨e, he, hg⟩
  have hloc := receipts_located source nv initialAuxState hq0 rc hrc
  obtain ⟨row, hrow, hkind, -, -⟩ := id hloc
  obtain ⟨hrowlt, hrow'⟩ := List.getElem?_eq_some_iff.mp hrow
  have hrowlt' : rc.row < (lowering source nv).allRows.length := hrowlt
  have hi' : publicVars.length + rc.row < (directRows source publicVars nv).length := by
    simp only [directRows, List.length_append, hlenPub]
    omega
  have hrowi : (directRows source publicVars nv)[publicVars.length + rc.row] = row := by
    simp only [directRows]
    rw [List.getElem_append_right (by omega)]
    simp only [hlenPub, Nat.add_sub_cancel_left]
    exact hrow'
  have hgen := hsat.1 ⟨publicVars.length + rc.row, by omega⟩
  have htyp' : (idx.gates ⟨publicVars.length + rc.row, by omega⟩).typ = .generic := by
    rw [hindex.typ_eq _ hi', hrowi, hkind]
  unfold Index.rowSatisfies at hgen
  rw [htyp'] at hgen
  simp only at hgen
  have hpub0 : Index.pubAt idx pub ⟨publicVars.length + rc.row, by omega⟩ = 0 := by
    unfold Index.pubAt
    rw [dif_neg (by
      rw [hindex.publicCount]
      show ¬ publicVars.length + rc.row < publicVars.length
      omega)]
  rw [hpub0, withPublic_zero] at hgen
  have hq : (⟨idx.coeffTable ⟨publicVars.length + rc.row, by omega⟩,
      wTab ⟨publicVars.length + rc.row, by omega⟩⟩ : Kimchi.Gate.Generic F) =
      genericAt row (wTab ⟨publicVars.length + rc.row, by omega⟩) := by
    simp only [genericAt]
    congr 1
    funext k
    rw [Index.coeffTable, hindex.coeffs_eq _ hi' k, hrowi]
  rw [hq] at hgen
  have hw : ∀ (k : Fin wCols) (w : Variable), row.vars[k] = some w →
      wTab ⟨publicVars.length + rc.row, by omega⟩ k = V w := by
    intro k w hk
    have := hval _ k.val hi' k.isLt w (by rw [hrowi]; exact hk)
    simpa using this
  have hz := genericValue_of_located hloc hrow _ V hw (by rw [hrcg]; exact habsent) hgen
  rw [hrcg] at hz
  exact hz

/-- A complete addition's row carries a variable in each of its eleven operand cells. -/
private theorem addComplete_cell_some (nv' : Variable) (aux' : AuxState F) (c : AddComplete F)
    (k : Fin wCols) (hk : k.val < 11) :
    ∃ w, (recordReduction nv' aux' c.reduce).result.row.vars[k] = some w := by
  obtain ⟨-, vs, hvs, hall⟩ := addComplete_names nv' aux' c
  have hvl : vs.length = 11 := by
    rw [(List.forall₂_iff_get.mp hall).1]
    simp [AddComplete.operands]
  have hidx : k.val < (recordReduction nv' aux' c.reduce).result.row.vars.toList.length := by
    rw [Vector.length_toList]
    exact k.isLt
  refine ⟨vs[k.val]'(by omega), ?_⟩
  have h := List.getElem_of_eq hvs hidx
  rw [List.getElem_append_left (by simp only [List.length_map]; omega), List.getElem_map] at h
  rw [Vector.getElem_toList] at h
  exact h

/-- **The wired fragment's closed theorem.** Any table satisfying an index of the fragment's
lowering yields a valuation satisfying every source constraint and reading the public
variables as the public input. -/
theorem KimchiConstraint.Wired.holds_of_satisfies {n : ℕ} [NeZero n]
    {source : List (KimchiConstraint F)} {publicVars : List Variable} {nv : Variable}
    {idx : Index F n} (hscope : KimchiConstraint.Wired.Scoped nv source publicVars)
    (hindex : IndexOf source publicVars nv idx) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (hsat : idx.Satisfies pub wTab) :
    ∃ V : Valuation F, (∀ c ∈ source, KimchiConstraint.Holds V c) ∧
      ∀ i : Fin publicVars.length, V publicVars[i] = pub (hindex.publicIndex i) := by
  have hrows_le := hindex.rows_le
  have hlenPub : (makePublicInputRows (F := F) publicVars).length = publicVars.length := by
    simp [makePublicInputRows]
  have hpub_le : publicVars.length ≤ (directRows source publicVars nv).length := by
    simp [directRows, hlenPub]
  -- the valuation
  let V : Valuation F :=
    recoverClass (directRoots source nv) (directRows source publicVars nv) (cellVal wTab)
  have hclass := hindex.classCells_eq pub wTab hsat
  have huniq : ∀ (r j : Nat) (hr : r < (directRows source publicVars nv).length) (hj : j < wCols)
      (v : Variable), 7 ≤ j → (directRows source publicVars nv)[r].vars[j] = some v →
      ∀ (r' j' : Nat) (hr' : r' < (directRows source publicVars nv).length) (hj' : j' < wCols),
        (directRows source publicVars nv)[r'].vars[j'] = some v → r' = r ∧ j' = j := by
    intro r j hr hj v h7 hv r' j' hr' hj' hv'
    obtain ⟨c, hc, hvc⟩ := unwired_of_cell hscope hr hj h7 hv
    exact unwired_cell_unique hscope hc hvc r' j' hr' hj' r j hr hj hv' hv
  have hreal : ∀ (r j : Nat) (hr : r < (directRows source publicVars nv).length) (hj : j < wCols)
      (v : Variable), (directRows source publicVars nv)[r].vars[j] = some v →
      cellVal wTab (r, j) = V v :=
    fun r j hr hj v hv =>
      recoverClass_spec _ _ _ (fun k c hc c' hc' => hclass k hc hc') huniq r j hr hj v hv
  have hval : ∀ (r j : Nat) (hr : r < (directRows source publicVars nv).length) (hj : j < wCols)
      (v : Variable), (directRows source publicVars nv)[r].vars[j] = some v →
      wTab ⟨r, lt_of_lt_of_le hr hrows_le⟩ ⟨j, hj⟩ = V v := by
    intro r j hr hj v hv
    rw [← hreal r j hr hj v hv]
    simp only [cellVal, dif_pos (And.intro (lt_of_lt_of_le hr hrows_le) hj)]
  -- no name of any event labels an unwired cell
  have hwiredOnly : ∀ s ∈ (lowering source nv).steps, ∀ e ∈ s.events, ∀ w ∈ e.names,
      ∀ (r j : Nat) (hr : r < (directRows source publicVars nv).length) (hj : j < wCols),
        (directRows source publicVars nv)[r].vars[j] = some w → j < 7 := by
    intro s hs e he w hw r j hr hj hrow
    by_contra h7
    obtain ⟨c, hc, hwc⟩ := unwired_of_cell hscope hr hj (Nat.le_of_not_lt h7) hrow
    exact unwired_not_named hscope hc hwc s hs e he hw
  -- every queued equation holds
  have hqueued : ∀ s ∈ (lowering source nv).steps, ∀ e ∈ s.events, ∀ g, e.queued? = some g →
      genericValue V g = 0 :=
    fun s hs e he g hg =>
      queued_holds hindex pub wTab hsat V hval hs he hg (step_absentZero hscope.wired hs e he g hg)
  -- fused variables read alike
  have hfused : ∀ s ∈ (lowering source nv).steps, ∀ p ∈ fusions s.events, V p.1 = V p.2 := by
    intro s hs p hp
    obtain ⟨e, he, h1, h2⟩ := mem_fusions_names hp
    refine recoverClass_eq_of_root_eq _ _ _ (fusion_root_eq source nv hs hp)
      (hwiredOnly s hs e he p.1 h1) ?_
    rcases h2 with h2 | ⟨c, k, rfl⟩
    · exact hwiredOnly s hs e he p.2 h2
    · obtain ⟨s', hs', c', g, hg⟩ := pinned_of_cached source nv hs he
      exact hwiredOnly s' hs' _ hg p.2 (List.mem_cons_self ..)
  -- a cache hit's constant is pinned
  have hpin : ∀ s ∈ (lowering source nv).steps, ∀ (c : EqualsConstraint F) (l v : Variable)
      (k : F), ReductionEvent.equal c (.cached l v k) ∈ s.events → V v = k := by
    intro s hs c l v k he
    obtain ⟨s', hs', c', g, hg⟩ := pinned_of_cached source nv hs he
    obtain ⟨p, hp, nv', aux', -, hshape⟩ := step_shape hs'
    have hdec : OutcomesFaithful ⟨[], nv', aux'⟩ s'.events := by
      rw [hshape]
      exact record_constraint_decides nv' aux' source[p]
    obtain ⟨cache, hcache⟩ := outcomeOf_of_mem hdec hg
    exact (equalsHolds_of_pinned hcache V (hqueued _ hs' _ hg g rfl)).2
  -- every event holds
  have hfacts : ∀ s ∈ (lowering source nv).steps, ReductionFacts V s.events := by
    intro s hs e he
    obtain ⟨p, hp, nv', aux', -, hshape⟩ := step_shape hs
    cases e with
    | alloc _ _ => trivial
    | generic g => exact hqueued s hs _ he g rfl
    | equal c o =>
      have hdec : OutcomesFaithful ⟨[], nv', aux'⟩ s.events := by
        rw [hshape]
        exact record_constraint_decides nv' aux' source[p]
      obtain ⟨cache, hcache⟩ := outcomeOf_of_mem hdec he
      show equalsHolds V c
      cases o with
      | merge l r => exact equalsHolds_of_merge hcache V (hfused s hs (l, r) (fusions_of_merge he))
      | cached l v k =>
        exact equalsHolds_of_cached hcache V (hfused s hs (l, v) (fusions_of_cached he))
          (hpin s hs c l v k he)
      | pinned v k g => exact (equalsHolds_of_pinned hcache V (hqueued s hs _ he g rfl)).1
      | row g => exact equalsHolds_of_row hcache V (hqueued s hs _ he g rfl)
      | trivial => exact equalsHolds_of_trivial hcache V
  refine ⟨V, ?_, ?_⟩
  · intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hc
    have hi : p < (lowering source nv).steps.length :=
      (length_steps source nv initialAuxState).symm ▸ hp
    obtain ⟨nv', aux', -, -, hstep⟩ := (recordGates_queued (fun _ => True) source nv
      (fun _ _ _ _ _ _ _ _ _ => trivial) nv initialAuxState (Nat.le_refl _)
      (fun _ _ => trivial)).1 p hp
    have hstep' : (lowering source nv).steps[p] =
        ⟨(recordReduction nv' aux' source[p].reduce).rows,
          (recordReduction nv' aux' source[p].reduce).result,
          (recordReduction nv' aux' source[p].reduce).events⟩ := hstep
    have hf := hfacts _ (List.getElem_mem hi)
    rw [hstep'] at hf
    have hwd := hscope.wired _ (List.getElem_mem hp)
    obtain ⟨cp, hsp⟩ : ∃ cp, source[p] = cp := ⟨_, rfl⟩
    rw [hsp] at hf hwd ⊢
    cases cp with
    | basic b => exact basic_of_reductionFacts nv' aux' b V hf
    | addComplete c =>
      have hgr : (lowering source nv).steps[p].gateRows =
          [(recordReduction nv' aux' c.reduce).result.row] := by
        rw [hstep, hsp]
        rfl
      have hip : p < (lowering source nv).placements.length := by
        rw [RecordedGates.length_placements]
        exact hi
      have hle := placements_customRows_le (lowering source nv) p hi
      rw [placements_customRows_count _ _ hi, hgr, List.length_singleton] at hle
      have hle' : ((lowering source nv).placements[p]'hip).customRows.first + 1 ≤
        (lowering source nv).bodyRows.length := hle
      have hi' : publicVars.length + ((lowering source nv).placements[p]'hip).customRows.first <
          (directRows source publicVars nv).length := by
        simp only [directRows, List.length_append, hlenPub, RecordedGates.allRows]
        omega
      have hrow := getElem_bodyRows_gate (lowering source nv) p hi 0 (by simp [hgr])
        (show ((lowering source nv).placements[p]'hip).customRows.first + 0 <
          (lowering source nv).bodyRows.length by omega)
      have hrowi : (directRows source publicVars nv)[publicVars.length +
          ((lowering source nv).placements[p]'hip).customRows.first] =
          (recordReduction nv' aux' c.reduce).result.row := by
        simp only [directRows]
        rw [List.getElem_append_right (by omega)]
        simp only [hlenPub, Nat.add_sub_cancel_left, RecordedGates.allRows]
        rw [List.getElem_append_left (by omega)]
        refine ((getElem_congr_idx (Nat.add_zero _)).symm.trans hrow).trans ?_
        simp only [hgr, List.getElem_cons_zero]
      have hadd := hsat.1 ⟨publicVars.length +
        ((lowering source nv).placements[p]'hip).customRows.first, by omega⟩
      have htyp' : (idx.gates ⟨publicVars.length +
          ((lowering source nv).placements[p]'hip).customRows.first, by omega⟩).typ =
          .completeAdd := by
        rw [hindex.typ_eq _ hi', hrowi]
        rfl
      unfold Index.rowSatisfies at hadd
      rw [htyp'] at hadd
      simp only at hadd
      have hcells : ∀ k : Fin wCols, k.val < 11 → wTab ⟨publicVars.length +
          ((lowering source nv).placements[p]'hip).customRows.first, by omega⟩ k =
          rowValues V (recordReduction nv' aux' c.reduce).result.row k := by
        intro k hk
        obtain ⟨w, hlab⟩ := addComplete_cell_some nv' aux' c k hk
        rw [hval _ k.val hi' k.isLt _ (by rw [hrowi]; exact hlab)]
        simp only [rowValues, hlab, Option.map_some, Option.getD_some]
      have hmap : Lift.Gate.AddComplete.cellMap (wTab ⟨publicVars.length +
          ((lowering source nv).placements[p]'hip).customRows.first, by omega⟩) =
          Lift.Gate.AddComplete.cellMap
            (rowValues V (recordReduction nv' aux' c.reduce).result.row) := by
        simp only [Lift.Gate.AddComplete.cellMap]
        congr 1 <;> exact hcells _ (by decide)
      refine addComplete_holds_of_reductionFacts nv' aux' c V hf ?_
      rw [← hmap]
      exact hadd
    | poseidon _ => exact hwd.elim
    | varBaseMul _ => exact hwd.elim
    | endoScalar _ => exact hwd.elim
    | endoMul _ => exact hwd.elim
    | pad _ => exact hwd.elim
  · intro i
    have hi : i.val < (directRows source publicVars nv).length := by
      have := i.isLt
      omega
    have hrowi : (directRows source publicVars nv)[i.val] =
        (makePublicInputRows publicVars)[i.val]'(by simp [hlenPub]) :=
      List.getElem_append_left (by simp [hlenPub])
    have hlab : (directRows source publicVars nv)[i.val].vars[0] = some publicVars[i] := by
      rw [hrowi]
      simp only [makePublicInputRows, List.getElem_map]
      rfl
    have h1 := hval i.val 0 hi (by decide) _ hlab
    have h2 := hsat.2.2 (hindex.publicIndex i)
    rw [← h1]
    exact h2.symm ▸ rfl

end Snarky.Kimchi
