import Snarky.Kimchi.Constraint

/-!
# The lowering trace

The builder's reduction with its provenance kept: which reduction operations a constraint's
reducer invoked, in execution order. The recording interpreter runs the existing polymorphic
reducers unchanged: each operation delegates to the builder's and logs its payload, so a
recorded reduction is the existing lowering beside its history, and `RecordedReduction.erase`
returns `reduceAsBuilder`'s.

## Main definitions

- `ReductionEvent`: one reduction operation with its payload, as the reducer issued it.
- `RecordedReduction`: a reduction's result, events, rows, and the counter and auxiliary
  state handed back; `RecordedReduction.erase` forgets the events.
- `RecordingBuilder`: the recording interpreter, and `recordReduction`, its run from a
  borrowed counter and auxiliary state.
- `replay`: an event list re-executed through the builder's primitives, and
  `RecordedReduction.finish`, a recorded reduction's final builder state.
- `AllocationsFresh`: every allocation's logged variable is the counter at its point.
- `OutcomesFaithful`: every equality's logged outcome is the equality op's decision at its
  point.
- `ReductionEvent.names`, `ReductionEvent.queued?`, `allocs`, `fusions`, `pinsOf`: the
  variables an event writes or fuses, the equation it queued, and a log's allocations, fusions
  and pins.

## Main results

- `record_reduceToVariable_erases`, `record_basic_erases`, `record_addComplete_erases`,
  `record_constraint_erases`: the reducers, recorded, erase to their ordinary reductions.
- `record_constraint_replays`, `record_constraint_allocates`, `record_constraint_decides`: a
  recorded reduction ends in the replay of its own events, whose allocations log the counter
  and whose equalities log their outcomes.
- `replayEvent_equal`, `outcomeOf_of_mem`: a faithful equality event replays as its outcome's
  effect, and its outcome is the op's decision at some cache.
- `cache_replay`, `cached_mem`, `mem_pinsOf`: a faithful log's replay extends the cache by
  exactly its pins, so a cache hit names a pin of the log or of the starting cache, and a pin
  of the log is one of its pinning events.
- `inv_replay`, `same_replay_mono`, `same_replay`: a faithful log replayed from an invariant
  union-find keeps it, never splits a class, and ends with every fusion it logs in one class.
- `allocs_ge`: a log with fresh allocations allocates at or above its starting counter.

## Implementation notes

An allocation event keeps the affine expression the reducer allocated for. That records the
intended advice computation only: the builder's allocation ignores it, and nothing reads it
as an equation. An equality event keeps the request and the decision the equality op took on
it, which depends on the constant cache at that moment; logging the decision lets every later
reading attribute a merge, a cache hit or a queued row to its event without replaying the
cache. Events carry payloads, not state snapshots; a snapshot per event would copy the
union-find and the constant cache at every operation.

Erasure is proved per reducer, not for arbitrary code in the recording monad: a computation
written directly in `RecordingBuilder` can change the core without logging, so only the
reducers, which touch the state through the three operations alone, are shown to simulate.
A simulation says the recording computation returns the builder's result and carries the
builder's state as its core, from every state; the operations simulate by reflexivity, the
lemmas for `pure` and `bind` compose them along a reducer's structure with a file-local
tactic, and one lemma turns a simulation into the erasure equation. The reducers' arithmetic
is never reproved.
-/

namespace Snarky.Kimchi

open Snarky

variable {F α β : Type}

/-! ## The trace data -/

/-- One reduction operation as the reducer issued it: an allocation with the affine
expression it stands for, a generic constraint handed to the batching queue, or a two-sided
equality with what the equality op did with it. -/
inductive ReductionEvent (F : Type) where
  /-- The variable allocated for an affine expression; the expression is the intended advice
  computation, not an equation. -/
  | alloc (v : Variable) (expression : AffineExpression F)
  /-- A generic constraint handed to the batching queue. -/
  | generic (constraint : GenericPlonkConstraint F)
  /-- A two-sided equality, with the equality op's decision on it. -/
  | equal (constraint : EqualsConstraint F) (outcome : EqualOutcome F)

/-- A reduction run with its provenance: the result, the operations in execution order, the
emitted rows in emission order, and the counter and auxiliary state handed back. -/
structure RecordedReduction (F : Type) (α : Type) where
  /-- The reducer's result. -/
  result : α
  /-- The operations, in execution order. -/
  events : List (ReductionEvent F)
  /-- The emitted rows, in emission order. -/
  rows : List (Rows F)
  /-- The counter handed back. -/
  nextVariable : Variable
  /-- The auxiliary state handed back. -/
  aux : AuxState F

/-- Forget the events: the shape `reduceAsBuilder` returns. -/
def RecordedReduction.erase (r : RecordedReduction F α) :
    α × List (Rows F) × Variable × AuxState F :=
  (r.result, r.rows, r.nextVariable, r.aux)

/-! ## The recording interpreter -/

/-- The builder's state beside the events logged so far. -/
structure RecordingState (F : Type) where
  /-- The builder's state. -/
  core : BuilderReductionState F
  /-- The events logged so far, newest first. -/
  eventsRev : List (ReductionEvent F)

/-- The monad the recording interpreter runs in. -/
abbrev RecordingBuilder (F : Type) := StateM (RecordingState F)

/-- Run a builder computation on the core state, leaving the log alone. -/
private def liftCore (x : PlonkBuilder F α) : RecordingBuilder F α := fun s =>
  let (a, core) := x s.core
  (a, { s with core })

/-- Log one event. -/
private def record (e : ReductionEvent F) : RecordingBuilder F Unit :=
  modify fun s => { s with eventsRev := e :: s.eventsRev }

/-- The recording interpreter: each operation delegates to the builder's and logs its payload,
an allocation with the variable the builder returned, an equality with the decision the op
takes against the cache it finds. -/
instance [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F] :
    PlonkReductionM F (RecordingBuilder F) where
  createInternalVariable e := do
    let v ← liftCore (createInternalVariable e)
    record (.alloc v e)
    pure v
  addGenericPlonkConstraint g := do
    liftCore (addGenericPlonkConstraint g)
    record (.generic g)
  addEqualsConstraint c := do
    let s ← get
    liftCore (addEqualsConstraint c)
    record (.equal c (outcomeOf c s.core.aux.wireState.cachedConstants))

/-- Run a reduction in the recording interpreter from a borrowed counter and auxiliary
state: the result, the events in execution order, the rows in emission order, and the
counter and auxiliary state to hand back. -/
def recordReduction (nextVariable : Variable) (aux : AuxState F) (x : RecordingBuilder F α) :
    RecordedReduction F α :=
  let (a, s) := x ⟨⟨[], nextVariable, aux⟩, []⟩
  { result := a, events := s.eventsRev.reverse, rows := s.core.constraints.reverse.map Rows.mk
    nextVariable := s.core.nextVariable, aux := s.core.aux }

/-! ## Replay -/

section Replay

variable [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F]

/-- The builder's primitive for one event, on the builder's state: an allocation, the logged
variable ignored; a generic constraint's batching; an equality's wiring, cache or emission, the
logged outcome ignored. -/
def replayEvent (s : BuilderReductionState F) : ReductionEvent F → BuilderReductionState F
  | .alloc _ e => ((createInternalVariable e : PlonkBuilder F Variable) s).2
  | .generic g => ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2
  | .equal c _ => ((addEqualsConstraint c : PlonkBuilder F Unit) s).2

/-- Re-execute an event list through the builder's primitives, in order. -/
def replay (s : BuilderReductionState F) (events : List (ReductionEvent F)) :
    BuilderReductionState F :=
  events.foldl replayEvent s

private theorem replay_append (s : BuilderReductionState F) (es₁ es₂ : List (ReductionEvent F)) :
    replay s (es₁ ++ es₂) = replay (replay s es₁) es₂ :=
  List.foldl_append

/-- A recorded reduction's final builder state: its rows newest first, the counter and the
auxiliary state. -/
def RecordedReduction.finish (r : RecordedReduction F α) : BuilderReductionState F :=
  { constraints := (r.rows.map (·.row)).reverse, nextVariable := r.nextVariable, aux := r.aux }

/-- Every allocation's logged variable is the counter at its point: the events replayed from
`s`, each allocation checked before its own effect. -/
def AllocationsFresh (s : BuilderReductionState F) : List (ReductionEvent F) → Prop
  | [] => True
  | .alloc v e :: es => v = s.nextVariable ∧ AllocationsFresh (replayEvent s (.alloc v e)) es
  | e :: es => AllocationsFresh (replayEvent s e) es

private theorem allocationsFresh_append (s : BuilderReductionState F)
    (es₁ es₂ : List (ReductionEvent F)) :
    AllocationsFresh s (es₁ ++ es₂) ↔
      AllocationsFresh s es₁ ∧ AllocationsFresh (replay s es₁) es₂ := by
  induction es₁ generalizing s with
  | nil => simp [AllocationsFresh, replay]
  | cons e es ih =>
    cases e with
    | alloc v ex =>
      simp only [List.cons_append, AllocationsFresh, ih, replay, List.foldl_cons, and_assoc]
    | generic g => simp only [List.cons_append, AllocationsFresh, ih, replay, List.foldl_cons]
    | equal c o => simp only [List.cons_append, AllocationsFresh, ih, replay, List.foldl_cons]

/-- Every equality's logged outcome is the equality op's decision at its point: the events
replayed from `s`, each equality checked against the cache before its own effect. -/
def OutcomesFaithful (s : BuilderReductionState F) : List (ReductionEvent F) → Prop
  | [] => True
  | .equal c o :: es =>
    o = outcomeOf c s.aux.wireState.cachedConstants ∧
      OutcomesFaithful (replayEvent s (.equal c o)) es
  | e :: es => OutcomesFaithful (replayEvent s e) es

private theorem outcomesFaithful_append (s : BuilderReductionState F)
    (es₁ es₂ : List (ReductionEvent F)) :
    OutcomesFaithful s (es₁ ++ es₂) ↔
      OutcomesFaithful s es₁ ∧ OutcomesFaithful (replay s es₁) es₂ := by
  induction es₁ generalizing s with
  | nil => simp [OutcomesFaithful, replay]
  | cons e es ih =>
    cases e with
    | alloc v ex => simp only [List.cons_append, OutcomesFaithful, ih, replay, List.foldl_cons]
    | generic g => simp only [List.cons_append, OutcomesFaithful, ih, replay, List.foldl_cons]
    | equal c o =>
      simp only [List.cons_append, OutcomesFaithful, ih, replay, List.foldl_cons, and_assoc]

/-- A faithful equality event replays as its outcome's effect. -/
theorem replayEvent_equal (s : BuilderReductionState F) (c : EqualsConstraint F)
    {o : EqualOutcome F} (h : o = outcomeOf c s.aux.wireState.cachedConstants) :
    replayEvent s (.equal c o) = applyOutcome o s := by
  subst h
  show ((addEqualsConstraint c : PlonkBuilder F Unit) s).2 = _
  rw [addEqualsConstraint_apply]

/-- The constants a log pins, newest first, as the cache holds them. -/
def pinsOf : List (ReductionEvent F) → List (F × Variable)
  | [] => []
  | .equal _ (.pinned v k _) :: es => pinsOf es ++ [(k, v)]
  | _ :: es => pinsOf es

/-- Faithfulness of a log splits at its head. -/
theorem outcomesFaithful_cons {s : BuilderReductionState F} {e : ReductionEvent F}
    {es : List (ReductionEvent F)} (h : OutcomesFaithful s (e :: es)) :
    OutcomesFaithful s [e] ∧ OutcomesFaithful (replayEvent s e) es := by
  cases e with
  | alloc v ex => exact ⟨trivial, h⟩
  | generic g => exact ⟨trivial, h⟩
  | equal c o => exact ⟨⟨h.1, trivial⟩, h.2⟩

/-- One faithful event's effect on the cache: a pin prepends its pair, any other event leaves
it. -/
private theorem cache_replayEvent (s : BuilderReductionState F) (e : ReductionEvent F)
    (hf : OutcomesFaithful s [e]) :
    (replayEvent s e).aux.wireState.cachedConstants =
      match e with
      | .equal _ (.pinned v k _) => (k, v) :: s.aux.wireState.cachedConstants
      | _ => s.aux.wireState.cachedConstants := by
  cases e with
  | alloc v ex =>
    show ((createInternalVariable ex : PlonkBuilder F Variable) s).2.aux.wireState.cachedConstants
      = _
    rw [createInternalVariable_apply]
  | generic g =>
    show ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.aux.wireState.cachedConstants
      = _
    rw [addGenericPlonkConstraint_apply]
    cases s.aux.queuedGenericGate <;> rfl
  | equal c o =>
    have ho : o = outcomeOf c s.aux.wireState.cachedConstants := hf.1
    rw [replayEvent_equal s c ho]
    cases o with
    | merge l r => rfl
    | cached l v k => rfl
    | trivial => rfl
    | row g =>
      show ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.aux.wireState.cachedConstants
        = _
      rw [addGenericPlonkConstraint_apply]
      cases s.aux.queuedGenericGate <;> rfl
    | pinned v k g =>
      show (k, v) ::
        ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.aux.wireState.cachedConstants = _
      rw [addGenericPlonkConstraint_apply]
      cases s.aux.queuedGenericGate <;> rfl

/-- A faithful log's replay extends the cache by exactly its pins. -/
theorem cache_replay {s : BuilderReductionState F} {es : List (ReductionEvent F)}
    (hf : OutcomesFaithful s es) :
    (replay s es).aux.wireState.cachedConstants = pinsOf es ++ s.aux.wireState.cachedConstants := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨hf1, hf2⟩ := outcomesFaithful_cons hf
    have hstep : replay s (e :: es) = replay (replayEvent s e) es := rfl
    rw [hstep, ih hf2, cache_replayEvent s e hf1]
    cases e with
    | alloc v ex => rfl
    | generic g => rfl
    | equal c o =>
      cases o with
      | merge l r => rfl
      | cached l v k => rfl
      | trivial => rfl
      | row g => rfl
      | pinned v k g => simp [pinsOf]

/-- A faithful log's cache hit names a pin of the log or of the starting cache. -/
theorem cached_mem {s : BuilderReductionState F} {es : List (ReductionEvent F)}
    (hf : OutcomesFaithful s es) {c : EqualsConstraint F} {l v : Variable} {k : F}
    (he : .equal c (.cached l v k) ∈ es) :
    (k, v) ∈ pinsOf es ∨ (k, v) ∈ s.aux.wireState.cachedConstants := by
  induction es generalizing s with
  | nil => exact (List.not_mem_nil he).elim
  | cons e es ih =>
    obtain ⟨hf1, hf2⟩ := outcomesFaithful_cons hf
    rcases List.mem_cons.mp he with rfl | he
    · exact Or.inr (outcomeOf_cached_mem hf1.1.symm)
    · rcases ih hf2 he with h | h
      · left
        cases e with
        | alloc v ex => exact h
        | generic g => exact h
        | equal c' o =>
          cases o with
          | merge l r => exact h
          | cached l v k => exact h
          | trivial => exact h
          | row g => exact h
          | pinned v' k' g => exact List.mem_append_left _ h
      · rw [cache_replayEvent s e hf1] at h
        cases e with
        | alloc v ex => exact Or.inr h
        | generic g => exact Or.inr h
        | equal c' o =>
          cases o with
          | merge l r => exact Or.inr h
          | cached l v k => exact Or.inr h
          | trivial => exact Or.inr h
          | row g => exact Or.inr h
          | pinned v' k' g =>
            rcases List.mem_cons.mp h with h | h
            · exact Or.inl (h ▸ List.mem_append_right _ (List.mem_singleton_self _))
            · exact Or.inr h

/-- A faithful log's equality event logs the equality op's decision at some cache. -/
theorem outcomeOf_of_mem {s : BuilderReductionState F} {es : List (ReductionEvent F)}
    (hf : OutcomesFaithful s es) {c : EqualsConstraint F} {o : EqualOutcome F}
    (he : ReductionEvent.equal c o ∈ es) : ∃ cache, outcomeOf c cache = o := by
  induction es generalizing s with
  | nil => exact (List.not_mem_nil he).elim
  | cons e es ih =>
    obtain ⟨hf1, hf2⟩ := outcomesFaithful_cons hf
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, hf1.1.symm⟩
    · exact ih hf2 he

omit [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F] in
/-- A pin of a log is one of its pinning events. -/
theorem mem_pinsOf {es : List (ReductionEvent F)} {k : F} {v : Variable}
    (h : (k, v) ∈ pinsOf es) : ∃ c g, ReductionEvent.equal c (.pinned v k g) ∈ es := by
  induction es with
  | nil => exact (List.not_mem_nil h).elim
  | cons e es ih =>
    have step : (k, v) ∈ pinsOf es →
        ∃ c g, ReductionEvent.equal c (.pinned v k g) ∈ e :: es := fun h' =>
      let ⟨c, g, hm⟩ := ih h'
      ⟨c, g, List.mem_cons_of_mem _ hm⟩
    cases e with
    | alloc _ _ => exact step h
    | generic _ => exact step h
    | equal c o =>
      cases o with
      | merge _ _ => exact step h
      | cached _ _ _ => exact step h
      | row _ => exact step h
      | trivial => exact step h
      | pinned v' k' g =>
        simp only [pinsOf] at h
        rcases List.mem_append.mp h with h | h
        · exact step h
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp h)
          exact ⟨c, g, List.mem_cons_self ..⟩

/-! ## The classes a log fuses -/

/-- The pairs a log fuses: a merge's two variables, and a cache hit's variable with the cached
one. -/
def fusions : List (ReductionEvent F) → List (Variable × Variable)
  | [] => []
  | .equal _ (.merge l r) :: es => (l, r) :: fusions es
  | .equal _ (.cached l v _) :: es => (l, v) :: fusions es
  | _ :: es => fusions es

/-- The variables an event names: an allocation's variable, a generic constraint's cells, an
equality's outcome names. -/
def ReductionEvent.names : ReductionEvent F → List Variable
  | .alloc v _ => [v]
  | .generic g => g.vars
  | .equal _ o => o.names

/-- The generic equation an event queued, if any: a generic constraint, or the row an
equality's outcome queued. -/
def ReductionEvent.queued? : ReductionEvent F → Option (GenericPlonkConstraint F)
  | .generic g => some g
  | .equal _ (.pinned _ _ g) => some g
  | .equal _ (.row g) => some g
  | _ => none

/-- The variables a log allocates, in order. -/
def allocs (es : List (ReductionEvent F)) : List Variable :=
  es.filterMap fun
    | .alloc v _ => some v
    | _ => none

omit [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F] in
theorem allocs_append (es₁ es₂ : List (ReductionEvent F)) :
    allocs (es₁ ++ es₂) = allocs es₁ ++ allocs es₂ :=
  List.filterMap_append

/-- One event's effect on the counter: an allocation advances it, any other event leaves it. -/
private theorem nextVariable_replayEvent (s : BuilderReductionState F) (e : ReductionEvent F) :
    (replayEvent s e).nextVariable =
      match e with
      | .alloc _ _ => s.nextVariable + 1
      | _ => s.nextVariable := by
  cases e with
  | alloc v ex =>
    show ((createInternalVariable ex : PlonkBuilder F Variable) s).2.nextVariable = _
    rw [createInternalVariable_apply]
  | generic g =>
    show ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.nextVariable = _
    rw [addGenericPlonkConstraint_apply]
    cases s.aux.queuedGenericGate <;> rfl
  | equal c o =>
    show ((addEqualsConstraint c : PlonkBuilder F Unit) s).2.nextVariable = _
    rw [addEqualsConstraint_apply]
    cases outcomeOf c s.aux.wireState.cachedConstants with
    | merge l r => rfl
    | cached l v k => rfl
    | trivial => rfl
    | row g =>
      show ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.nextVariable = _
      rw [addGenericPlonkConstraint_apply]
      cases s.aux.queuedGenericGate <;> rfl
    | pinned v k g =>
      show ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.nextVariable = _
      rw [addGenericPlonkConstraint_apply]
      cases s.aux.queuedGenericGate <;> rfl

/-- A log with fresh allocations allocates at or above its starting counter and ends there or
above. -/
theorem allocs_ge {s : BuilderReductionState F} {es : List (ReductionEvent F)}
    (hfresh : AllocationsFresh s es) :
    (∀ v ∈ allocs es, s.nextVariable ≤ v) ∧ s.nextVariable ≤ (replay s es).nextVariable := by
  induction es generalizing s with
  | nil => exact ⟨fun _ h => (List.not_mem_nil h).elim, Nat.le_refl _⟩
  | cons e es ih =>
    have hstep : replay s (e :: es) = replay (replayEvent s e) es := rfl
    rw [hstep]
    cases e with
    | alloc v ex =>
      obtain ⟨rfl, hfresh'⟩ := hfresh
      obtain ⟨ih1, ih2⟩ := ih hfresh'
      simp only [nextVariable_replayEvent] at ih1 ih2
      refine ⟨fun w hw => ?_, Nat.le_of_succ_le ih2⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (ih1 w hw)
    | generic g =>
      obtain ⟨ih1, ih2⟩ := ih hfresh
      simp only [nextVariable_replayEvent] at ih1 ih2
      exact ⟨ih1, ih2⟩
    | equal c o =>
      obtain ⟨ih1, ih2⟩ := ih hfresh
      simp only [nextVariable_replayEvent] at ih1 ih2
      exact ⟨ih1, ih2⟩

omit [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F] in
private theorem fusions_cons (e : ReductionEvent F) (es : List (ReductionEvent F)) :
    fusions (e :: es) = fusions [e] ++ fusions es := by
  cases e with
  | alloc _ _ => rfl
  | generic _ => rfl
  | equal c o => cases o <;> rfl

/-- One faithful event from an invariant union-find: the invariant holds after it, no class
splits, and the fusion it logs, if any, is one class after it. -/
private theorem classes_replayEvent (s : BuilderReductionState F) (e : ReductionEvent F)
    (hf : OutcomesFaithful s [e]) (hinv : UnionFind.Inv s.aux.wireState.unionFind) :
    UnionFind.Inv (replayEvent s e).aux.wireState.unionFind ∧
      (∀ v w, s.aux.wireState.unionFind.Same v w →
        (replayEvent s e).aux.wireState.unionFind.Same v w) ∧
      ∀ p ∈ fusions [e], (replayEvent s e).aux.wireState.unionFind.Same p.1 p.2 := by
  cases e with
  | alloc v ex =>
    have h : (replayEvent s (.alloc v ex)).aux.wireState.unionFind =
        (s.aux.wireState.unionFind.find s.nextVariable).2 := by
      show ((createInternalVariable ex : PlonkBuilder F Variable) s).2.aux.wireState.unionFind = _
      rw [createInternalVariable_apply]
    rw [h]
    exact ⟨UnionFind.find_inv hinv _, fun _ _ hvw => UnionFind.same_find_mono hinv hvw _,
      fun _ hp => (List.not_mem_nil hp).elim⟩
  | generic g =>
    have h : (replayEvent s (.generic g)).aux.wireState.unionFind =
        s.aux.wireState.unionFind := by
      show ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.aux.wireState.unionFind = _
      rw [addGenericPlonkConstraint_apply]
      cases s.aux.queuedGenericGate <;> rfl
    rw [h]
    exact ⟨hinv, fun _ _ hvw => hvw, fun _ hp => (List.not_mem_nil hp).elim⟩
  | equal c o =>
    have ho : o = outcomeOf c s.aux.wireState.cachedConstants := hf.1
    rw [replayEvent_equal s c ho]
    cases o with
    | merge l r =>
      exact ⟨UnionFind.union_inv hinv l r, fun _ _ hvw => UnionFind.same_union_mono hinv hvw l r,
        fun p hp => by
          rw [List.mem_singleton.mp hp]
          exact UnionFind.same_union_self hinv l r⟩
    | cached l v k =>
      exact ⟨UnionFind.union_inv hinv l v, fun _ _ hvw => UnionFind.same_union_mono hinv hvw l v,
        fun p hp => by
          rw [List.mem_singleton.mp hp]
          exact UnionFind.same_union_self hinv l v⟩
    | trivial => exact ⟨hinv, fun _ _ hvw => hvw, fun _ hp => (List.not_mem_nil hp).elim⟩
    | row g =>
      have h : (applyOutcome (.row g) s).aux.wireState.unionFind = s.aux.wireState.unionFind := by
        show ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.aux.wireState.unionFind = _
        rw [addGenericPlonkConstraint_apply]
        cases s.aux.queuedGenericGate <;> rfl
      rw [h]
      exact ⟨hinv, fun _ _ hvw => hvw, fun _ hp => (List.not_mem_nil hp).elim⟩
    | pinned v k g =>
      have h : (applyOutcome (.pinned v k g) s).aux.wireState.unionFind =
          s.aux.wireState.unionFind := by
        show ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.aux.wireState.unionFind = _
        rw [addGenericPlonkConstraint_apply]
        cases s.aux.queuedGenericGate <;> rfl
      rw [h]
      exact ⟨hinv, fun _ _ hvw => hvw, fun _ hp => (List.not_mem_nil hp).elim⟩

/-- A faithful log from an invariant union-find: the invariant holds at the end, no class splits,
and every fusion the log records is one class at the end. -/
private theorem classes_replay {s : BuilderReductionState F} {es : List (ReductionEvent F)}
    (hinv : UnionFind.Inv s.aux.wireState.unionFind) (hf : OutcomesFaithful s es) :
    UnionFind.Inv (replay s es).aux.wireState.unionFind ∧
      (∀ v w, s.aux.wireState.unionFind.Same v w →
        (replay s es).aux.wireState.unionFind.Same v w) ∧
      ∀ p ∈ fusions es, (replay s es).aux.wireState.unionFind.Same p.1 p.2 := by
  induction es generalizing s with
  | nil => exact ⟨hinv, fun _ _ h => h, fun _ h => (List.not_mem_nil h).elim⟩
  | cons e es ih =>
    obtain ⟨hf1, hf2⟩ := outcomesFaithful_cons hf
    obtain ⟨hinv', hmono', hfus'⟩ := classes_replayEvent s e hf1 hinv
    obtain ⟨ih1, ih2, ih3⟩ := ih hinv' hf2
    refine ⟨ih1, fun v w h => ih2 v w (hmono' v w h), fun p hp => ?_⟩
    rw [fusions_cons] at hp
    rcases List.mem_append.mp hp with h | h
    · exact ih2 p.1 p.2 (hfus' p h)
    · exact ih3 p h

/-- A faithful log replayed from an invariant union-find keeps the invariant. -/
theorem inv_replay {s : BuilderReductionState F} {es : List (ReductionEvent F)}
    (hinv : UnionFind.Inv s.aux.wireState.unionFind) (hf : OutcomesFaithful s es) :
    UnionFind.Inv (replay s es).aux.wireState.unionFind :=
  (classes_replay hinv hf).1

/-- A faithful log never splits a class. -/
theorem same_replay_mono {s : BuilderReductionState F} {es : List (ReductionEvent F)}
    (hinv : UnionFind.Inv s.aux.wireState.unionFind) (hf : OutcomesFaithful s es) {v w : Variable}
    (h : s.aux.wireState.unionFind.Same v w) : (replay s es).aux.wireState.unionFind.Same v w :=
  (classes_replay hinv hf).2.1 v w h

/-- Every fusion a faithful log records is one class once the log is replayed. -/
theorem same_replay {s : BuilderReductionState F} {es : List (ReductionEvent F)}
    (hinv : UnionFind.Inv s.aux.wireState.unionFind) (hf : OutcomesFaithful s es)
    {p : Variable × Variable} (hp : p ∈ fusions es) :
    (replay s es).aux.wireState.unionFind.Same p.1 p.2 :=
  (classes_replay hinv hf).2.2 p hp

/-! ## Erasure -/

/-- A recording computation simulates a builder computation: from every recording state it
returns the builder's result, carries the builder's state as its core, and appends the events
whose replay is the builder's state change, whose allocations log the counter, and whose
equalities log their outcomes. -/
private def Simulates (b : PlonkBuilder F α) (r : RecordingBuilder F α) : Prop :=
  ∀ s : RecordingState F, (r s).1 = (b s.core).1 ∧ (r s).2.core = (b s.core).2 ∧
    ∃ es, (r s).2.eventsRev = es.reverse ++ s.eventsRev ∧ (b s.core).2 = replay s.core es ∧
      AllocationsFresh s.core es ∧ OutcomesFaithful s.core es

private theorem simulates_pure (a : α) : Simulates (pure a : PlonkBuilder F α) (pure a) :=
  fun _ => ⟨rfl, rfl, [], rfl, rfl, trivial, trivial⟩

private theorem simulates_map {b : PlonkBuilder F α} {r : RecordingBuilder F α} (f : α → β)
    (hb : Simulates b r) : Simulates (f <$> b) (f <$> r) := by
  intro s
  obtain ⟨h1, h2, es, h3, h4, h5, h6⟩ := hb s
  show f (r s).1 = f (b s.core).1 ∧ (r s).2.core = (b s.core).2 ∧
    ∃ es, (r s).2.eventsRev = es.reverse ++ s.eventsRev ∧ (b s.core).2 = replay s.core es ∧
      AllocationsFresh s.core es ∧ OutcomesFaithful s.core es
  rw [h1]
  exact ⟨rfl, h2, es, h3, h4, h5, h6⟩

private theorem simulates_bind {b : PlonkBuilder F α} {r : RecordingBuilder F α}
    {f : α → PlonkBuilder F β} {g : α → RecordingBuilder F β}
    (hb : Simulates b r) (hf : ∀ x, Simulates (f x) (g x)) :
    Simulates (b >>= f) (r >>= g) := by
  intro s
  obtain ⟨h1, h2, es₁, h3, h4, h9, h11⟩ := hb s
  obtain ⟨h5, h6, es₂, h7, h8, h10, h12⟩ := hf (r s).1 (r s).2
  show (g (r s).1 (r s).2).1 = (f (b s.core).1 (b s.core).2).1 ∧
    (g (r s).1 (r s).2).2.core = (f (b s.core).1 (b s.core).2).2 ∧
    ∃ es, (g (r s).1 (r s).2).2.eventsRev = es.reverse ++ s.eventsRev ∧
      (f (b s.core).1 (b s.core).2).2 = replay s.core es ∧ AllocationsFresh s.core es ∧
        OutcomesFaithful s.core es
  refine ⟨?_, ?_, es₁ ++ es₂, ?_, ?_, ?_, ?_⟩
  · rw [h5, h2, h1]
  · rw [h6, h2, h1]
  · rw [h7, h3, List.reverse_append, List.append_assoc]
  · rw [← h1, ← h2, h8, h2, h4, replay_append]
  · rw [allocationsFresh_append]
    refine ⟨h9, ?_⟩
    rw [← h4, ← h2]
    exact h10
  · rw [outcomesFaithful_append]
    refine ⟨h11, ?_⟩
    rw [← h4, ← h2]
    exact h12

private theorem simulates_createInternalVariable (e : AffineExpression F) :
    Simulates (createInternalVariable e : PlonkBuilder F Variable)
      (createInternalVariable e) :=
  fun _ => ⟨rfl, rfl, [.alloc _ e], rfl, rfl, ⟨rfl, trivial⟩, trivial⟩

private theorem simulates_addGenericPlonkConstraint (g : GenericPlonkConstraint F) :
    Simulates (addGenericPlonkConstraint g : PlonkBuilder F Unit)
      (addGenericPlonkConstraint g) :=
  fun _ => ⟨rfl, rfl, [.generic g], rfl, rfl, trivial, trivial⟩

private theorem simulates_addEqualsConstraint (c : EqualsConstraint F) :
    Simulates (addEqualsConstraint c : PlonkBuilder F Unit) (addEqualsConstraint c) :=
  fun s => ⟨rfl, rfl, [.equal c (outcomeOf c s.core.aux.wireState.cachedConstants)], rfl, rfl,
    trivial, rfl, trivial⟩

/-- Close a simulation goal by walking the reducer's structure: an operation or `pure` closes
the goal, a `bind` splits into the simulations of its two parts, and a `match` or `if` is
cased on. Further closers, such as an induction hypothesis for a recursive reducer, are
supplied as `simulates [h₁, h₂]`. -/
local syntax "simulates" (" [" term,* "]")? : tactic

local macro_rules
  | `(tactic| simulates) => `(tactic| simulates [])
  | `(tactic| simulates [$ts,*]) => `(tactic|
      repeat first
        | exact simulates_pure _
        | exact simulates_createInternalVariable _
        | exact simulates_addGenericPlonkConstraint _
        | exact simulates_addEqualsConstraint _
        $[| exact $ts]*
        | refine simulates_bind ?_ fun _ => ?_
        | refine simulates_map _ ?_
        | split)

/-- A simulating recording erases to the builder's run from the same counter and auxiliary
state. -/
private theorem erase_recordReduction {b : PlonkBuilder F α} {r : RecordingBuilder F α}
    (h : Simulates b r) (nv : Variable) (aux : AuxState F) :
    (recordReduction nv aux r).erase = reduceAsBuilder nv aux b := by
  obtain ⟨h1, h2, -⟩ := h ⟨⟨[], nv, aux⟩, []⟩
  show ((r _).1, ((r _).2.core.constraints.reverse.map Rows.mk), (r _).2.core.nextVariable,
      (r _).2.core.aux) =
    ((b _).1, ((b _).2.constraints.reverse.map Rows.mk), (b _).2.nextVariable, (b _).2.aux)
  rw [h1, h2]

/-- A simulating recording's final state is the replay of its events from its start. -/
private theorem finish_recordReduction {b : PlonkBuilder F α} {r : RecordingBuilder F α}
    (h : Simulates b r) (nv : Variable) (aux : AuxState F) :
    (recordReduction nv aux r).finish =
      replay ⟨[], nv, aux⟩ (recordReduction nv aux r).events := by
  obtain ⟨-, h2, es, h3, h4, -, -⟩ := h ⟨⟨[], nv, aux⟩, []⟩
  show (⟨(((r _).2.core.constraints.reverse.map Rows.mk).map (·.row)).reverse,
      (r _).2.core.nextVariable, (r _).2.core.aux⟩ : BuilderReductionState F) =
    replay ⟨[], nv, aux⟩ ((r _).2.eventsRev.reverse)
  rw [h3, List.append_nil, List.reverse_reverse, ← h4, ← h2, List.map_map]
  have hid : ((fun x : Rows F => x.row) ∘ Rows.mk) = id := rfl
  rw [hid, List.map_id, List.reverse_reverse]

/-- A simulating recording's allocations log the counter at their points. -/
private theorem allocations_recordReduction {b : PlonkBuilder F α} {r : RecordingBuilder F α}
    (h : Simulates b r) (nv : Variable) (aux : AuxState F) :
    AllocationsFresh ⟨[], nv, aux⟩ (recordReduction nv aux r).events := by
  obtain ⟨-, -, es, h3, -, h5, -⟩ := h ⟨⟨[], nv, aux⟩, []⟩
  show AllocationsFresh ⟨[], nv, aux⟩ ((r _).2.eventsRev.reverse)
  rw [h3, List.append_nil, List.reverse_reverse]
  exact h5

/-- A simulating recording's equalities log the equality op's decisions at their points. -/
private theorem outcomes_recordReduction {b : PlonkBuilder F α} {r : RecordingBuilder F α}
    (h : Simulates b r) (nv : Variable) (aux : AuxState F) :
    OutcomesFaithful ⟨[], nv, aux⟩ (recordReduction nv aux r).events := by
  obtain ⟨-, -, es, h3, -, -, h6⟩ := h ⟨⟨[], nv, aux⟩, []⟩
  show OutcomesFaithful ⟨[], nv, aux⟩ ((r _).2.eventsRev.reverse)
  rw [h3, List.append_nil, List.reverse_reverse]
  exact h6

section Reducers

variable [Add F] [Mul F] [One F]

omit [Add F] [Mul F] in
private theorem simulates_completelyReduce (single : Variable × F) :
    (l : List (Variable × F)) →
      Simulates (completelyReduce single l : PlonkBuilder F (Variable × F))
        (completelyReduce single l)
  | [] => simulates_pure _
  | next :: rest => by
    unfold completelyReduce
    simulates [simulates_completelyReduce next rest]

omit [Add F] [Mul F] in
private theorem simulates_reduceAffineExpression (ae : AffineExpression F) :
    Simulates (reduceAffineExpression ae : PlonkBuilder F (Option Variable × F))
      (reduceAffineExpression ae) := by
  unfold reduceAffineExpression
  simulates [simulates_completelyReduce _ _]

private theorem simulates_reduceToVariable (x : CVar F) :
    Simulates (reduceToVariable x : PlonkBuilder F Variable) (reduceToVariable x) := by
  unfold reduceToVariable
  simulates [simulates_reduceAffineExpression _]

/-- The `Basic` reducer simulates in every arm: each operand reduction simulates, and the
surviving shape's one emission is an operation or nothing. -/
private theorem simulates_reduce (c : Basic F) :
    Simulates (reduce c : PlonkBuilder F Unit) (reduce c) := by
  cases c <;> unfold reduce <;> simulates [simulates_reduceAffineExpression _]

private theorem simulates_reduceAffinePoint (p : AffinePoint (FVar F)) :
    Simulates (reduceAffinePoint p : PlonkBuilder F (AffinePoint Variable))
      (reduceAffinePoint p) := by
  unfold reduceAffinePoint
  simulates [simulates_reduceToVariable _]

private theorem simulates_addComplete_reduce (c : AddComplete F) :
    Simulates (c.reduce : PlonkBuilder F (Rows F)) c.reduce := by
  unfold AddComplete.reduce
  simulates [simulates_reduceAffinePoint _, simulates_reduceToVariable _]

/-- Recording `reduceToVariable` erases to its ordinary reduction. -/
theorem record_reduceToVariable_erases (nv : Variable) (aux : AuxState F) (x : CVar F) :
    (recordReduction nv aux (reduceToVariable x)).erase =
      reduceAsBuilder nv aux (reduceToVariable x) :=
  erase_recordReduction (simulates_reduceToVariable x) nv aux

/-- Recording a `Basic` constraint's reduction, Booleanity included, erases to its ordinary
reduction. -/
theorem record_basic_erases (nv : Variable) (aux : AuxState F) (c : Basic F) :
    (recordReduction nv aux (reduce c)).erase = reduceAsBuilder nv aux (reduce c) :=
  erase_recordReduction (simulates_reduce c) nv aux

/-- Recording a complete addition's reduction erases to its ordinary reduction. -/
theorem record_addComplete_erases (nv : Variable) (aux : AuxState F) (c : AddComplete F) :
    (recordReduction nv aux c.reduce).erase = reduceAsBuilder nv aux c.reduce :=
  erase_recordReduction (simulates_addComplete_reduce c) nv aux

private theorem simulates_scaleRound_reduce (c : ScaleRound F) :
    Simulates (c.reduce : PlonkBuilder F (KimchiRow F × KimchiRow F)) c.reduce := by
  unfold ScaleRound.reduce
  simulates [simulates_reduceToVariable _]

private theorem simulates_varBaseMul_reduce :
    (c : VarBaseMul F) →
      Simulates (VarBaseMul.reduce c : PlonkBuilder F (List (KimchiRow F × KimchiRow F)))
        (VarBaseMul.reduce c)
  | [] => simulates_pure _
  | round :: rest => by
    unfold VarBaseMul.reduce
    simulates [simulates_scaleRound_reduce _, simulates_varBaseMul_reduce rest]

private theorem simulates_endoScalarRound_reduce (c : EndoScalarRound F) :
    Simulates (c.reduce : PlonkBuilder F (KimchiRow F)) c.reduce := by
  unfold EndoScalarRound.reduce
  simulates [simulates_reduceToVariable _]

private theorem simulates_endoScalar_reduce :
    (c : EndoScalar F) →
      Simulates (EndoScalar.reduce c : PlonkBuilder F (List (KimchiRow F))) (EndoScalar.reduce c)
  | [] => simulates_pure _
  | round :: rest => by
    unfold EndoScalar.reduce
    simulates [simulates_endoScalarRound_reduce _, simulates_endoScalar_reduce rest]

private theorem simulates_endoMulRound_reduce (c : EndoMulRound F) :
    Simulates (c.reduce : PlonkBuilder F (KimchiRow F)) c.reduce := by
  unfold EndoMulRound.reduce
  simulates [simulates_reduceToVariable _]

private theorem simulates_endoMul_reduceRounds :
    (rounds : List (EndoMulRound F)) →
      Simulates (EndoMul.reduceRounds rounds : PlonkBuilder F (List (KimchiRow F)))
        (EndoMul.reduceRounds rounds)
  | [] => simulates_pure _
  | round :: rest => by
    unfold EndoMul.reduceRounds
    simulates [simulates_endoMulRound_reduce _, simulates_endoMul_reduceRounds rest]

private theorem simulates_endoMul_reduce (c : EndoMul F) :
    Simulates (c.reduce : PlonkBuilder F (List (KimchiRow F))) c.reduce := by
  unfold EndoMul.reduce
  simulates [simulates_reduceToVariable _, simulates_endoMul_reduceRounds _]

private theorem simulates_reduceState (t : FVar F × FVar F × FVar F) :
    Simulates (reduceState t : PlonkBuilder F (Variable × Variable × Variable))
      (reduceState t) := by
  unfold reduceState
  simulates [simulates_reduceToVariable _]

private theorem simulates_reduceStates :
    (ts : List (FVar F × FVar F × FVar F)) →
      Simulates (reduceStates ts : PlonkBuilder F (List (Variable × Variable × Variable)))
        (reduceStates ts)
  | [] => simulates_pure _
  | t :: rest => by
    unfold reduceStates
    simulates [simulates_reduceState _, simulates_reduceStates rest]

private theorem simulates_poseidon_reduce (c : PoseidonConstraint F) :
    Simulates (c.reduce : PlonkBuilder F (List (KimchiRow F))) c.reduce := by
  unfold PoseidonConstraint.reduce
  simulates [simulates_reduceStates _]

private theorem simulates_reducePad (vs : Vector (FVar F) 7) :
    Simulates (reducePad vs : PlonkBuilder F (Rows F)) (reducePad vs) := by
  unfold reducePad
  simulates [simulates_reduceToVariable _]

/-- The dispatch over every constraint simulates: each arm is its gate's reducer, wrapped. -/
private theorem simulates_constraint_reduce (c : KimchiConstraint F) :
    Simulates (c.reduce : PlonkBuilder F (KimchiGate F)) c.reduce := by
  cases c <;> unfold KimchiConstraint.reduce <;>
    simulates [simulates_reduce _, simulates_addComplete_reduce _, simulates_poseidon_reduce _,
      simulates_varBaseMul_reduce _, simulates_endoScalar_reduce _, simulates_endoMul_reduce _,
      simulates_reducePad _]

/-- Recording any constraint's reduction erases to its ordinary reduction. -/
theorem record_constraint_erases (nv : Variable) (aux : AuxState F) (c : KimchiConstraint F) :
    (recordReduction nv aux c.reduce).erase = reduceAsBuilder nv aux c.reduce :=
  erase_recordReduction (simulates_constraint_reduce c) nv aux

/-- Recording any constraint's reduction ends in the replay of its events from its start. -/
theorem record_constraint_replays (nv : Variable) (aux : AuxState F) (c : KimchiConstraint F) :
    (recordReduction nv aux c.reduce).finish =
      replay ⟨[], nv, aux⟩ (recordReduction nv aux c.reduce).events :=
  finish_recordReduction (simulates_constraint_reduce c) nv aux

/-- Recording any constraint's reduction logs each allocation's variable as the counter at
its point. -/
theorem record_constraint_allocates (nv : Variable) (aux : AuxState F)
    (c : KimchiConstraint F) :
    AllocationsFresh ⟨[], nv, aux⟩ (recordReduction nv aux c.reduce).events :=
  allocations_recordReduction (simulates_constraint_reduce c) nv aux

/-- Recording any constraint's reduction logs each equality's outcome as the equality op's
decision at its point. -/
theorem record_constraint_decides (nv : Variable) (aux : AuxState F) (c : KimchiConstraint F) :
    OutcomesFaithful ⟨[], nv, aux⟩ (recordReduction nv aux c.reduce).events :=
  outcomes_recordReduction (simulates_constraint_reduce c) nv aux

end Reducers

end Replay

end Snarky.Kimchi
