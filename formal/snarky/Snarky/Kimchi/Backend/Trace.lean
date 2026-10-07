import Snarky.Kimchi.Constraint

/-!
# The lowering trace

The builder's reduction with its provenance kept: which reduction operations a constraint's
reducer invoked, in execution order.
The data is compiler-internal, naming no index and no gate semantics. The recording
interpreter runs the existing polymorphic reducers unchanged: each operation delegates to the
builder's and logs its payload, so a recorded reduction is the existing lowering beside its
history, and `RecordedReduction.erase` returns exactly what `reduceAsBuilder` returns.

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

## Main results

- `record_reduceToVariable_erases`, `record_basic_erases`, `record_addComplete_erases`: the
  reducers the direct fragment and its operands run, recorded, erase to their ordinary
  reductions; `record_constraint_erases` is the same for the dispatch over every constraint.
- `record_constraint_replays`, `record_constraint_allocates`, `record_constraint_decides`: a
  recorded reduction ends in the replay of its own events, whose allocations log the counter
  and whose equalities log their outcomes.
- `replayEvent_equal`: a faithful equality event replays as its outcome's effect.

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
