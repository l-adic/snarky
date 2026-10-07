import Snarky.Kimchi.Backend.Trace
import Snarky.Kimchi.Semantics
import Kimchi.Lift
import Kimchi.Columns

/-!
# The events' reading

What a reduction event means at a valuation, and that a reducer's events force its source
constraint. A generic event reads as its equation with an absent cell contributing `0`; an
equality reads as its two sides with an absent side standing for `1`; an allocation asserts
nothing, because its expression is advice and only the emitted equation pins the variable.
The two `none` conventions differ on purpose.

## Main definitions

- `genericValue`, `equalsHolds`, `ReductionEvent.Holds`, `ReductionFacts`: the readings.
- `rowValues`: a named row's cells at a valuation, an absent cell reading `0`.
- `CVar.termVars`, `Basic.termVars`, `KimchiConstraint.termVars`: the variables an operand's
  affine form, a `Basic` constraint and a constraint name, with repetition.

## Main results

- `reduceToVariable_reads`: when the recorded events hold, the pinned variable reads as the
  operand.
- `boolean_of_reductionFacts`: when the recorded events hold, the Boolean holds.
- `addComplete_read_eq`: when the recorded events hold, the emitted row read cell by cell is
  the gate's witness at the operands' values; `addComplete_holds_of_reductionFacts` transports
  the gate's predicate across it to the source constraint.
- `equalsHolds_of_merge`, `equalsHolds_of_cached`, `equalsHolds_of_pinned`,
  `equalsHolds_of_row`, `equalsHolds_of_trivial`: an equality holds once the fact its logged
  outcome names holds, a merge or cache hit by class, a pin or row by its emitted equation.
- `basic_names`, `addComplete_names`: the names of a constraint's recorded reduction are terms
  of its operands or its allocations; an addition's row cells are its operands' variables,
  position by position, a bare operand's being itself.
- `basic_absentZero`, `addComplete_absentZero`: every equation a constraint's recorded
  reduction queues carries no coefficient on an absent cell.
- `basic_of_reductionFacts`: when the recorded events hold, any `Basic` constraint holds.

## Implementation notes

Each lemma's premise, that the recorded events hold, stays a premise: later phases derive it
from a satisfying table. The proofs walk the reducers with a file-local relation that names
the events a computation appends from any state, composed along `pure`, `bind` and the three
operations, with an induction for `completelyReduce`; the reducers' arithmetic is read off
the emitted equations with `CVar.reduce_val`.
-/

open Kimchi

namespace Snarky.Kimchi

open Snarky

variable {F α β : Type}

/-! ## The readings -/

section Readings

variable [Add F] [Mul F] [Zero F] [One F]

/-- A generic event's equation at a valuation, an absent cell reading `0`. -/
def genericValue (V : Valuation F) (g : GenericPlonkConstraint F) : F :=
  let l := (g.vl.map V).getD 0
  let r := (g.vr.map V).getD 0
  let o := (g.vo.map V).getD 0
  g.cl * l + g.cr * r + g.co * o + g.m * (l * r) + g.c

/-- An equality event at a valuation, an absent side standing for `1`. -/
def equalsHolds (V : Valuation F) (e : EqualsConstraint F) : Prop :=
  e.cl * (e.vl.map V).getD 1 = e.cr * (e.vr.map V).getD 1

/-- An event at a valuation: a generic equation vanishes, an equality holds, an allocation
asserts nothing. -/
def ReductionEvent.Holds (V : Valuation F) : ReductionEvent F → Prop
  | .alloc _ _ => True
  | .generic g => genericValue V g = 0
  | .equal e _ => equalsHolds V e

/-- Every event of a list holds at the valuation. -/
def ReductionFacts (V : Valuation F) (events : List (ReductionEvent F)) : Prop :=
  ∀ e ∈ events, e.Holds V

/-- A named row's cells at a valuation, an absent cell reading `0`. -/
def rowValues (V : Valuation F) (r : KimchiRow F) : Fin wCols → F :=
  fun i => (r.vars[i].map V).getD 0

end Readings

/-! ## The event walk -/

/-- A computation appends events satisfying `P` with its result, from every state. -/
private def Records (x : RecordingBuilder F α) (P : α → List (ReductionEvent F) → Prop) :
    Prop :=
  ∀ s : RecordingState F, ∃ es, (x s).2.eventsRev = es.reverse ++ s.eventsRev ∧ P (x s).1 es

private theorem records_pure {P : α → List (ReductionEvent F) → Prop} (a : α) (h : P a []) :
    Records (pure a : RecordingBuilder F α) P :=
  fun _ => ⟨[], rfl, h⟩

private theorem records_mono {x : RecordingBuilder F α} {P R : α → List (ReductionEvent F) → Prop}
    (h : Records x P) (hpr : ∀ a es, P a es → R a es) : Records x R :=
  fun s => let ⟨es, h1, hp⟩ := h s; ⟨es, h1, hpr _ _ hp⟩

private theorem records_bind {x : RecordingBuilder F α} {f : α → RecordingBuilder F β}
    {P : α → List (ReductionEvent F) → Prop} {R : β → List (ReductionEvent F) → Prop}
    (hx : Records x P)
    (hf : ∀ a es₁, P a es₁ → Records (f a) fun b es₂ => R b (es₁ ++ es₂)) :
    Records (x >>= f) R := by
  intro s
  obtain ⟨es₁, h1, hp⟩ := hx s
  obtain ⟨es₂, h2, hr⟩ := hf (x s).1 es₁ hp (x s).2
  refine ⟨es₁ ++ es₂, ?_, hr⟩
  show (f (x s).1 (x s).2).2.eventsRev = (es₁ ++ es₂).reverse ++ s.eventsRev
  rw [h2, h1, List.reverse_append, List.append_assoc]

section Operations

variable [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F]

private theorem records_createInternalVariable (e : AffineExpression F) :
    Records (createInternalVariable e : RecordingBuilder F Variable)
      fun v es => es = [.alloc v e] :=
  fun _ => ⟨[.alloc _ e], rfl, rfl⟩

private theorem records_addGenericPlonkConstraint (g : GenericPlonkConstraint F) :
    Records (addGenericPlonkConstraint g : RecordingBuilder F Unit)
      fun _ es => es = [.generic g] :=
  fun _ => ⟨[.generic g], rfl, rfl⟩

private theorem records_addEqualsConstraint (c : EqualsConstraint F) :
    Records (addEqualsConstraint c : RecordingBuilder F Unit) fun _ es =>
      ∃ o cache, es = [.equal c o] ∧ outcomeOf c cache = o :=
  fun s => ⟨[.equal c (outcomeOf c s.core.aux.wireState.cachedConstants)], rfl, _, _, rfl, rfl⟩

end Operations

/-- Walk a computation's structure: a `bind` whose head is an operation or a listed lemma
continues into its tail, a `pure` or a trailing operation leaves its obligation, and a
`match` or `if` is cased on. -/
local syntax "records" (" [" term,* "]")? : tactic

local macro_rules
  | `(tactic| records) => `(tactic| records [])
  | `(tactic| records [$ts,*]) => `(tactic|
      repeat any_goals first
        | refine records_pure _ ?_
        | refine records_bind (records_createInternalVariable _) fun _ _ _ => ?_
        | refine records_bind (records_addGenericPlonkConstraint _) fun _ _ _ => ?_
        | refine records_bind (records_addEqualsConstraint _) fun _ _ _ => ?_
        $[| refine records_bind $ts fun _ _ _ => ?_]*
        | refine records_mono (records_addGenericPlonkConstraint _) fun _ _ _ => ?_
        | refine records_mono (records_addEqualsConstraint _) fun _ _ _ => ?_
        | split)

/-- What a recorded reduction's result and events satisfy, from a walk. -/
private theorem recordReduction_of_records {x : RecordingBuilder F α}
    {P : α → List (ReductionEvent F) → Prop} (h : Records x P) (nv : Variable)
    (aux : AuxState F) : P (recordReduction nv aux x).result (recordReduction nv aux x).events := by
  obtain ⟨es, h1, hp⟩ := h ⟨⟨[], nv, aux⟩, []⟩
  show P (x _).1 ((x _).2.eventsRev.reverse)
  rw [h1, List.append_nil, List.reverse_reverse]
  exact hp

/-! ## The local lemmas -/

section Reducers

variable [Field F] [DecidableEq F]

/-- The reading of a reduced affine form: `(some v, k)` as `k · V v`, `(none, k)` as `k`. -/
private def reducedValue (V : Valuation F) (r : Option Variable × F) : F :=
  match r.1 with
  | some v => r.2 * V v
  | none => r.2

omit [DecidableEq F] in
private theorem facts_append {V : Valuation F} {es₁ es₂ : List (ReductionEvent F)}
    (h : ReductionFacts V (es₁ ++ es₂)) : ReductionFacts V es₁ ∧ ReductionFacts V es₂ :=
  List.forall_mem_append.mp h

omit [DecidableEq F] in
private theorem facts_generic {V : Valuation F} {g : GenericPlonkConstraint F}
    (h : ReductionFacts V [.generic g]) : genericValue V g = 0 :=
  h _ (List.mem_singleton_self _)

omit [DecidableEq F] in
private theorem facts_equal {V : Valuation F} {e : EqualsConstraint F} {o : EqualOutcome F}
    (h : ReductionFacts V [.equal e o]) : equalsHolds V e :=
  h _ (List.mem_singleton_self _)

private theorem records_completelyReduce (single : Variable × F) :
    (l : List (Variable × F)) →
      Records (completelyReduce single l : RecordingBuilder F (Variable × F)) fun r es =>
        ∀ V : Valuation F, ReductionFacts V es →
          r.2 * V r.1 = single.2 * V single.1 + (l.map fun t => t.2 * V t.1).sum
  | [] => records_pure _ fun _ _ => by simp
  | next :: rest => by
    unfold completelyReduce
    records [records_completelyReduce next rest]
    subst_vars
    have hr := ‹∀ V : Valuation F, ReductionFacts V _ →
      _ = next.2 * V next.1 + (rest.map fun t => t.2 * V t.1).sum›
    intro V hV
    obtain ⟨h1, h2⟩ := facts_append hV
    have hg := facts_generic (facts_append (facts_append h2).2).1
    simp only [genericValue, Option.map_some, Option.getD_some] at hg
    dsimp only
    rw [List.map_cons, List.sum_cons, ← hr V h1]
    linear_combination -hg

private theorem records_reduceAffineExpression (ae : AffineExpression F) :
    Records (reduceAffineExpression ae : RecordingBuilder F (Option Variable × F)) fun r es =>
      ∀ V : Valuation F, ReductionFacts V es → reducedValue V r = ae.val V := by
  unfold reduceAffineExpression
  records [records_completelyReduce _ _]
  · intro V _
    simp [reducedValue, AffineExpression.val, *]
  · intro V _
    simp [reducedValue, AffineExpression.val, *]
  · intro V _
    simp [reducedValue, AffineExpression.val, *]
  · subst_vars
    intro V hV
    have hg := facts_generic (facts_append (facts_append hV).2).1
    simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none] at hg
    simp only [reducedValue, AffineExpression.val, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Option.getD_some, ‹ae.terms = _›, ‹ae.constant = _›]
    linear_combination -hg
  · subst_vars
    have hr := ‹∀ V : Valuation F, ReductionFacts V _ → _ * V _ = _›
    intro V hV
    obtain ⟨h1, h2⟩ := facts_append hV
    have hg := facts_generic (facts_append (facts_append h2).2).1
    simp only [genericValue, Option.map_some, Option.getD_some] at hg
    simp only [reducedValue, AffineExpression.val, List.map_cons, List.sum_cons, ‹ae.terms = _›]
    rw [← hr V h1]
    linear_combination -hg

private theorem records_reduceToVariable (x : CVar F) :
    Records (reduceToVariable x : RecordingBuilder F Variable) fun v es =>
      ∀ V : Valuation F, ReductionFacts V es → V v = x.val V := by
  unfold reduceToVariable
  records [records_reduceAffineExpression _]
  · obtain ⟨o, -, rfl, -⟩ := ‹∃ o cache, _ = [ReductionEvent.equal _ o] ∧ _›
    subst_vars
    have hr := ‹∀ V : Valuation F, ReductionFacts V _ → reducedValue V _ = _›
    have hnone := ‹_ = none›
    intro V hV
    obtain ⟨h1, h2⟩ := facts_append hV
    have he := facts_equal (facts_append (facts_append h2).2).1
    simp only [equalsHolds, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none, one_mul, mul_one] at he
    rw [he, ← CVar.reduce_val, ← hr V h1]
    simp only [reducedValue, hnone]
  · have hr := ‹∀ V : Valuation F, ReductionFacts V _ → reducedValue V _ = _›
    have hsome := ‹_ = some _›
    have hone := ‹_ = (1 : F)›
    intro V hV
    rw [← CVar.reduce_val, ← hr V (facts_append hV).1]
    simp [reducedValue, hsome, hone]
  · subst_vars
    have hr := ‹∀ V : Valuation F, ReductionFacts V _ → reducedValue V _ = _›
    have hsome := ‹_ = some _›
    intro V hV
    obtain ⟨h1, h2⟩ := facts_append hV
    have hg := facts_generic (facts_append (facts_append h2).2).1
    simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none] at hg
    rw [← CVar.reduce_val, ← hr V h1]
    simp only [reducedValue, hsome]
    linear_combination -hg

/-- When the recorded events hold at a valuation, the variable `reduceToVariable` returns
reads as the operand. -/
theorem reduceToVariable_reads (nv : Variable) (aux : AuxState F) (x : CVar F)
    (V : Valuation F) (h : ReductionFacts V (recordReduction nv aux (reduceToVariable x)).events) :
    V (recordReduction nv aux (reduceToVariable x)).result = x.val V :=
  recordReduction_of_records (records_reduceToVariable x) nv aux V h

omit [DecidableEq F] in
private theorem eq_zero_or_one_of_mul_self (y : F) (h : y * y = y) : y = 0 ∨ y = 1 := by
  have : y * (y - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

private theorem records_boolean (b : CVar F) :
    Records (reduce (.boolean b) : RecordingBuilder F Unit) fun _ es =>
      ∀ V : Valuation F, ReductionFacts V es → Basic.Holds V (.boolean b) := by
  simp only [reduce]
  records [records_reduceAffineExpression _]
  · have hr := ‹∀ V : Valuation F, ReductionFacts V _ → reducedValue V _ = _›
    have hnone := ‹_ = none›
    have hself := ‹_ * _ = _›
    intro V hV
    have hval := hr V (facts_append hV).1
    simp only [reducedValue, hnone, CVar.reduce_val] at hval
    show b.val V = 0 ∨ b.val V = 1
    rw [← hval]
    exact eq_zero_or_one_of_mul_self _ hself
  · subst_vars
    have hr := ‹∀ V : Valuation F, ReductionFacts V _ → reducedValue V _ = _›
    have hnone := ‹_ = none›
    intro V hV
    obtain ⟨h1, h2⟩ := facts_append hV
    have hg := facts_generic h2
    have hval := hr V h1
    simp only [reducedValue, hnone, CVar.reduce_val] at hval
    simp only [genericValue, Option.map_none, Option.getD_none] at hg
    show b.val V = 0 ∨ b.val V = 1
    rw [← hval]
    exact eq_zero_or_one_of_mul_self _ (by linear_combination hg)
  · subst_vars
    have hr := ‹∀ V : Valuation F, ReductionFacts V _ → reducedValue V _ = _›
    have hsome := ‹_ = some _›
    intro V hV
    obtain ⟨h1, h2⟩ := facts_append hV
    have hg := facts_generic h2
    have hval := hr V h1
    simp only [reducedValue, hsome, CVar.reduce_val] at hval
    simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none] at hg
    show b.val V = 0 ∨ b.val V = 1
    rw [← hval]
    exact eq_zero_or_one_of_mul_self _ (by linear_combination hg)

/-- When the recorded events hold at a valuation, a Boolean constraint holds there. -/
theorem boolean_of_reductionFacts (nv : Variable) (aux : AuxState F) (x : CVar F)
    (V : Valuation F) (h : ReductionFacts V (recordReduction nv aux (reduce (.boolean x))).events) :
    Basic.Holds V (.boolean x) :=
  recordReduction_of_records (records_boolean x) nv aux V h

omit [DecidableEq F] in
private theorem reducedValue_eq_of_equalsHolds {V : Valuation F} {l r : Option Variable × F}
    (he : equalsHolds V { cl := l.2, vl := l.1, cr := r.2, vr := r.1 }) :
    reducedValue V l = reducedValue V r := by
  obtain ⟨lv, lk⟩ := l
  obtain ⟨rv, rk⟩ := r
  simp only [equalsHolds] at he
  cases lv <;> cases rv <;> simpa [reducedValue] using he

private theorem records_equal (a b : CVar F) :
    Records (reduce (.equal a b) : RecordingBuilder F Unit) fun _ es =>
      ∀ V : Valuation F, ReductionFacts V es → Basic.Holds V (.equal a b) := by
  simp only [reduce]
  refine records_bind (records_reduceAffineExpression _) fun l esl hl => ?_
  refine records_bind (records_reduceAffineExpression _) fun r esr hr => ?_
  refine records_mono (records_addEqualsConstraint _) fun _ es₃ h => ?_
  obtain ⟨o, -, rfl, -⟩ := h
  intro V hV
  obtain ⟨h1, h2⟩ := facts_append hV
  obtain ⟨h2, h3⟩ := facts_append h2
  have he := facts_equal h3
  show a.val V = b.val V
  rw [← CVar.reduce_val, ← CVar.reduce_val, ← hl V h1, ← hr V h2]
  exact reducedValue_eq_of_equalsHolds he

private theorem records_square (a b : CVar F) :
    Records (reduce (.square a b) : RecordingBuilder F Unit) fun _ es =>
      ∀ V : Valuation F, ReductionFacts V es → Basic.Holds V (.square a b) := by
  simp only [reduce]
  refine records_bind (records_reduceAffineExpression _) fun x esx hx => ?_
  refine records_bind (records_reduceAffineExpression _) fun y esy hy => ?_
  split
  · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₃ h => ?_
    subst h
    intro V hV
    obtain ⟨h1, h2⟩ := facts_append hV
    obtain ⟨h2, h3⟩ := facts_append h2
    have hg := facts_generic h3
    simp only [genericValue, Option.map_some, Option.getD_some] at hg
    show a.val V * a.val V = b.val V
    rw [← CVar.reduce_val, ← CVar.reduce_val, ← hx V h1, ← hy V h2]
    simp only [reducedValue, ‹x.1 = some _›, ‹y.1 = some _›]
    linear_combination hg
  · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₃ h => ?_
    subst h
    intro V hV
    obtain ⟨h1, h2⟩ := facts_append hV
    obtain ⟨h2, h3⟩ := facts_append h2
    have hg := facts_generic h3
    simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none] at hg
    show a.val V * a.val V = b.val V
    rw [← CVar.reduce_val, ← CVar.reduce_val, ← hx V h1, ← hy V h2]
    simp only [reducedValue, ‹x.1 = some _›, ‹y.1 = none›]
    linear_combination hg
  · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₃ h => ?_
    subst h
    intro V hV
    obtain ⟨h1, h2⟩ := facts_append hV
    obtain ⟨h2, h3⟩ := facts_append h2
    have hg := facts_generic h3
    simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none] at hg
    show a.val V * a.val V = b.val V
    rw [← CVar.reduce_val, ← CVar.reduce_val, ← hx V h1, ← hy V h2]
    simp only [reducedValue, ‹x.1 = none›, ‹y.1 = some _›]
    linear_combination -hg
  · split
    · refine records_pure _ fun V hV => ?_
      obtain ⟨h1, h2⟩ := facts_append hV
      obtain ⟨h2, -⟩ := facts_append h2
      show a.val V * a.val V = b.val V
      rw [← CVar.reduce_val, ← CVar.reduce_val, ← hx V h1, ← hy V h2]
      simp only [reducedValue, ‹x.1 = none›, ‹y.1 = none›]
      exact ‹_ = _›
    · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₃ h => ?_
      subst h
      intro V hV
      obtain ⟨h1, h2⟩ := facts_append hV
      obtain ⟨h2, h3⟩ := facts_append h2
      have hg := facts_generic h3
      simp only [genericValue, Option.map_none, Option.getD_none] at hg
      show a.val V * a.val V = b.val V
      rw [← CVar.reduce_val, ← CVar.reduce_val, ← hx V h1, ← hy V h2]
      simp only [reducedValue, ‹x.1 = none›, ‹y.1 = none›]
      linear_combination hg

/-- Close an `r1cs` leaf: read the three operands through their walks and the trailing
equation, if any. -/
local macro "r1cs_leaf" hl:ident hr:ident ho:ident V:ident h4:ident : tactic => `(tactic| (
  intro $V hV
  obtain ⟨h1, h2⟩ := facts_append hV
  obtain ⟨h2, h3⟩ := facts_append h2
  obtain ⟨h3, $h4⟩ := facts_append h3
  show _ * _ = _
  rw [← CVar.reduce_val, ← CVar.reduce_val, ← CVar.reduce_val, ← $hl $V h1, ← $hr $V h2,
    ← $ho $V h3]))

private theorem records_r1cs (a b c : CVar F) :
    Records (reduce (.r1cs a b c) : RecordingBuilder F Unit) fun _ es =>
      ∀ V : Valuation F, ReductionFacts V es → Basic.Holds V (.r1cs a b c) := by
  simp only [reduce]
  refine records_bind (records_reduceAffineExpression _) fun l esl hl => ?_
  refine records_bind (records_reduceAffineExpression _) fun r esr hr => ?_
  refine records_bind (records_reduceAffineExpression _) fun o eso ho => ?_
  split
  · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
    subst h
    r1cs_leaf hl hr ho V h4
    have hg := facts_generic h4
    simp only [genericValue, Option.map_some, Option.getD_some] at hg
    simp only [reducedValue, ‹l.1 = some _›, ‹r.1 = some _›, ‹o.1 = some _›]
    linear_combination -hg
  · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
    subst h
    r1cs_leaf hl hr ho V h4
    have hg := facts_generic h4
    simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none] at hg
    simp only [reducedValue, ‹l.1 = some _›, ‹r.1 = some _›, ‹o.1 = none›]
    linear_combination hg
  · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
    subst h
    r1cs_leaf hl hr ho V h4
    have hg := facts_generic h4
    simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none] at hg
    simp only [reducedValue, ‹l.1 = some _›, ‹r.1 = none›, ‹o.1 = some _›]
    linear_combination hg
  · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
    subst h
    r1cs_leaf hl hr ho V h4
    have hg := facts_generic h4
    simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none] at hg
    simp only [reducedValue, ‹l.1 = none›, ‹r.1 = some _›, ‹o.1 = some _›]
    linear_combination hg
  · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
    subst h
    r1cs_leaf hl hr ho V h4
    have hg := facts_generic h4
    simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none] at hg
    simp only [reducedValue, ‹l.1 = some _›, ‹r.1 = none›, ‹o.1 = none›]
    linear_combination hg
  · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
    subst h
    r1cs_leaf hl hr ho V h4
    have hg := facts_generic h4
    simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none] at hg
    simp only [reducedValue, ‹l.1 = none›, ‹r.1 = some _›, ‹o.1 = none›]
    linear_combination hg
  · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
    subst h
    r1cs_leaf hl hr ho V h4
    have hg := facts_generic h4
    simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
      Option.getD_none] at hg
    simp only [reducedValue, ‹l.1 = none›, ‹r.1 = none›, ‹o.1 = some _›]
    linear_combination -hg
  · split
    · refine records_pure _ fun V hV => ?_
      obtain ⟨h1, h2⟩ := facts_append hV
      obtain ⟨h2, h3⟩ := facts_append h2
      obtain ⟨h3, -⟩ := facts_append h3
      show _ * _ = _
      rw [← CVar.reduce_val, ← CVar.reduce_val, ← CVar.reduce_val, ← hl V h1, ← hr V h2,
        ← ho V h3]
      simp only [reducedValue, ‹l.1 = none›, ‹r.1 = none›, ‹o.1 = none›]
      exact ‹_ = _›
    · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
      subst h
      r1cs_leaf hl hr ho V h4
      have hg := facts_generic h4
      simp only [genericValue, Option.map_none, Option.getD_none] at hg
      simp only [reducedValue, ‹l.1 = none›, ‹r.1 = none›, ‹o.1 = none›]
      linear_combination hg

/-- When the recorded events hold at a valuation, a `Basic` constraint holds there. -/
theorem basic_of_reductionFacts (nv : Variable) (aux : AuxState F) (b : Basic F)
    (V : Valuation F) (h : ReductionFacts V (recordReduction nv aux (reduce b)).events) :
    Basic.Holds V b := by
  cases b with
  | r1cs a b c => exact recordReduction_of_records (records_r1cs a b c) nv aux V h
  | equal a b => exact recordReduction_of_records (records_equal a b) nv aux V h
  | square a b => exact recordReduction_of_records (records_square a b) nv aux V h
  | boolean x => exact boolean_of_reductionFacts nv aux x V h

private theorem records_reduceAffinePoint (p : AffinePoint (FVar F)) :
    Records (reduceAffinePoint p : RecordingBuilder F (AffinePoint Variable)) fun q es =>
      ∀ V : Valuation F, ReductionFacts V es → V q.x = p.x.val V ∧ V q.y = p.y.val V := by
  unfold reduceAffinePoint
  records [records_reduceToVariable _]
  rename_i y _ hy x _ hx
  intro V hV
  obtain ⟨h1, h2⟩ := facts_append hV
  exact ⟨hx V (facts_append h2).1, hy V h1⟩

private theorem records_addComplete (c : AddComplete F) :
    Records (c.reduce : RecordingBuilder F (Rows F)) fun row es =>
      ∀ V : Valuation F, ReductionFacts V es →
        Kimchi.Lift.Gate.AddComplete.cellMap (rowValues V row.row) = AddComplete.read V c := by
  unfold AddComplete.reduce
  records [records_reduceAffinePoint _, records_reduceToVariable _]
  rename_i p1 _ h1 p2 _ h2 p3 _ h3 x21Inv _ h4 infZ _ h5 s _ h6 sameX _ h7 inf _ h8
  intro V hV
  obtain ⟨f1, hV⟩ := facts_append hV
  obtain ⟨f2, hV⟩ := facts_append hV
  obtain ⟨f3, hV⟩ := facts_append hV
  obtain ⟨f4, hV⟩ := facts_append hV
  obtain ⟨f5, hV⟩ := facts_append hV
  obtain ⟨f6, hV⟩ := facts_append hV
  obtain ⟨f7, hV⟩ := facts_append hV
  obtain ⟨f8, -⟩ := facts_append hV
  obtain ⟨hx1, hy1⟩ := h1 V f1
  obtain ⟨hx2, hy2⟩ := h2 V f2
  obtain ⟨hx3, hy3⟩ := h3 V f3
  have h4' := h4 V f4
  have h5' := h5 V f5
  have h6' := h6 V f6
  have h7' := h7 V f7
  have h8' := h8 V f8
  simp [Kimchi.Lift.Gate.AddComplete.cellMap, rowValues, AddComplete.read, hx1, hy1, hx2, hy2,
    hx3, hy3, h4', h5', h6', h7', h8']

/-- When the recorded events hold at a valuation, the emitted complete-addition row read cell
by cell is the gate's witness at the operands' values. -/
theorem addComplete_read_eq (nv : Variable) (aux : AuxState F) (c : AddComplete F)
    (V : Valuation F) (h : ReductionFacts V (recordReduction nv aux c.reduce).events) :
    Kimchi.Lift.Gate.AddComplete.cellMap
        (rowValues V (recordReduction nv aux c.reduce).result.row) =
      AddComplete.read V c :=
  recordReduction_of_records (records_addComplete c) nv aux V h

/-- The gate's predicate on the emitted row, read at a valuation where the recorded events
hold, is the source constraint's. -/
theorem addComplete_holds_of_reductionFacts (nv : Variable) (aux : AuxState F)
    (c : AddComplete F) (V : Valuation F)
    (h : ReductionFacts V (recordReduction nv aux c.reduce).events)
    (hg : Kimchi.Gate.AddComplete.Holds (Kimchi.Lift.Gate.AddComplete.cellMap
      (rowValues V (recordReduction nv aux c.reduce).result.row))) :
    KimchiConstraint.Holds V (.addComplete c) := by
  show Kimchi.Gate.AddComplete.Holds (AddComplete.read V c)
  rwa [addComplete_read_eq nv aux c V h] at hg

end Reducers

/-! ## Discharging an equality by its outcome -/

section Outcomes

variable [Field F] [DecidableEq F]

/-- A merged equality holds where the two variables agree. -/
theorem equalsHolds_of_merge {c : EqualsConstraint F} {cache : List (F × Variable)}
    {l r : Variable} (h : outcomeOf c cache = .merge l r) (V : Valuation F) (hV : V l = V r) :
    equalsHolds V c := by
  unfold outcomeOf at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
        simp only [equalsHolds, ‹c.vl = some l›, ‹c.vr = some r›, Option.map_some,
          Option.getD_some, ‹c.cl = c.cr›, hV]
      · cases h
    · split at h
      · cases h
      · split at h <;> cases h
    · split at h
      · cases h
      · split at h <;> cases h
    · split at h <;> cases h

/-- A cache-hit equality holds where the variable agrees with the cached one, which reads as
the constant. -/
theorem equalsHolds_of_cached {c : EqualsConstraint F} {cache : List (F × Variable)}
    {l v : Variable} {k : F} (h : outcomeOf c cache = .cached l v k) (V : Valuation F)
    (hV : V l = V v) (hk : V v = k) : equalsHolds V c := by
  unfold outcomeOf at h
  split at h
  · cases h
  · split at h
    · split at h <;> cases h
    · split at h
      · cases h
      · split at h
        · cases h
          simp only [equalsHolds, ‹c.vl = some l›, ‹c.vr = none›, Option.map_some,
            Option.getD_some, Option.map_none, Option.getD_none, hV, hk, mul_one]
          exact mul_div_cancel₀ _ ‹¬ c.cl = 0›
        · cases h
    · split at h
      · cases h
      · split at h
        · cases h
          simp only [equalsHolds, ‹c.vl = none›, ‹c.vr = some l›, Option.map_some,
            Option.getD_some, Option.map_none, Option.getD_none, hV, hk, mul_one]
          exact (mul_div_cancel₀ _ ‹¬ c.cr = 0›).symm
        · cases h
    · split at h <;> cases h

/-- A pinning equality holds where its row's equation vanishes, and pins its variable to the
constant. -/
theorem equalsHolds_of_pinned {c : EqualsConstraint F} {cache : List (F × Variable)}
    {v : Variable} {k : F} {g : GenericPlonkConstraint F} (h : outcomeOf c cache = .pinned v k g)
    (V : Valuation F) (hg : genericValue V g = 0) : equalsHolds V c ∧ V v = k := by
  unfold outcomeOf at h
  split at h
  · cases h
  · split at h
    · split at h <;> cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
            Option.getD_none, mul_zero, add_zero] at hg
          have hcl : c.cl * V v = c.cr := by linear_combination hg
          refine ⟨?_, ?_⟩
          · simp only [equalsHolds, ‹c.vl = some v›, ‹c.vr = none›, Option.map_some,
              Option.getD_some, Option.map_none, Option.getD_none, mul_one]
            exact hcl
          · rw [eq_div_iff ‹¬ c.cl = 0›, mul_comm]
            exact hcl
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
            Option.getD_none, mul_zero, zero_mul, add_zero, zero_add] at hg
          have hcr : c.cr * V v = c.cl := by linear_combination hg
          refine ⟨?_, ?_⟩
          · simp only [equalsHolds, ‹c.vl = none›, ‹c.vr = some v›, Option.map_some,
              Option.getD_some, Option.map_none, Option.getD_none, mul_one]
            exact hcr.symm
          · rw [eq_div_iff ‹¬ c.cr = 0›, mul_comm]
            exact hcr
    · split at h <;> cases h

/-- An equality queued as a row holds where that row's equation vanishes. -/
theorem equalsHolds_of_row {c : EqualsConstraint F} {cache : List (F × Variable)}
    {g : GenericPlonkConstraint F} (h : outcomeOf c cache = .row g) (V : Valuation F)
    (hg : genericValue V g = 0) : equalsHolds V c := by
  unfold outcomeOf at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        simp only [genericValue, Option.map_some, Option.getD_some, Option.map_none,
          Option.getD_none, mul_zero, zero_mul, add_zero] at hg
        simp only [equalsHolds, ‹c.vl = some _›, ‹c.vr = some _›, Option.map_some,
          Option.getD_some]
        linear_combination hg
    · split at h
      · cases h
        simp only [genericValue, Option.map_none, Option.getD_none, mul_zero,
          add_zero, zero_add] at hg
        simp only [equalsHolds, ‹c.vl = some _›, ‹c.vr = none›, Option.map_some,
          Option.getD_some, Option.map_none, Option.getD_none, ‹c.cl = 0›, hg, zero_mul,
          mul_one]
      · split at h <;> cases h
    · split at h
      · cases h
        simp only [genericValue, Option.map_none, Option.getD_none, mul_zero,
          add_zero, zero_add] at hg
        simp only [equalsHolds, ‹c.vl = none›, ‹c.vr = some _›, Option.map_some,
          Option.getD_some, Option.map_none, Option.getD_none, ‹c.cr = 0›, hg, zero_mul,
          mul_one]
      · split at h <;> cases h
    · split at h
      · cases h
      · cases h
        simp only [genericValue, Option.map_none, Option.getD_none, mul_zero,
          add_zero, zero_add] at hg
        simp only [equalsHolds, ‹c.vl = none›, ‹c.vr = none›, Option.map_none, Option.getD_none,
          mul_one]
        linear_combination hg

/-- A trivial equality holds at every valuation. -/
theorem equalsHolds_of_trivial {c : EqualsConstraint F} {cache : List (F × Variable)}
    (h : outcomeOf c cache = .trivial) (V : Valuation F) : equalsHolds V c := by
  unfold outcomeOf at h
  split at h
  · simp only [equalsHolds, ‹c.cl = 0 ∧ c.cr = 0›.1, ‹c.cl = 0 ∧ c.cr = 0›.2, zero_mul]
  · split at h
    · split at h <;> cases h
    · split at h
      · cases h
      · split at h <;> cases h
    · split at h
      · cases h
      · split at h <;> cases h
    · split at h
      · simp only [equalsHolds, ‹c.vl = none›, ‹c.vr = none›, Option.map_none, Option.getD_none,
          mul_one, ‹c.cl = c.cr›]
      · cases h

end Outcomes

/-! ## The names -/

section Names

variable [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]

/-- The variables an operand's affine form names, in term order. -/
def _root_.Snarky.CVar.termVars (x : CVar F) : List Variable :=
  x.reduceToAffineExpression.terms.map Prod.fst

/-- The variables a `Basic` constraint's operands name, with repetition. -/
def _root_.Snarky.Basic.termVars : Basic F → List Variable
  | .r1cs a b c => a.termVars ++ b.termVars ++ c.termVars
  | .equal a b => a.termVars ++ b.termVars
  | .square a b => a.termVars ++ b.termVars
  | .boolean x => x.termVars

/-- The variables a constraint's operands name, with repetition: every term of every affine
operand. -/
def KimchiConstraint.termVars : KimchiConstraint F → List Variable
  | .basic b => b.termVars
  | .addComplete c => c.operands.toList.flatMap CVar.termVars
  | _ => []

end Names

section NameWalks

variable [Field F] [DecidableEq F]

/-- Every name of the log, and the result's variable if any, is one of the terms or an
allocation of the log. -/
private def NamesFrom (terms : List Variable) (r : Option Variable)
    (es : List (ReductionEvent F)) : Prop :=
  (∀ e ∈ es, ∀ w ∈ e.names, w ∈ terms ∨ w ∈ allocs es) ∧
    ∀ v, r = some v → v ∈ terms ∨ v ∈ allocs es

omit [Field F] [DecidableEq F] in
private theorem namesFrom_nil {terms : List Variable} {r : Option Variable}
    (hr : ∀ v, r = some v → v ∈ terms) : NamesFrom terms r ([] : List (ReductionEvent F)) :=
  ⟨fun _ h => (List.not_mem_nil h).elim, fun v hv => Or.inl (hr v hv)⟩

omit [Field F] [DecidableEq F] in
private theorem namesFrom_mono {terms terms' : List Variable} {r : Option Variable}
    {es : List (ReductionEvent F)} (h : NamesFrom terms r es) (ht : terms ⊆ terms') :
    NamesFrom terms' r es :=
  ⟨fun e he w hw => (h.1 e he w hw).imp_left (ht ·), fun v hv => (h.2 v hv).imp_left (ht ·)⟩

omit [Field F] [DecidableEq F] in
/-- A log followed by a tail whose names draw on the whole log's allocations. -/
private theorem namesFrom_append {terms : List Variable} {r₁ r : Option Variable}
    {es₁ es₂ : List (ReductionEvent F)} (h₁ : NamesFrom terms r₁ es₁)
    (h₂ : ∀ e ∈ es₂, ∀ w ∈ e.names, w ∈ terms ∨ w ∈ allocs (es₁ ++ es₂))
    (hr : ∀ v, r = some v → v ∈ terms ∨ v ∈ allocs (es₁ ++ es₂)) :
    NamesFrom terms r (es₁ ++ es₂) := by
  refine ⟨fun e he w hw => ?_, hr⟩
  rcases List.mem_append.mp he with he | he
  · rcases h₁.1 e he w hw with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [allocs_append]; exact List.mem_append_left _ h)
  · exact h₂ e he w hw

omit [Field F] [DecidableEq F] in
private theorem mem_allocs_cons {v : Variable} {ex : AffineExpression F}
    {es : List (ReductionEvent F)} : v ∈ allocs (.alloc v ex :: es) := by
  simp [allocs]

omit [Field F] [DecidableEq F] in
private theorem allocs_mono_left {es₁ es₂ : List (ReductionEvent F)} {v : Variable}
    (h : v ∈ allocs es₁) : v ∈ allocs (es₁ ++ es₂) := by
  rw [allocs_append]
  exact List.mem_append_left _ h

omit [Field F] [DecidableEq F] in
private theorem allocs_mono_right {es₁ es₂ : List (ReductionEvent F)} {v : Variable}
    (h : v ∈ allocs es₂) : v ∈ allocs (es₁ ++ es₂) := by
  rw [allocs_append]
  exact List.mem_append_right _ h

private theorem records_completelyReduce_names (single : Variable × F) :
    (l : List (Variable × F)) →
      Records (completelyReduce single l : RecordingBuilder F (Variable × F)) fun r es =>
        NamesFrom ((single :: l).map Prod.fst) (some r.1) es
  | [] => records_pure _ (namesFrom_nil fun v hv => by simp_all)
  | next :: rest => by
    unfold completelyReduce
    records [records_completelyReduce_names next rest]
    subst_vars
    have hr := ‹NamesFrom ((next :: rest).map Prod.fst) (some _) _›
    refine namesFrom_append (namesFrom_mono hr (by simp)) ?_ ?_
    · intro e he w hw
      simp only [List.append_nil, List.mem_append, List.mem_singleton] at he
      rcases he with rfl | rfl
      · simp only [ReductionEvent.names, List.mem_singleton] at hw
        subst hw
        exact Or.inr (allocs_mono_right mem_allocs_cons)
      · simp only [ReductionEvent.names, GenericPlonkConstraint.vars, Option.toList_some,
          List.mem_append, List.mem_singleton] at hw
        rcases hw with (rfl | rfl) | rfl
        · exact Or.inl (by simp)
        · rcases hr.2 _ rfl with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr (allocs_mono_left h)
        · exact Or.inr (allocs_mono_right mem_allocs_cons)
    · intro v hv
      simp only [Option.some.injEq] at hv
      subst hv
      exact Or.inr (allocs_mono_right mem_allocs_cons)

/-- The walk of an affine form: its names are its terms or its allocations, and a single unit
term with no constant is handed back as is, with no event. -/
private theorem records_reduceAffineExpression_names (ae : AffineExpression F) :
    Records (reduceAffineExpression ae : RecordingBuilder F (Option Variable × F)) fun r es =>
      NamesFrom (ae.terms.map Prod.fst) r.1 es ∧
        ∀ w, ae.terms = [(w, 1)] → ae.constant = none → es = [] ∧ r = (some w, 1) := by
  unfold reduceAffineExpression
  records [records_completelyReduce_names _ _]
  · refine ⟨namesFrom_nil fun v hv => (by simp at hv), fun w hw _ => (by simp_all)⟩
  · refine ⟨namesFrom_nil fun v hv => (by simp_all), fun w => ?_⟩
    have hterms := ‹ae.terms = [_]›
    intro hw _
    rw [hterms] at hw
    simp only [List.cons.injEq, and_true] at hw
    subst hw
    exact ⟨rfl, rfl⟩
  · refine ⟨namesFrom_nil fun v hv => (by simp_all), fun w hw hc => (by simp_all)⟩
  · subst_vars
    refine ⟨⟨fun e he w hw => ?_, fun v hv => ?_⟩, fun w hw hc => (by simp_all)⟩
    · simp only [List.append_nil, List.mem_append, List.mem_singleton] at he
      rcases he with rfl | rfl
      · simp only [ReductionEvent.names, List.mem_singleton] at hw
        subst hw
        exact Or.inr mem_allocs_cons
      · simp only [ReductionEvent.names, GenericPlonkConstraint.vars, Option.toList_some,
          Option.toList_none, List.append_nil, List.mem_append,
          List.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Or.inl (by simp_all)
        · exact Or.inr mem_allocs_cons
    · simp only [Option.some.injEq] at hv
      subst hv
      exact Or.inr mem_allocs_cons
  · subst_vars
    have hr := ‹NamesFrom ((_ :: _).map Prod.fst) (some _) _›
    refine ⟨?_, fun w hw hc => (by simp_all)⟩
    refine namesFrom_append (namesFrom_mono hr (by simp_all)) ?_ ?_
    · intro e he w hw
      simp only [List.append_nil, List.mem_append, List.mem_singleton] at he
      rcases he with rfl | rfl
      · simp only [ReductionEvent.names, List.mem_singleton] at hw
        subst hw
        exact Or.inr (allocs_mono_right mem_allocs_cons)
      · simp only [ReductionEvent.names, GenericPlonkConstraint.vars, Option.toList_some,
          List.mem_append, List.mem_singleton] at hw
        rcases hw with (rfl | rfl) | rfl
        · exact Or.inl (by simp_all)
        · rcases hr.2 _ rfl with h | h
          · exact Or.inl (by simp_all)
          · exact Or.inr (allocs_mono_left h)
        · exact Or.inr (allocs_mono_right mem_allocs_cons)
    · intro v hv
      simp only [Option.some.injEq] at hv
      subst hv
      exact Or.inr (allocs_mono_right mem_allocs_cons)

/-- The walk of an operand: its names and its variable are its terms or its allocations, and a
bare variable is handed back as is, with no event. -/
private theorem records_reduceToVariable_names (x : CVar F) :
    Records (reduceToVariable x : RecordingBuilder F Variable) fun v es =>
      NamesFrom x.termVars (some v) es ∧ ∀ w, x = .var w → es = [] ∧ v = w := by
  unfold reduceToVariable
  records [records_reduceAffineExpression_names _]
  · obtain ⟨o, cache, rfl, hoc⟩ := ‹∃ o cache, _ = [ReductionEvent.equal _ o] ∧ _›
    subst hoc
    subst_vars
    obtain ⟨hr, hbare⟩ := ‹NamesFrom _ _ _ ∧ _›
    refine ⟨?_, fun w hw => ?_⟩
    · refine namesFrom_append hr ?_ ?_
      · intro e he w hw
        simp only [List.append_nil, List.mem_append, List.mem_singleton] at he
        rcases he with rfl | rfl
        · simp only [ReductionEvent.names, List.mem_singleton] at hw
          subst hw
          exact Or.inr (allocs_mono_right mem_allocs_cons)
        · simp only [ReductionEvent.names] at hw
          have := outcomeOf_names _ _ w hw
          simp only [Option.toList_some, Option.toList_none, List.append_nil,
            List.mem_singleton] at this
          subst this
          exact Or.inr (allocs_mono_right mem_allocs_cons)
      · intro v hv
        simp only [Option.some.injEq] at hv
        subst hv
        exact Or.inr (allocs_mono_right mem_allocs_cons)
    · subst hw
      obtain ⟨-, h⟩ := hbare w rfl rfl
      simp_all
  · obtain ⟨hr, hbare⟩ := ‹NamesFrom _ _ _ ∧ _›
    refine ⟨?_, fun w hw => ?_⟩
    · rw [List.append_nil]
      exact ⟨hr.1, fun v hv => by
        simp only [Option.some.injEq] at hv
        subst hv
        exact hr.2 _ ‹_ = some _›⟩
    · subst hw
      obtain ⟨h1, h2⟩ := hbare w rfl rfl
      simp_all
  · obtain ⟨hr, hbare⟩ := ‹NamesFrom _ _ _ ∧ _›
    subst_vars
    refine ⟨?_, fun w hw => ?_⟩
    · refine namesFrom_append hr ?_ ?_
      · intro e he w hw
        simp only [List.append_nil, List.mem_append, List.mem_singleton] at he
        rcases he with rfl | rfl
        · simp only [ReductionEvent.names, List.mem_singleton] at hw
          subst hw
          exact Or.inr (allocs_mono_right mem_allocs_cons)
        · simp only [ReductionEvent.names, GenericPlonkConstraint.vars, Option.toList_some,
            Option.toList_none, List.append_nil, List.mem_append, List.mem_singleton] at hw
          rcases hw with rfl | rfl
          · rcases hr.2 _ ‹_ = some _› with h | h
            · exact Or.inl h
            · exact Or.inr (allocs_mono_left h)
          · exact Or.inr (allocs_mono_right mem_allocs_cons)
      · intro v hv
        simp only [Option.some.injEq] at hv
        subst hv
        exact Or.inr (allocs_mono_right mem_allocs_cons)
    · subst hw
      obtain ⟨h1, h2⟩ := hbare w rfl rfl
      simp_all


omit [Field F] [DecidableEq F] in
/-- Three walked logs, then a tail naming only what they allocated or the ambient terms. -/
private theorem names_seq3 {T : List Variable} {r₁ r₂ r₃ : Option Variable}
    {es₁ es₂ es₃ es₄ : List (ReductionEvent F)} (h₁ : NamesFrom T r₁ es₁)
    (h₂ : NamesFrom T r₂ es₂) (h₃ : NamesFrom T r₃ es₃)
    (h₄ : ∀ e ∈ es₄, ∀ w ∈ e.names, w ∈ T ∨ w ∈ allocs (es₁ ++ (es₂ ++ es₃))) :
    ∀ e ∈ es₁ ++ (es₂ ++ (es₃ ++ es₄)), ∀ w ∈ e.names,
      w ∈ T ∨ w ∈ allocs (es₁ ++ (es₂ ++ (es₃ ++ es₄))) := by
  intro e he w hw
  simp only [List.mem_append] at he
  simp only [allocs_append, List.mem_append]
  rcases he with he | he | he | he
  · have := h₁.1 e he w hw
    tauto
  · have := h₂.1 e he w hw
    tauto
  · have := h₃.1 e he w hw
    tauto
  · have := h₄ e he w hw
    simp only [allocs_append, List.mem_append] at this
    tauto

omit [Field F] [DecidableEq F] in
/-- Two walked logs, then a tail naming only what they allocated or the ambient terms. -/
private theorem names_seq2 {T : List Variable} {r₁ r₂ : Option Variable}
    {es₁ es₂ es₃ : List (ReductionEvent F)} (h₁ : NamesFrom T r₁ es₁) (h₂ : NamesFrom T r₂ es₂)
    (h₃ : ∀ e ∈ es₃, ∀ w ∈ e.names, w ∈ T ∨ w ∈ allocs (es₁ ++ es₂)) :
    ∀ e ∈ es₁ ++ (es₂ ++ es₃), ∀ w ∈ e.names, w ∈ T ∨ w ∈ allocs (es₁ ++ (es₂ ++ es₃)) := by
  intro e he w hw
  simp only [List.mem_append] at he
  simp only [allocs_append, List.mem_append]
  rcases he with he | he | he
  · have := h₁.1 e he w hw
    tauto
  · have := h₂.1 e he w hw
    tauto
  · have := h₃ e he w hw
    simp only [allocs_append, List.mem_append] at this
    tauto

omit [Field F] [DecidableEq F] in
/-- One walked log, then a tail naming only what it allocated or the ambient terms. -/
private theorem names_seq1 {T : List Variable} {r₁ : Option Variable}
    {es₁ es₂ : List (ReductionEvent F)} (h₁ : NamesFrom T r₁ es₁)
    (h₂ : ∀ e ∈ es₂, ∀ w ∈ e.names, w ∈ T ∨ w ∈ allocs es₁) :
    ∀ e ∈ es₁ ++ es₂, ∀ w ∈ e.names, w ∈ T ∨ w ∈ allocs (es₁ ++ es₂) := by
  intro e he w hw
  simp only [List.mem_append] at he
  simp only [allocs_append, List.mem_append]
  rcases he with he | he
  · have := h₁.1 e he w hw
    tauto
  · have := h₂ e he w hw
    tauto

omit [Field F] [DecidableEq F] in
private theorem names_generic_of {T A : List Variable} {g : GenericPlonkConstraint F}
    (hg : ∀ w ∈ g.vars, w ∈ T ∨ w ∈ A) :
    ∀ e ∈ [ReductionEvent.generic g], ∀ w ∈ e.names, w ∈ T ∨ w ∈ A := by
  intro e he w hw
  rw [List.mem_singleton] at he
  subst he
  exact hg w hw

omit [Field F] [DecidableEq F] in
private theorem names_nil {T A : List Variable} :
    ∀ e ∈ ([] : List (ReductionEvent F)), ∀ w ∈ e.names, w ∈ T ∨ w ∈ A :=
  fun _ h => (List.not_mem_nil h).elim

/-- The walk of a `Basic` constraint: its names are its terms or its allocations. -/
private theorem records_basic_names (b : Basic F) :
    Records (reduce b : RecordingBuilder F Unit) fun _ es =>
      ∀ e ∈ es, ∀ w ∈ e.names, w ∈ b.termVars ∨ w ∈ allocs es := by
  cases b with
  | r1cs a b c =>
    simp only [reduce]
    refine records_bind (records_reduceAffineExpression_names _) fun l esl hl => ?_
    refine records_bind (records_reduceAffineExpression_names _) fun r esr hr => ?_
    refine records_bind (records_reduceAffineExpression_names _) fun o eso ho => ?_
    have sa : a.termVars ⊆ (Basic.r1cs a b c).termVars :=
      (List.subset_append_left _ _).trans (List.subset_append_left _ _)
    have sb : b.termVars ⊆ (Basic.r1cs a b c).termVars :=
      (List.subset_append_right _ _).trans (List.subset_append_left _ _)
    have sc : c.termVars ⊆ (Basic.r1cs a b c).termVars := List.subset_append_right _ _
    have ha := namesFrom_mono hl.1 sa
    have hb := namesFrom_mono hr.1 sb
    have hc := namesFrom_mono ho.1 sc
    have la : ∀ v, l.1 = some v → v ∈ (Basic.r1cs a b c).termVars ∨
        v ∈ allocs (esl ++ (esr ++ eso)) :=
      fun v hv => (hl.1.2 v hv).imp (sa ·) allocs_mono_left
    have lb : ∀ v, r.1 = some v → v ∈ (Basic.r1cs a b c).termVars ∨
        v ∈ allocs (esl ++ (esr ++ eso)) :=
      fun v hv => (hr.1.2 v hv).imp (sb ·) fun h => allocs_mono_right (allocs_mono_left h)
    have lc : ∀ v, o.1 = some v → v ∈ (Basic.r1cs a b c).termVars ∨
        v ∈ allocs (esl ++ (esr ++ eso)) :=
      fun v hv => (ho.1.2 v hv).imp (sc ·) fun h => allocs_mono_right (allocs_mono_right h)
    split
    · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
      subst h
      refine names_seq3 ha hb hc (names_generic_of fun w hw => ?_)
      simp only [GenericPlonkConstraint.vars, Option.toList_some, List.mem_append,
        List.mem_singleton] at hw
      rcases hw with (rfl | rfl) | rfl
      · exact la _ ‹_›
      · exact lb _ ‹_›
      · exact lc _ ‹_›
    · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
      subst h
      refine names_seq3 ha hb hc (names_generic_of fun w hw => ?_)
      simp only [GenericPlonkConstraint.vars, Option.toList_some, Option.toList_none,
        List.append_nil, List.mem_append, List.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact la _ ‹_›
      · exact lb _ ‹_›
    · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
      subst h
      refine names_seq3 ha hb hc (names_generic_of fun w hw => ?_)
      simp only [GenericPlonkConstraint.vars, Option.toList_some, Option.toList_none,
        List.append_nil, List.mem_append, List.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact la _ ‹_›
      · exact lc _ ‹_›
    · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
      subst h
      refine names_seq3 ha hb hc (names_generic_of fun w hw => ?_)
      simp only [GenericPlonkConstraint.vars, Option.toList_some, Option.toList_none,
        List.nil_append, List.mem_append, List.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact lb _ ‹_›
      · exact lc _ ‹_›
    · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
      subst h
      refine names_seq3 ha hb hc (names_generic_of fun w hw => ?_)
      simp only [GenericPlonkConstraint.vars, Option.toList_some, Option.toList_none,
        List.append_nil, List.mem_singleton] at hw
      subst hw
      exact la _ ‹_›
    · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
      subst h
      refine names_seq3 ha hb hc (names_generic_of fun w hw => ?_)
      simp only [GenericPlonkConstraint.vars, Option.toList_some, Option.toList_none,
        List.append_nil, List.nil_append, List.mem_singleton] at hw
      subst hw
      exact lb _ ‹_›
    · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
      subst h
      refine names_seq3 ha hb hc (names_generic_of fun w hw => ?_)
      simp only [GenericPlonkConstraint.vars, Option.toList_some, Option.toList_none,
        List.append_nil, List.nil_append, List.mem_singleton] at hw
      subst hw
      exact lc _ ‹_›
    · split
      · exact records_pure _ (names_seq3 ha hb hc names_nil)
      · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₄ h => ?_
        subst h
        exact names_seq3 ha hb hc (names_generic_of fun w hw => by
          simp [GenericPlonkConstraint.vars] at hw)
  | equal a b =>
    simp only [reduce]
    refine records_bind (records_reduceAffineExpression_names _) fun l esl hl => ?_
    refine records_bind (records_reduceAffineExpression_names _) fun r esr hr => ?_
    have sa : a.termVars ⊆ (Basic.equal a b).termVars := List.subset_append_left _ _
    have sb : b.termVars ⊆ (Basic.equal a b).termVars := List.subset_append_right _ _
    refine records_mono (records_addEqualsConstraint _) fun _ es₃ h => ?_
    obtain ⟨o, cache, rfl, hoc⟩ := h
    subst hoc
    refine names_seq2 (namesFrom_mono hl.1 sa) (namesFrom_mono hr.1 sb) fun e he w hw => ?_
    rw [List.mem_singleton] at he
    subst he
    simp only [ReductionEvent.names] at hw
    have hm := outcomeOf_names _ _ w hw
    simp only [List.mem_append, Option.mem_toList] at hm
    rcases hm with hm | hm
    · exact (hl.1.2 w hm).imp (sa ·) allocs_mono_left
    · exact (hr.1.2 w hm).imp (sb ·) allocs_mono_right
  | square a b =>
    simp only [reduce]
    refine records_bind (records_reduceAffineExpression_names _) fun x esx hx => ?_
    refine records_bind (records_reduceAffineExpression_names _) fun y esy hy => ?_
    have sa : a.termVars ⊆ (Basic.square a b).termVars := List.subset_append_left _ _
    have sb : b.termVars ⊆ (Basic.square a b).termVars := List.subset_append_right _ _
    have ha := namesFrom_mono hx.1 sa
    have hb := namesFrom_mono hy.1 sb
    have la : ∀ v, x.1 = some v → v ∈ (Basic.square a b).termVars ∨ v ∈ allocs (esx ++ esy) :=
      fun v hv => (hx.1.2 v hv).imp (sa ·) allocs_mono_left
    have lb : ∀ v, y.1 = some v → v ∈ (Basic.square a b).termVars ∨ v ∈ allocs (esx ++ esy) :=
      fun v hv => (hy.1.2 v hv).imp (sb ·) allocs_mono_right
    split
    · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₃ h => ?_
      subst h
      refine names_seq2 ha hb (names_generic_of fun w hw => ?_)
      simp only [GenericPlonkConstraint.vars, Option.toList_some, List.mem_append,
        List.mem_singleton, or_self] at hw
      rcases hw with rfl | rfl
      · exact la _ ‹_›
      · exact lb _ ‹_›
    · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₃ h => ?_
      subst h
      refine names_seq2 ha hb (names_generic_of fun w hw => ?_)
      simp only [GenericPlonkConstraint.vars, Option.toList_some, Option.toList_none,
        List.append_nil, List.mem_append, List.mem_singleton, or_self] at hw
      subst hw
      exact la _ ‹_›
    · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₃ h => ?_
      subst h
      refine names_seq2 ha hb (names_generic_of fun w hw => ?_)
      simp only [GenericPlonkConstraint.vars, Option.toList_some, Option.toList_none,
        List.append_nil, List.nil_append, List.mem_singleton] at hw
      subst hw
      exact lb _ ‹_›
    · split
      · exact records_pure _ (names_seq2 ha hb names_nil)
      · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₃ h => ?_
        subst h
        exact names_seq2 ha hb (names_generic_of fun w hw => by
          simp [GenericPlonkConstraint.vars] at hw)
  | boolean x =>
    simp only [reduce]
    refine records_bind (records_reduceAffineExpression_names _) fun r esr hr => ?_
    have ha : NamesFrom (Basic.boolean x).termVars r.1 esr := hr.1
    split
    · split
      · exact records_pure _ (names_seq1 ha names_nil)
      · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₂ h => ?_
        subst h
        exact names_seq1 ha (names_generic_of fun w hw => by
          simp [GenericPlonkConstraint.vars] at hw)
    · refine records_mono (records_addGenericPlonkConstraint _) fun _ es₂ h => ?_
      subst h
      refine names_seq1 ha (names_generic_of fun w hw => ?_)
      simp only [GenericPlonkConstraint.vars, Option.toList_some, Option.toList_none,
        List.append_nil, List.mem_append, List.mem_singleton, or_self] at hw
      subst hw
      exact ha.2 _ ‹_›

/-- The names of a `Basic` constraint's recorded reduction are its terms or its allocations. -/
theorem basic_names (nv : Variable) (aux : AuxState F) (b : Basic F) :
    ∀ e ∈ (recordReduction nv aux (reduce b)).events, ∀ w ∈ e.names,
      w ∈ b.termVars ∨ w ∈ allocs (recordReduction nv aux (reduce b)).events :=
  recordReduction_of_records (records_basic_names b) nv aux


/-- An operand's walk read within a longer log whose allocations are `A`: every event names an
allocation or a term of the operand, which is then not that bare variable; the result is a term
or an allocation; a bare operand returns its variable. -/
private def OperandNames (x : CVar F) (v : Variable) (A : List Variable)
    (es : List (ReductionEvent F)) : Prop :=
  (∀ e ∈ es, ∀ w ∈ e.names, w ∈ A ∨ (w ∈ x.termVars ∧ x ≠ .var w)) ∧
    (v ∈ x.termVars ∨ v ∈ A) ∧ ∀ w, x = .var w → v = w

private theorem operandNames_of {x : CVar F} {v : Variable} {es : List (ReductionEvent F)}
    (h : NamesFrom x.termVars (some v) es ∧ ∀ w, x = .var w → es = [] ∧ v = w)
    {A : List Variable} (hA : ∀ u ∈ allocs es, u ∈ A) : OperandNames x v A es := by
  refine ⟨fun e he w hw => ?_, (h.1.2 v rfl).imp_right (hA v), fun w hw => (h.2 w hw).2⟩
  rcases h.1.1 e he w hw with hw' | hw'
  · refine Or.inr ⟨hw', fun hx => ?_⟩
    obtain ⟨hes, -⟩ := h.2 w hx
    subst hes
    exact List.not_mem_nil he
  · exact Or.inl (hA w hw')

/-- A point's two operands, read within a longer log whose allocations are `A`. -/
private def PointNames (p : AffinePoint (FVar F)) (q : AffinePoint Variable) (A : List Variable)
    (es : List (ReductionEvent F)) : Prop :=
  (∀ e ∈ es, ∀ w ∈ e.names, w ∈ A ∨ (w ∈ p.x.termVars ∧ p.x ≠ .var w) ∨
    (w ∈ p.y.termVars ∧ p.y ≠ .var w)) ∧
    (q.x ∈ p.x.termVars ∨ q.x ∈ A) ∧ (q.y ∈ p.y.termVars ∨ q.y ∈ A) ∧
    (∀ w, p.x = .var w → q.x = w) ∧ ∀ w, p.y = .var w → q.y = w

private theorem pointNames_mono {p : AffinePoint (FVar F)} {q : AffinePoint Variable}
    {A A' : List Variable} {es : List (ReductionEvent F)} (h : PointNames p q A es)
    (hA : ∀ u ∈ A, u ∈ A') : PointNames p q A' es :=
  ⟨fun e he w hw => (h.1 e he w hw).imp_left (hA w), h.2.1.imp_right (hA _),
    h.2.2.1.imp_right (hA _), h.2.2.2.1, h.2.2.2.2⟩

private theorem records_reduceAffinePoint_names (p : AffinePoint (FVar F)) :
    Records (reduceAffinePoint p : RecordingBuilder F (AffinePoint Variable)) fun q es =>
      PointNames p q (allocs es) es := by
  unfold reduceAffinePoint
  refine records_bind (records_reduceToVariable_names _) fun y esy hy => ?_
  refine records_bind (records_reduceToVariable_names _) fun x esx hx => ?_
  refine records_pure _ ?_
  have hy' := operandNames_of hy (A := allocs (esy ++ (esx ++ []))) fun u hu => allocs_mono_left hu
  have hx' := operandNames_of hx (A := allocs (esy ++ (esx ++ []))) fun u hu =>
    allocs_mono_right (allocs_mono_left hu)
  refine ⟨fun e he w hw => ?_, hx'.2.1, hy'.2.1, hx'.2.2, hy'.2.2⟩
  simp only [List.append_nil, List.mem_append] at he
  rcases he with he | he
  · exact (hy'.1 e he w hw).imp_right Or.inr
  · exact (hx'.1 e he w hw).imp_right Or.inl

/-- The walk of a complete addition: every name is an allocation or a term of an operand that
is not that bare variable, and the row's eleven cells are the operands' variables, each a term
of its operand or an allocation, a bare operand's being itself. -/
private theorem records_addComplete_names (c : AddComplete F) :
    Records (c.reduce : RecordingBuilder F (Rows F)) fun row es =>
      (∀ e ∈ es, ∀ w ∈ e.names, w ∈ allocs es ∨
        ∃ x ∈ c.operands.toList, w ∈ x.termVars ∧ x ≠ .var w) ∧
      ∃ vs : List Variable, row.row.vars.toList = vs.map some ++ List.replicate 4 none ∧
        List.Forall₂ (fun v x => (v ∈ x.termVars ∨ v ∈ allocs es) ∧ ∀ w, x = .var w → v = w)
          vs c.operands.toList := by
  unfold AddComplete.reduce
  refine records_bind (records_reduceAffinePoint_names _) fun p1 es1 h1 => ?_
  refine records_bind (records_reduceAffinePoint_names _) fun p2 es2 h2 => ?_
  refine records_bind (records_reduceAffinePoint_names _) fun p3 es3 h3 => ?_
  refine records_bind (records_reduceToVariable_names _) fun x21Inv es4 h4 => ?_
  refine records_bind (records_reduceToVariable_names _) fun infZ es5 h5 => ?_
  refine records_bind (records_reduceToVariable_names _) fun s es6 h6 => ?_
  refine records_bind (records_reduceToVariable_names _) fun sameX es7 h7 => ?_
  refine records_bind (records_reduceToVariable_names _) fun inf es8 h8 => ?_
  refine records_pure _ ?_
  have h1' := pointNames_mono h1
    (A' := allocs (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++ (es6 ++ (es7 ++ (es8 ++ [])))))))))
    fun u hu => allocs_mono_left hu
  have h2' := pointNames_mono h2
    (A' := allocs (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++ (es6 ++ (es7 ++ (es8 ++ [])))))))))
    fun u hu => allocs_mono_right (allocs_mono_left hu)
  have h3' := pointNames_mono h3
    (A' := allocs (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++ (es6 ++ (es7 ++ (es8 ++ [])))))))))
    fun u hu => allocs_mono_right (allocs_mono_right (allocs_mono_left hu))
  have h4' := operandNames_of h4
    (A := allocs (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++ (es6 ++ (es7 ++ (es8 ++ [])))))))))
    fun u hu => allocs_mono_right (allocs_mono_right (allocs_mono_right (allocs_mono_left hu)))
  have h5' := operandNames_of h5
    (A := allocs (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++ (es6 ++ (es7 ++ (es8 ++ [])))))))))
    fun u hu => allocs_mono_right (allocs_mono_right (allocs_mono_right (allocs_mono_right
      (allocs_mono_left hu))))
  have h6' := operandNames_of h6
    (A := allocs (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++ (es6 ++ (es7 ++ (es8 ++ [])))))))))
    fun u hu => allocs_mono_right (allocs_mono_right (allocs_mono_right (allocs_mono_right
      (allocs_mono_right (allocs_mono_left hu)))))
  have h7' := operandNames_of h7
    (A := allocs (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++ (es6 ++ (es7 ++ (es8 ++ [])))))))))
    fun u hu => allocs_mono_right (allocs_mono_right (allocs_mono_right (allocs_mono_right
      (allocs_mono_right (allocs_mono_right (allocs_mono_left hu))))))
  have h8' := operandNames_of h8
    (A := allocs (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++ (es6 ++ (es7 ++ (es8 ++ [])))))))))
    fun u hu => allocs_mono_right (allocs_mono_right (allocs_mono_right (allocs_mono_right
      (allocs_mono_right (allocs_mono_right (allocs_mono_right (allocs_mono_left hu)))))))
  have hops : c.operands.toList = [c.p1.x, c.p1.y, c.p2.x, c.p2.y, c.p3.x, c.p3.y, c.inf,
      c.sameX, c.s, c.infZ, c.x21Inv] := rfl
  refine ⟨fun e he w hw => ?_,
    [p1.x, p1.y, p2.x, p2.y, p3.x, p3.y, inf, sameX, s, infZ, x21Inv], rfl, ?_⟩
  · simp only [List.append_nil, List.mem_append] at he
    rw [hops]
    rcases he with he | he | he | he | he | he | he | he
    · rcases h1'.1 e he w hw with h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨c.p1.x, by simp, h⟩
      · exact Or.inr ⟨c.p1.y, by simp, h⟩
    · rcases h2'.1 e he w hw with h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨c.p2.x, by simp, h⟩
      · exact Or.inr ⟨c.p2.y, by simp, h⟩
    · rcases h3'.1 e he w hw with h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨c.p3.x, by simp, h⟩
      · exact Or.inr ⟨c.p3.y, by simp, h⟩
    · rcases h4'.1 e he w hw with h | h
      · exact Or.inl h
      · exact Or.inr ⟨c.x21Inv, by simp, h⟩
    · rcases h5'.1 e he w hw with h | h
      · exact Or.inl h
      · exact Or.inr ⟨c.infZ, by simp, h⟩
    · rcases h6'.1 e he w hw with h | h
      · exact Or.inl h
      · exact Or.inr ⟨c.s, by simp, h⟩
    · rcases h7'.1 e he w hw with h | h
      · exact Or.inl h
      · exact Or.inr ⟨c.sameX, by simp, h⟩
    · rcases h8'.1 e he w hw with h | h
      · exact Or.inl h
      · exact Or.inr ⟨c.inf, by simp, h⟩
  · rw [hops]
    exact .cons ⟨h1'.2.1, h1'.2.2.2.1⟩ (.cons ⟨h1'.2.2.1, h1'.2.2.2.2⟩
      (.cons ⟨h2'.2.1, h2'.2.2.2.1⟩ (.cons ⟨h2'.2.2.1, h2'.2.2.2.2⟩
      (.cons ⟨h3'.2.1, h3'.2.2.2.1⟩ (.cons ⟨h3'.2.2.1, h3'.2.2.2.2⟩
      (.cons ⟨h8'.2.1, h8'.2.2⟩ (.cons ⟨h7'.2.1, h7'.2.2⟩ (.cons ⟨h6'.2.1, h6'.2.2⟩
      (.cons ⟨h5'.2.1, h5'.2.2⟩ (.cons ⟨h4'.2.1, h4'.2.2⟩ .nil))))))))))

/-- The names of a complete addition's recorded reduction are allocations or terms of operands
that are not that bare variable, and its row's cells are its operands' variables, each a term
of its operand or an allocation, a bare operand's being itself. -/
theorem addComplete_names (nv : Variable) (aux : AuxState F) (c : AddComplete F) :
    (∀ e ∈ (recordReduction nv aux c.reduce).events, ∀ w ∈ e.names,
      w ∈ allocs (recordReduction nv aux c.reduce).events ∨
        ∃ x ∈ c.operands.toList, w ∈ x.termVars ∧ x ≠ .var w) ∧
    ∃ vs : List Variable,
      (recordReduction nv aux c.reduce).result.row.vars.toList =
        vs.map some ++ List.replicate 4 none ∧
      List.Forall₂ (fun v x => (v ∈ x.termVars ∨
        v ∈ allocs (recordReduction nv aux c.reduce).events) ∧ ∀ w, x = .var w → v = w)
        vs c.operands.toList :=
  recordReduction_of_records (records_addComplete_names c) nv aux


/-! ## Absent cells carry no coefficient -/

/-- Every equation a log queues carries no coefficient on an absent cell. -/
private def AbsentAll (es : List (ReductionEvent F)) : Prop :=
  ∀ e ∈ es, ∀ g, e.queued? = some g → g.AbsentZero

omit [DecidableEq F] in
private theorem absentAll_nil : AbsentAll ([] : List (ReductionEvent F)) :=
  fun _ h => (List.not_mem_nil h).elim

omit [DecidableEq F] in
private theorem absentAll_append_iff {es₁ es₂ : List (ReductionEvent F)} :
    AbsentAll (es₁ ++ es₂) ↔ AbsentAll es₁ ∧ AbsentAll es₂ :=
  ⟨fun h => ⟨fun e he => h e (List.mem_append_left _ he),
    fun e he => h e (List.mem_append_right _ he)⟩,
    fun ⟨h₁, h₂⟩ e he => (List.mem_append.mp he).elim (h₁ e) (h₂ e)⟩

omit [DecidableEq F] in
private theorem absentAll_cons_iff {e : ReductionEvent F} {es : List (ReductionEvent F)} :
    AbsentAll (e :: es) ↔ (∀ g, e.queued? = some g → g.AbsentZero) ∧ AbsentAll es :=
  ⟨fun h => ⟨h e (List.mem_cons_self ..), fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩,
    fun ⟨h₁, h₂⟩ e' he' => (List.mem_cons.mp he').elim (fun h => h ▸ h₁) (h₂ e')⟩

/-- The equation a decision queues, if any, carries no coefficient on an absent cell. -/
private theorem queued_outcome_absent (c : EqualsConstraint F) (cache : List (F × Variable)) :
    ∀ g, (ReductionEvent.equal c (outcomeOf c cache)).queued? = some g → g.AbsentZero := by
  intro g hg
  cases ho : outcomeOf c cache with
  | pinned v k g' =>
    rw [ho] at hg
    simp only [ReductionEvent.queued?, Option.some.injEq] at hg
    subst hg
    exact outcomeOf_pinned_absentZero ho
  | row g' =>
    rw [ho] at hg
    simp only [ReductionEvent.queued?, Option.some.injEq] at hg
    subst hg
    exact outcomeOf_row_absentZero ho
  | merge _ _ =>
    rw [ho] at hg
    simp [ReductionEvent.queued?] at hg
  | cached _ _ _ =>
    rw [ho] at hg
    simp [ReductionEvent.queued?] at hg
  | trivial =>
    rw [ho] at hg
    simp [ReductionEvent.queued?] at hg

omit [Field F] [DecidableEq F] in
private theorem queued?_alloc (v : Variable) (ex : AffineExpression F) :
    (ReductionEvent.alloc v ex).queued? = none := by
  simp [ReductionEvent.queued?]

omit [Field F] [DecidableEq F] in
private theorem queued?_generic (g : GenericPlonkConstraint F) :
    (ReductionEvent.generic g).queued? = some g := by
  simp [ReductionEvent.queued?]

/-- Close a leaf of an absent-cell walk: split the log event by event and discharge each by
its shape, a queued equation by its literal cells. -/
local macro "absent_leaf" : tactic => `(tactic| (
  simp_all [absentAll_cons_iff, absentAll_nil, absentAll_append_iff, queued?_alloc,
    queued?_generic]
  all_goals first
    | exact queued_outcome_absent _ _
    | simp [GenericPlonkConstraint.AbsentZero]))

private theorem records_completelyReduce_absent (single : Variable × F) :
    (l : List (Variable × F)) →
      Records (completelyReduce single l : RecordingBuilder F (Variable × F)) fun _ es =>
        AbsentAll es
  | [] => records_pure _ absentAll_nil
  | next :: rest => by
    unfold completelyReduce
    records [records_completelyReduce_absent next rest]
    subst_vars
    absent_leaf

private theorem records_reduceAffineExpression_absent (ae : AffineExpression F) :
    Records (reduceAffineExpression ae : RecordingBuilder F (Option Variable × F)) fun _ es =>
      AbsentAll es := by
  unfold reduceAffineExpression
  records [records_completelyReduce_absent _ _]
  all_goals (subst_vars; absent_leaf)

private theorem records_reduceToVariable_absent (x : CVar F) :
    Records (reduceToVariable x : RecordingBuilder F Variable) fun _ es => AbsentAll es := by
  unfold reduceToVariable
  records [records_reduceAffineExpression_absent _]
  · obtain ⟨o, cache, rfl, hoc⟩ := ‹∃ o cache, _ = [ReductionEvent.equal _ o] ∧ _›
    subst_vars
    absent_leaf
  · absent_leaf
  · subst_vars
    absent_leaf

private theorem records_reduceAffinePoint_absent (p : AffinePoint (FVar F)) :
    Records (reduceAffinePoint p : RecordingBuilder F (AffinePoint Variable)) fun _ es =>
      AbsentAll es := by
  unfold reduceAffinePoint
  records [records_reduceToVariable_absent _]
  absent_leaf

private theorem records_addComplete_absent (c : AddComplete F) :
    Records (c.reduce : RecordingBuilder F (Rows F)) fun _ es => AbsentAll es := by
  unfold AddComplete.reduce
  records [records_reduceAffinePoint_absent _, records_reduceToVariable_absent _]
  absent_leaf

private theorem records_basic_absent (b : Basic F) :
    Records (reduce b : RecordingBuilder F Unit) fun _ es => AbsentAll es := by
  cases b <;> simp only [reduce] <;> records [records_reduceAffineExpression_absent _]
  all_goals
    try obtain ⟨o, cache, rfl, hoc⟩ := ‹∃ o cache, _ = [ReductionEvent.equal _ o] ∧ _›
  all_goals (subst_vars; absent_leaf)

/-- Every equation a `Basic` constraint's recorded reduction queues carries no coefficient on
an absent cell. -/
theorem basic_absentZero (nv : Variable) (aux : AuxState F) (b : Basic F) :
    ∀ e ∈ (recordReduction nv aux (reduce b)).events, ∀ g, e.queued? = some g → g.AbsentZero :=
  recordReduction_of_records (records_basic_absent b) nv aux

/-- Every equation a complete addition's recorded reduction queues carries no coefficient on
an absent cell. -/
theorem addComplete_absentZero (nv : Variable) (aux : AuxState F) (c : AddComplete F) :
    ∀ e ∈ (recordReduction nv aux c.reduce).events, ∀ g, e.queued? = some g → g.AbsentZero :=
  recordReduction_of_records (records_addComplete_absent c) nv aux

end NameWalks

end Snarky.Kimchi
