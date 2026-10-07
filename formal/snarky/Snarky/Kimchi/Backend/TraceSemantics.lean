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

## Main results

- `reduceToVariable_reads`: when the recorded events hold, the pinned variable reads as the
  operand.
- `boolean_of_reductionFacts`: when the recorded events hold, the Boolean holds.
- `addComplete_read_eq`: when the recorded events hold, the emitted row read cell by cell is
  the gate's witness at the operands' values; `addComplete_holds_of_reductionFacts` transports
  the gate's predicate across it to the source constraint.

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
      ∃ o, es = [.equal c o] :=
  fun s => ⟨[.equal c (outcomeOf c s.core.aux.wireState.cachedConstants)], rfl, _, rfl⟩

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
  · obtain ⟨o, rfl⟩ := ‹∃ o, _ = [ReductionEvent.equal _ o]›
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

end Snarky.Kimchi
