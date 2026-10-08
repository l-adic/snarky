import Snarky.Kimchi.Backend.Trace
import Snarky.Kimchi.Backend.Admissibility
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
- `KimchiConstraint.placedOperands`, `CellOf`: the operands a constraint places, and a row cell
  against its placed operand. The layouts they read, `KimchiConstraint.rowOperands` and the
  variables it names, are the scope checker's.

## Main results

- `reduceToVariable_reads`: when the recorded events hold, the pinned variable reads as the
  operand.
- `boolean_of_reductionFacts`: when the recorded events hold, the Boolean holds.
- `addComplete_read_eq`, `endoScalar_read_eq`, `varBaseMul_read_eq`: when the recorded
  events hold, each emitted row, or row pair, read cell by cell is the gate's witness at the
  operands' values; `addComplete_holds_of_reductionFacts`,
  `endoScalar_holds_of_reductionFacts`, `varBaseMul_holds_of_reductionFacts` transport the
  gate's predicate across it to the source constraint; `endoMul_holds_of_reductionFacts` and
  `poseidon_holds_of_reductionFacts` read each round's or window's row with its successor and
  close the chain, the latter under the block shape `5w + 1`. `endoScalar_result_length`,
  `endoScalar_kind`, `varBaseMul_result_length`, `varBaseMul_kind`, `varBaseMul_rows_fst`,
  `varBaseMul_rows_snd`, `endoMul_result_length`, `endoMul_kind`, `poseidon_result_length`,
  `poseidon_kind`, `poseidon_coeffs`: the rows the multi-row gates emit, per round, and a
  window's constants in its coefficients.
- `equalsHolds_of_merge`, `equalsHolds_of_cached`, `equalsHolds_of_pinned`,
  `equalsHolds_of_row`, `equalsHolds_of_trivial`: an equality holds once the fact its logged
  outcome names holds, a merge or cache hit by class, a pin or row by its emitted equation.
- `basic_names`: the names of a `Basic` constraint's recorded reduction are its terms or its
  allocations.
- `Placed`, `addComplete_placed`, `endoScalar_placed`, `varBaseMul_placed`, `endoMul_placed`,
  `poseidon_placed`, `pad_placed`: a gate's recorded reduction placed, its names terms of
  placed operands that are not that bare variable, its rows matching
  `KimchiConstraint.rowOperands` cell by cell (`CellOf`); `endoScalar_cell_some`,
  `varBaseMul_cell_some_fst`, `varBaseMul_cell_some_snd`, `endoMul_cell_some_round`,
  `endoMul_cell_some_next`, `poseidon_cell_some_window`, `poseidon_cell_some_next`: every
  operand cell of an emitted row is labelled.
- `basic_absentZero`, `addComplete_absentZero`, `endoScalar_absentZero`,
  `varBaseMul_absentZero`, `endoMul_absentZero`, `poseidon_absentZero`, `pad_absentZero`:
  every equation a constraint's recorded reduction queues has no coefficient on an absent cell.
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

omit [Field F] [DecidableEq F] in
/-- A vector of eight, mapped, as the list of its cells. -/
private theorem vector8_toList_map {α β : Type} (f : α → β) (v : Vector α 8) :
    v.toList.map f = [f v[0], f v[1], f v[2], f v[3], f v[4], f v[5], f v[6], f v[7]] := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, Vector.getElem_toList]
    simp only [List.length_map, Vector.length_toList] at h1
    interval_cases i <;> rfl

/-- The reading of one decomposition round: the emitted row read cell by cell is the gate's
witness at the operands' values. -/
private theorem records_endoScalarRound (r : EndoScalarRound F) :
    Records (r.reduce : RecordingBuilder F (KimchiRow F)) fun row es =>
      ∀ V : Valuation F, ReductionFacts V es →
        Kimchi.Lift.Gate.EndoScalar.cellMap (rowValues V row) = EndoScalarRound.read V r := by
  unfold EndoScalarRound.reduce
  refine records_bind (records_reduceToVariable _) fun x0 es0 h0 => ?_
  refine records_bind (records_reduceToVariable _) fun x1 es1 h1 => ?_
  refine records_bind (records_reduceToVariable _) fun x2 es2 h2 => ?_
  refine records_bind (records_reduceToVariable _) fun x3 es3 h3 => ?_
  refine records_bind (records_reduceToVariable _) fun x4 es4 h4 => ?_
  refine records_bind (records_reduceToVariable _) fun x5 es5 h5 => ?_
  refine records_bind (records_reduceToVariable _) fun x6 es6 h6 => ?_
  refine records_bind (records_reduceToVariable _) fun x7 es7 h7 => ?_
  refine records_bind (records_reduceToVariable _) fun b8 es8 h8 => ?_
  refine records_bind (records_reduceToVariable _) fun a8 es9 h9 => ?_
  refine records_bind (records_reduceToVariable _) fun b0 es10 h10 => ?_
  refine records_bind (records_reduceToVariable _) fun a0 es11 h11 => ?_
  refine records_bind (records_reduceToVariable _) fun n8 es12 h12 => ?_
  refine records_bind (records_reduceToVariable _) fun n0 es13 h13 => ?_
  refine records_pure _ ?_
  intro V hV
  obtain ⟨f0, hV⟩ := facts_append hV
  obtain ⟨f1, hV⟩ := facts_append hV
  obtain ⟨f2, hV⟩ := facts_append hV
  obtain ⟨f3, hV⟩ := facts_append hV
  obtain ⟨f4, hV⟩ := facts_append hV
  obtain ⟨f5, hV⟩ := facts_append hV
  obtain ⟨f6, hV⟩ := facts_append hV
  obtain ⟨f7, hV⟩ := facts_append hV
  obtain ⟨f8, hV⟩ := facts_append hV
  obtain ⟨f9, hV⟩ := facts_append hV
  obtain ⟨f10, hV⟩ := facts_append hV
  obtain ⟨f11, hV⟩ := facts_append hV
  obtain ⟨f12, hV⟩ := facts_append hV
  obtain ⟨f13, -⟩ := facts_append hV
  have hx0 := h0 V f0
  have hx1 := h1 V f1
  have hx2 := h2 V f2
  have hx3 := h3 V f3
  have hx4 := h4 V f4
  have hx5 := h5 V f5
  have hx6 := h6 V f6
  have hx7 := h7 V f7
  have hb8 := h8 V f8
  have ha8 := h9 V f9
  have hb0 := h10 V f10
  have ha0 := h11 V f11
  have hn8 := h12 V f12
  have hn0 := h13 V f13
  simp [Kimchi.Lift.Gate.EndoScalar.cellMap, rowValues, EndoScalarRound.read, vector8_toList_map,
    hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hb8, ha8, hb0, ha0, hn8, hn0]

/-- One round emits an `endoScalar` row. -/
private theorem records_endoScalarRound_kind (r : EndoScalarRound F) :
    Records (r.reduce : RecordingBuilder F (KimchiRow F)) fun row _ => row.kind = .endoScalar := by
  unfold EndoScalarRound.reduce
  records [records_reduceToVariable _]
  rfl

/-- A decomposition emits one `endoScalar` row per round. -/
private theorem records_endoScalar_shape :
    (rounds : EndoScalar F) →
      Records (EndoScalar.reduce rounds : RecordingBuilder F (List (KimchiRow F))) fun rows _ =>
        rows.length = rounds.length ∧
          ∀ (i : Nat) (hi : i < rows.length), rows[i].kind = .endoScalar
  | [] => records_pure _ ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | r :: rs => by
    unfold EndoScalar.reduce
    refine records_bind (records_endoScalarRound_kind r) fun row es1 h1 => ?_
    refine records_bind (records_endoScalar_shape rs) fun rest es2 h2 => ?_
    refine records_pure _ ⟨by simp [h2.1], fun i hi => ?_⟩
    cases i with
    | zero => exact h1
    | succ k => exact h2.2 k (by simpa using hi)

/-- The reading of a decomposition: round by round. -/
private theorem records_endoScalar :
    (rounds : EndoScalar F) →
      Records (EndoScalar.reduce rounds : RecordingBuilder F (List (KimchiRow F))) fun rows es =>
        ∀ V : Valuation F, ReductionFacts V es →
          ∀ (i : Nat) (hi : i < rounds.length) (hi' : i < rows.length),
            Kimchi.Lift.Gate.EndoScalar.cellMap (rowValues V rows[i]) =
              EndoScalarRound.read V rounds[i]
  | [] => records_pure _ fun _ _ _ hi => absurd hi (Nat.not_lt_zero _)
  | r :: rs => by
    unfold EndoScalar.reduce
    refine records_bind (records_endoScalarRound r) fun row es1 h1 => ?_
    refine records_bind (records_endoScalar rs) fun rest es2 h2 => ?_
    refine records_pure _ fun V hV i hi hi' => ?_
    obtain ⟨f1, hV⟩ := facts_append hV
    obtain ⟨f2, -⟩ := facts_append hV
    cases i with
    | zero => exact h1 V f1
    | succ k => exact h2 V f2 k (by simpa using hi) (by simpa using hi')

/-- A decomposition's recorded reduction emits one row per round. -/
theorem endoScalar_result_length (nv : Variable) (aux : AuxState F) (rounds : EndoScalar F) :
    (recordReduction nv aux (EndoScalar.reduce rounds)).result.length = rounds.length :=
  (recordReduction_of_records (records_endoScalar_shape rounds) nv aux).1

/-- Every row a decomposition's recorded reduction emits is an `endoScalar` row. -/
theorem endoScalar_kind (nv : Variable) (aux : AuxState F) (rounds : EndoScalar F)
    (i : Fin rounds.length) :
    ((recordReduction nv aux (EndoScalar.reduce rounds)).result[i.val]'(by
      rw [endoScalar_result_length]; exact i.isLt)).kind = .endoScalar :=
  (recordReduction_of_records (records_endoScalar_shape rounds) nv aux).2 i.val _

/-- When the recorded events hold at a valuation, each emitted decomposition row read cell by
cell is the gate's witness at its round's operands' values. -/
theorem endoScalar_read_eq (nv : Variable) (aux : AuxState F) (rounds : EndoScalar F)
    (V : Valuation F)
    (h : ReductionFacts V (recordReduction nv aux (EndoScalar.reduce rounds)).events)
    (i : Fin rounds.length) :
    Kimchi.Lift.Gate.EndoScalar.cellMap (rowValues V
        ((recordReduction nv aux (EndoScalar.reduce rounds)).result[i.val]'(by
          rw [endoScalar_result_length]; exact i.isLt))) =
      EndoScalarRound.read V rounds[i] :=
  recordReduction_of_records (records_endoScalar rounds) nv aux V h i.val i.isLt _

/-- The gate's predicate on every emitted row, read at a valuation where the recorded events
hold, is the source constraint's. -/
theorem endoScalar_holds_of_reductionFacts (nv : Variable) (aux : AuxState F)
    (rounds : EndoScalar F) (V : Valuation F)
    (h : ReductionFacts V (recordReduction nv aux (EndoScalar.reduce rounds)).events)
    (hg : ∀ i : Fin rounds.length, Kimchi.Gate.EndoScalar.Holds (Kimchi.Lift.Gate.EndoScalar.cellMap
      (rowValues V ((recordReduction nv aux (EndoScalar.reduce rounds)).result[i.val]'(by
        rw [endoScalar_result_length]; exact i.isLt))))) :
    KimchiConstraint.Holds V (.endoScalar rounds) := by
  show ∀ r ∈ rounds, Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read V r)
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  change Kimchi.Gate.EndoScalar.Holds
    (EndoScalarRound.read V rounds[(⟨i, hi⟩ : Fin rounds.length)])
  rw [← endoScalar_read_eq nv aux rounds V h ⟨i, hi⟩]
  exact hg ⟨i, hi⟩

omit [Field F] [DecidableEq F] in
/-- A list flattened pairwise has twice the length. -/
private theorem length_flatMap_pair {α β : Type} (f g : α → β) :
    (l : List α) → (l.flatMap fun x => [f x, g x]).length = 2 * l.length
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_pair f g xs]
    simp only [List.length_cons, List.length_nil]
    omega

omit [Field F] [DecidableEq F] in
/-- The even positions of a pairwise flattening are the first components. -/
private theorem getElem_flatMap_pair_fst {α β : Type} (f g : α → β) :
    (l : List α) → (k : Nat) → (hk : k < l.length) →
      (l.flatMap fun x => [f x, g x])[2 * k]'(by rw [length_flatMap_pair]; omega) = f l[k]
  | _ :: _, 0, _ => rfl
  | x :: xs, k + 1, hk => by
    show (f x :: g x :: xs.flatMap fun x => [f x, g x])[2 * k + 2]'(by
      rw [List.length_cons, List.length_cons, length_flatMap_pair]
      simp only [List.length_cons] at hk
      omega) = f (xs[k]'(Nat.lt_of_succ_lt_succ hk))
    simp only [List.getElem_cons_succ]
    exact getElem_flatMap_pair_fst f g xs k (Nat.lt_of_succ_lt_succ hk)

omit [Field F] [DecidableEq F] in
/-- The odd positions of a pairwise flattening are the second components. -/
private theorem getElem_flatMap_pair_snd {α β : Type} (f g : α → β) :
    (l : List α) → (k : Nat) → (hk : k < l.length) →
      (l.flatMap fun x => [f x, g x])[2 * k + 1]'(by rw [length_flatMap_pair]; omega) = g l[k]
  | _ :: _, 0, _ => rfl
  | x :: xs, k + 1, hk => by
    show (f x :: g x :: xs.flatMap fun x => [f x, g x])[2 * k + 1 + 2]'(by
      rw [List.length_cons, List.length_cons, length_flatMap_pair]
      simp only [List.length_cons] at hk
      omega) = g (xs[k]'(Nat.lt_of_succ_lt_succ hk))
    simp only [List.getElem_cons_succ]
    exact getElem_flatMap_pair_snd f g xs k (Nat.lt_of_succ_lt_succ hk)

/-- The reading of one scale round: the emitted row pair read cell by cell is the gate's
witness at the operands' values. -/
private theorem records_scaleRound (r : ScaleRound F) :
    Records (r.reduce : RecordingBuilder F (KimchiRow F × KimchiRow F)) fun pair es =>
      ∀ V : Valuation F, ReductionFacts V es →
        Kimchi.Lift.Gate.VarBaseMul.cellMap (rowValues V pair.1) (rowValues V pair.2) =
          ScaleRound.read V r := by
  unfold ScaleRound.reduce
  refine records_bind (records_reduceToVariable _) fun a0x es0 h0 => ?_
  refine records_bind (records_reduceToVariable _) fun a0y es1 h1 => ?_
  refine records_bind (records_reduceToVariable _) fun a1x es2 h2 => ?_
  refine records_bind (records_reduceToVariable _) fun a1y es3 h3 => ?_
  refine records_bind (records_reduceToVariable _) fun a2x es4 h4 => ?_
  refine records_bind (records_reduceToVariable _) fun a2y es5 h5 => ?_
  refine records_bind (records_reduceToVariable _) fun a3x es6 h6 => ?_
  refine records_bind (records_reduceToVariable _) fun a3y es7 h7 => ?_
  refine records_bind (records_reduceToVariable _) fun a4x es8 h8 => ?_
  refine records_bind (records_reduceToVariable _) fun a4y es9 h9 => ?_
  refine records_bind (records_reduceToVariable _) fun a5x es10 h10 => ?_
  refine records_bind (records_reduceToVariable _) fun a5y es11 h11 => ?_
  refine records_bind (records_reduceToVariable _) fun b0 es12 h12 => ?_
  refine records_bind (records_reduceToVariable _) fun b1 es13 h13 => ?_
  refine records_bind (records_reduceToVariable _) fun b2 es14 h14 => ?_
  refine records_bind (records_reduceToVariable _) fun b3 es15 h15 => ?_
  refine records_bind (records_reduceToVariable _) fun b4 es16 h16 => ?_
  refine records_bind (records_reduceToVariable _) fun s0 es17 h17 => ?_
  refine records_bind (records_reduceToVariable _) fun s1 es18 h18 => ?_
  refine records_bind (records_reduceToVariable _) fun s2 es19 h19 => ?_
  refine records_bind (records_reduceToVariable _) fun s3 es20 h20 => ?_
  refine records_bind (records_reduceToVariable _) fun s4 es21 h21 => ?_
  refine records_bind (records_reduceToVariable _) fun np es22 h22 => ?_
  refine records_bind (records_reduceToVariable _) fun nn es23 h23 => ?_
  refine records_bind (records_reduceToVariable _) fun bx es24 h24 => ?_
  refine records_bind (records_reduceToVariable _) fun by_ es25 h25 => ?_
  refine records_pure _ ?_
  intro V hV
  obtain ⟨f0, hV⟩ := facts_append hV
  obtain ⟨f1, hV⟩ := facts_append hV
  obtain ⟨f2, hV⟩ := facts_append hV
  obtain ⟨f3, hV⟩ := facts_append hV
  obtain ⟨f4, hV⟩ := facts_append hV
  obtain ⟨f5, hV⟩ := facts_append hV
  obtain ⟨f6, hV⟩ := facts_append hV
  obtain ⟨f7, hV⟩ := facts_append hV
  obtain ⟨f8, hV⟩ := facts_append hV
  obtain ⟨f9, hV⟩ := facts_append hV
  obtain ⟨f10, hV⟩ := facts_append hV
  obtain ⟨f11, hV⟩ := facts_append hV
  obtain ⟨f12, hV⟩ := facts_append hV
  obtain ⟨f13, hV⟩ := facts_append hV
  obtain ⟨f14, hV⟩ := facts_append hV
  obtain ⟨f15, hV⟩ := facts_append hV
  obtain ⟨f16, hV⟩ := facts_append hV
  obtain ⟨f17, hV⟩ := facts_append hV
  obtain ⟨f18, hV⟩ := facts_append hV
  obtain ⟨f19, hV⟩ := facts_append hV
  obtain ⟨f20, hV⟩ := facts_append hV
  obtain ⟨f21, hV⟩ := facts_append hV
  obtain ⟨f22, hV⟩ := facts_append hV
  obtain ⟨f23, hV⟩ := facts_append hV
  obtain ⟨f24, hV⟩ := facts_append hV
  obtain ⟨f25, -⟩ := facts_append hV
  have e0 := h0 V f0
  have e1 := h1 V f1
  have e2 := h2 V f2
  have e3 := h3 V f3
  have e4 := h4 V f4
  have e5 := h5 V f5
  have e6 := h6 V f6
  have e7 := h7 V f7
  have e8 := h8 V f8
  have e9 := h9 V f9
  have e10 := h10 V f10
  have e11 := h11 V f11
  have e12 := h12 V f12
  have e13 := h13 V f13
  have e14 := h14 V f14
  have e15 := h15 V f15
  have e16 := h16 V f16
  have e17 := h17 V f17
  have e18 := h18 V f18
  have e19 := h19 V f19
  have e20 := h20 V f20
  have e21 := h21 V f21
  have e22 := h22 V f22
  have e23 := h23 V f23
  have e24 := h24 V f24
  have e25 := h25 V f25
  simp [Kimchi.Lift.Gate.VarBaseMul.cellMap, rowValues, ScaleRound.read, e0, e1, e2, e3, e4, e5,
    e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24,
    e25]

/-- One scale round emits a `varBaseMul` row first. -/
private theorem records_scaleRound_kind (r : ScaleRound F) :
    Records (r.reduce : RecordingBuilder F (KimchiRow F × KimchiRow F)) fun pair _ =>
      pair.1.kind = .varBaseMul := by
  unfold ScaleRound.reduce
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  exact records_pure _ rfl

/-- A multiplication emits one row pair per round, each led by a `varBaseMul` row. -/
private theorem records_varBaseMul_shape :
    (rounds : VarBaseMul F) →
      Records (VarBaseMul.reduce rounds : RecordingBuilder F (List (KimchiRow F × KimchiRow F)))
        fun pairs _ => pairs.length = rounds.length ∧
          ∀ (i : Nat) (hi : i < pairs.length), pairs[i].1.kind = .varBaseMul
  | [] => records_pure _ ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | r :: rs => by
    unfold VarBaseMul.reduce
    refine records_bind (records_scaleRound_kind r) fun pair es1 h1 => ?_
    refine records_bind (records_varBaseMul_shape rs) fun rest es2 h2 => ?_
    refine records_pure _ ⟨by simp [h2.1], fun i hi => ?_⟩
    cases i with
    | zero => exact h1
    | succ k => exact h2.2 k (by simpa using hi)

/-- The reading of a multiplication: round by round. -/
private theorem records_varBaseMul :
    (rounds : VarBaseMul F) →
      Records (VarBaseMul.reduce rounds : RecordingBuilder F (List (KimchiRow F × KimchiRow F)))
        fun pairs es => ∀ V : Valuation F, ReductionFacts V es →
          ∀ (i : Nat) (hi : i < rounds.length) (hi' : i < pairs.length),
            Kimchi.Lift.Gate.VarBaseMul.cellMap (rowValues V pairs[i].1)
              (rowValues V pairs[i].2) = ScaleRound.read V rounds[i]
  | [] => records_pure _ fun _ _ _ hi => absurd hi (Nat.not_lt_zero _)
  | r :: rs => by
    unfold VarBaseMul.reduce
    refine records_bind (records_scaleRound r) fun pair es1 h1 => ?_
    refine records_bind (records_varBaseMul rs) fun rest es2 h2 => ?_
    refine records_pure _ fun V hV i hi hi' => ?_
    obtain ⟨f1, hV⟩ := facts_append hV
    obtain ⟨f2, -⟩ := facts_append hV
    cases i with
    | zero => exact h1 V f1
    | succ k => exact h2 V f2 k (by simpa using hi) (by simpa using hi')

/-- A multiplication's recorded reduction emits one row pair per round. -/
theorem varBaseMul_result_length (nv : Variable) (aux : AuxState F) (rounds : VarBaseMul F) :
    (recordReduction nv aux (VarBaseMul.reduce rounds)).result.length = rounds.length :=
  (recordReduction_of_records (records_varBaseMul_shape rounds) nv aux).1

/-- Every row pair a multiplication's recorded reduction emits is led by a `varBaseMul` row. -/
theorem varBaseMul_kind (nv : Variable) (aux : AuxState F) (rounds : VarBaseMul F)
    (i : Fin rounds.length) :
    ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[i.val]'(by
      rw [varBaseMul_result_length]; exact i.isLt)).1.kind = .varBaseMul :=
  (recordReduction_of_records (records_varBaseMul_shape rounds) nv aux).2 i.val _

/-- A multiplication's emitted rows, the pairs flattened, number twice its rounds. -/
theorem varBaseMul_rows_length (nv : Variable) (aux : AuxState F) (rounds : VarBaseMul F) :
    ((recordReduction nv aux (VarBaseMul.reduce rounds)).result.flatMap
      fun p => [p.1, p.2]).length = 2 * rounds.length := by
  rw [length_flatMap_pair, varBaseMul_result_length]

/-- A round's first row sits at the even position of the flattened rows. -/
theorem varBaseMul_rows_fst (nv : Variable) (aux : AuxState F) (rounds : VarBaseMul F)
    (i : Fin rounds.length) :
    ((recordReduction nv aux (VarBaseMul.reduce rounds)).result.flatMap
        fun p => [p.1, p.2])[2 * i.val]'(by rw [varBaseMul_rows_length]; omega) =
      ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[i.val]'(by
        rw [varBaseMul_result_length]; exact i.isLt)).1 :=
  getElem_flatMap_pair_fst _ _ _ i.val _

/-- A round's second row sits at the odd position of the flattened rows. -/
theorem varBaseMul_rows_snd (nv : Variable) (aux : AuxState F) (rounds : VarBaseMul F)
    (i : Fin rounds.length) :
    ((recordReduction nv aux (VarBaseMul.reduce rounds)).result.flatMap
        fun p => [p.1, p.2])[2 * i.val + 1]'(by rw [varBaseMul_rows_length]; omega) =
      ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[i.val]'(by
        rw [varBaseMul_result_length]; exact i.isLt)).2 :=
  getElem_flatMap_pair_snd _ _ _ i.val _

/-- When the recorded events hold at a valuation, each emitted row pair read cell by cell is
the gate's witness at its round's operands' values. -/
theorem varBaseMul_read_eq (nv : Variable) (aux : AuxState F) (rounds : VarBaseMul F)
    (V : Valuation F)
    (h : ReductionFacts V (recordReduction nv aux (VarBaseMul.reduce rounds)).events)
    (i : Fin rounds.length) :
    Kimchi.Lift.Gate.VarBaseMul.cellMap
        (rowValues V ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[i.val]'(by
          rw [varBaseMul_result_length]; exact i.isLt)).1)
        (rowValues V ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[i.val]'(by
          rw [varBaseMul_result_length]; exact i.isLt)).2) =
      ScaleRound.read V rounds[i] :=
  recordReduction_of_records (records_varBaseMul rounds) nv aux V h i.val i.isLt _

/-- The gate's predicate on every emitted row pair, read at a valuation where the recorded
events hold, is the source constraint's. -/
theorem varBaseMul_holds_of_reductionFacts (nv : Variable) (aux : AuxState F)
    (rounds : VarBaseMul F) (V : Valuation F)
    (h : ReductionFacts V (recordReduction nv aux (VarBaseMul.reduce rounds)).events)
    (hg : ∀ i : Fin rounds.length, Kimchi.Gate.VarBaseMul.Holds
      (Kimchi.Lift.Gate.VarBaseMul.cellMap
        (rowValues V ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[i.val]'(by
          rw [varBaseMul_result_length]; exact i.isLt)).1)
        (rowValues V ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[i.val]'(by
          rw [varBaseMul_result_length]; exact i.isLt)).2))) :
    KimchiConstraint.Holds V (.varBaseMul rounds) := by
  show ∀ r ∈ rounds, Kimchi.Gate.VarBaseMul.Holds (ScaleRound.read V r)
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  change Kimchi.Gate.VarBaseMul.Holds (ScaleRound.read V rounds[(⟨i, hi⟩ : Fin rounds.length)])
  rw [← varBaseMul_read_eq nv aux rounds V h ⟨i, hi⟩]
  exact hg ⟨i, hi⟩

/-- The reading of one endomorphism round against any successor row: the row read cell by
cell is the gate's witness at the operands' values, with the successor's output cells. -/
private theorem records_endoMulRound (r : EndoMulRound F) :
    Records (r.reduce : RecordingBuilder F (KimchiRow F)) fun row es =>
      ∀ V : Valuation F, ReductionFacts V es → ∀ nxt : Fin wCols → F,
        Kimchi.Lift.Gate.EndoMul.cellMap (rowValues V row) nxt =
          EndoMulRound.readWith V r (nxt 4) (nxt 5) (nxt 6) := by
  unfold EndoMulRound.reduce
  refine records_bind (records_reduceToVariable _) fun tx es0 h0 => ?_
  refine records_bind (records_reduceToVariable _) fun ty es1 h1 => ?_
  refine records_bind (records_reduceToVariable _) fun px es2 h2 => ?_
  refine records_bind (records_reduceToVariable _) fun py es3 h3 => ?_
  refine records_bind (records_reduceToVariable _) fun na es4 h4 => ?_
  refine records_bind (records_reduceToVariable _) fun rx es5 h5 => ?_
  refine records_bind (records_reduceToVariable _) fun ry es6 h6 => ?_
  refine records_bind (records_reduceToVariable _) fun s1 es7 h7 => ?_
  refine records_bind (records_reduceToVariable _) fun s3 es8 h8 => ?_
  refine records_bind (records_reduceToVariable _) fun b1 es9 h9 => ?_
  refine records_bind (records_reduceToVariable _) fun b2 es10 h10 => ?_
  refine records_bind (records_reduceToVariable _) fun b3 es11 h11 => ?_
  refine records_bind (records_reduceToVariable _) fun b4 es12 h12 => ?_
  refine records_bind (records_reduceToVariable _) fun inv es13 h13 => ?_
  refine records_pure _ ?_
  intro V hV nxt
  obtain ⟨f0, hV⟩ := facts_append hV
  obtain ⟨f1, hV⟩ := facts_append hV
  obtain ⟨f2, hV⟩ := facts_append hV
  obtain ⟨f3, hV⟩ := facts_append hV
  obtain ⟨f4, hV⟩ := facts_append hV
  obtain ⟨f5, hV⟩ := facts_append hV
  obtain ⟨f6, hV⟩ := facts_append hV
  obtain ⟨f7, hV⟩ := facts_append hV
  obtain ⟨f8, hV⟩ := facts_append hV
  obtain ⟨f9, hV⟩ := facts_append hV
  obtain ⟨f10, hV⟩ := facts_append hV
  obtain ⟨f11, hV⟩ := facts_append hV
  obtain ⟨f12, hV⟩ := facts_append hV
  obtain ⟨f13, -⟩ := facts_append hV
  have e0 := h0 V f0
  have e1 := h1 V f1
  have e2 := h2 V f2
  have e3 := h3 V f3
  have e4 := h4 V f4
  have e5 := h5 V f5
  have e6 := h6 V f6
  have e7 := h7 V f7
  have e8 := h8 V f8
  have e9 := h9 V f9
  have e10 := h10 V f10
  have e11 := h11 V f11
  have e12 := h12 V f12
  have e13 := h13 V f13
  simp [Kimchi.Lift.Gate.EndoMul.cellMap, rowValues, EndoMulRound.readWith, e0, e1, e2, e3, e4,
    e5, e6, e7, e8, e9, e10, e11, e12, e13]

/-- One endomorphism round emits an `endoMul` row. -/
private theorem records_endoMulRound_kind (r : EndoMulRound F) :
    Records (r.reduce : RecordingBuilder F (KimchiRow F)) fun row _ => row.kind = .endoMul := by
  unfold EndoMulRound.reduce
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable _) fun _ _ _ => ?_
  exact records_pure _ rfl

/-- The rounds emit one `endoMul` row each. -/
private theorem records_endoMulRounds_shape :
    (state : List (EndoMulRound F)) →
      Records (EndoMul.reduceRounds state : RecordingBuilder F (List (KimchiRow F)))
        fun rows _ => rows.length = state.length ∧
          ∀ (i : Nat) (hi : i < rows.length), rows[i].kind = .endoMul
  | [] => records_pure _ ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | r :: rs => by
    unfold EndoMul.reduceRounds
    refine records_bind (records_endoMulRound_kind r) fun row es1 h1 => ?_
    refine records_bind (records_endoMulRounds_shape rs) fun rest es2 h2 => ?_
    refine records_pure _ ⟨by simp [h2.1], fun i hi => ?_⟩
    cases i with
    | zero => exact h1
    | succ k => exact h2.2 k (by simpa using hi)

/-- The reading of the rounds: round by round, against any successor. -/
private theorem records_endoMulRounds :
    (state : List (EndoMulRound F)) →
      Records (EndoMul.reduceRounds state : RecordingBuilder F (List (KimchiRow F)))
        fun rows es => rows.length = state.length ∧ ∀ V : Valuation F, ReductionFacts V es →
          ∀ (i : Nat) (hi : i < state.length) (hi' : i < rows.length) (nxt : Fin wCols → F),
            Kimchi.Lift.Gate.EndoMul.cellMap (rowValues V rows[i]) nxt =
              EndoMulRound.readWith V state[i] (nxt 4) (nxt 5) (nxt 6)
  | [] => records_pure _ ⟨rfl, fun _ _ _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | r :: rs => by
    unfold EndoMul.reduceRounds
    refine records_bind (records_endoMulRound r) fun row es1 h1 => ?_
    refine records_bind (records_endoMulRounds rs) fun rest es2 h2 => ?_
    refine records_pure _ ⟨by simp [h2.1], fun V hV i hi hi' nxt => ?_⟩
    obtain ⟨f1, hV⟩ := facts_append hV
    obtain ⟨f2, -⟩ := facts_append hV
    cases i with
    | zero => exact h1 V f1 nxt
    | succ k => exact h2.2 V f2 k (by simpa using hi) (by simpa using hi') nxt

/-- A multiplication emits its rounds' rows then the terminal row. -/
private theorem records_endoMul_shape (c : EndoMul F) :
    Records (EndoMul.reduce c : RecordingBuilder F (List (KimchiRow F))) fun rows _ =>
      rows.length = c.state.length + 1 ∧
        ∀ (i : Nat) (hi : i < rows.length), i < c.state.length → rows[i].kind = .endoMul := by
  unfold EndoMul.reduce
  refine records_bind (records_reduceToVariable _) fun xs es0 _ => ?_
  refine records_bind (records_reduceToVariable _) fun ys es1 _ => ?_
  refine records_bind (records_reduceToVariable _) fun na es2 _ => ?_
  refine records_bind (records_endoMulRounds_shape c.state) fun rows es3 h3 => ?_
  refine records_pure _ ⟨by simp [h3.1], fun i hi hi' => ?_⟩
  rw [List.getElem_append_left (by rw [h3.1]; exact hi')]
  exact h3.2 i (by rw [h3.1]; exact hi')

/-- The reading of a multiplication: each round's row against any successor, and the terminal
row's output cells as the finals. -/
private theorem records_endoMul (c : EndoMul F) :
    Records (EndoMul.reduce c : RecordingBuilder F (List (KimchiRow F))) fun rows es =>
      ∀ V : Valuation F, ReductionFacts V es →
        (∀ (i : Nat) (hi : i < rows.length) (hi' : i < c.state.length) (nxt : Fin wCols → F),
          Kimchi.Lift.Gate.EndoMul.cellMap (rowValues V rows[i]) nxt =
            EndoMulRound.readWith V c.state[i] (nxt 4) (nxt 5) (nxt 6)) ∧
        ∀ hi : c.state.length < rows.length,
          rowValues V rows[c.state.length] 4 = c.s.x.val V ∧
            rowValues V rows[c.state.length] 5 = c.s.y.val V ∧
            rowValues V rows[c.state.length] 6 = c.nAcc.val V := by
  unfold EndoMul.reduce
  refine records_bind (records_reduceToVariable _) fun xs es0 h0 => ?_
  refine records_bind (records_reduceToVariable _) fun ys es1 h1 => ?_
  refine records_bind (records_reduceToVariable _) fun na es2 h2 => ?_
  refine records_bind (records_endoMulRounds c.state) fun rows es3 h3 => ?_
  refine records_pure _ fun V hV => ?_
  obtain ⟨f0, hV⟩ := facts_append hV
  obtain ⟨f1, hV⟩ := facts_append hV
  obtain ⟨f2, hV⟩ := facts_append hV
  obtain ⟨f3, -⟩ := facts_append hV
  refine ⟨fun i hi hi' nxt => ?_, fun hi => ?_⟩
  · rw [List.getElem_append_left (by rw [h3.1]; exact hi')]
    exact h3.2 V f3 i hi' (by rw [h3.1]; exact hi') nxt
  · rw [List.getElem_concat_length h3.1.symm]
    refine ⟨?_, ?_, ?_⟩
    · show V xs = c.s.x.val V
      exact h0 V f0
    · show V ys = c.s.y.val V
      exact h1 V f1
    · show V na = c.nAcc.val V
      exact h2 V f2

omit [DecidableEq F] in
/-- The chain from the rows: the gate holds at each round's row with its successor, every
round's row reads as its round against any successor, and the row after the last reads the
finals in its output cells. -/
private theorem chainHolds_of_rows (V : Valuation F) (endo : F) (fin : F × F × F) :
    (state : List (EndoMulRound F)) → (rows : List (KimchiRow F)) →
      (hlen : rows.length = state.length + 1) →
      (∀ (k : Nat) (hk : k < state.length), Kimchi.Gate.EndoMul.Holds endo
        (Kimchi.Lift.Gate.EndoMul.cellMap (rowValues V (rows[k]'(by omega)))
          (rowValues V (rows[k + 1]'(by omega))))) →
      (∀ (k : Nat) (hk : k < state.length) (nxt : Fin wCols → F),
        Kimchi.Lift.Gate.EndoMul.cellMap (rowValues V (rows[k]'(by omega))) nxt =
          EndoMulRound.readWith V state[k] (nxt 4) (nxt 5) (nxt 6)) →
      (rowValues V (rows[state.length]'(by omega)) 4 = fin.1 ∧
        rowValues V (rows[state.length]'(by omega)) 5 = fin.2.1 ∧
        rowValues V (rows[state.length]'(by omega)) 6 = fin.2.2) →
      EndoMul.chainHolds V endo fin state
  | [], _, _, _, _, _ => trivial
  | [r], rows, hlen, hg, hread, hfin => by
    show Kimchi.Gate.EndoMul.Holds endo (EndoMulRound.readWith V r fin.1 fin.2.1 fin.2.2)
    have h := hg 0 (by simp)
    rw [hread 0 (by simp)] at h
    obtain ⟨h4, h5, h6⟩ := hfin
    have h4' : rowValues V (rows[0 + 1]'(by rw [hlen]; simp)) 4 = fin.1 := h4
    have h5' : rowValues V (rows[0 + 1]'(by rw [hlen]; simp)) 5 = fin.2.1 := h5
    have h6' : rowValues V (rows[0 + 1]'(by rw [hlen]; simp)) 6 = fin.2.2 := h6
    rw [h4', h5', h6'] at h
    exact h
  | r :: r' :: rest, rows, hlen, hg, hread, hfin => by
    show Kimchi.Gate.EndoMul.Holds endo
        (EndoMulRound.readWith V r (r'.p.x.val V) (r'.p.y.val V) (r'.nAcc.val V)) ∧
      EndoMul.chainHolds V endo fin (r' :: rest)
    refine ⟨?_, ?_⟩
    · have h := hg 0 (by simp)
      rw [hread 0 (by simp)] at h
      have hn := hread (0 + 1) (by simp) (fun _ => 0)
      have hx : rowValues V (rows[0 + 1]'(by rw [hlen]; simp)) 4 = r'.p.x.val V :=
        congrArg Kimchi.Gate.EndoMul.Witness.xP hn
      have hy : rowValues V (rows[0 + 1]'(by rw [hlen]; simp)) 5 = r'.p.y.val V :=
        congrArg Kimchi.Gate.EndoMul.Witness.yP hn
      have hz : rowValues V (rows[0 + 1]'(by rw [hlen]; simp)) 6 = r'.nAcc.val V :=
        congrArg Kimchi.Gate.EndoMul.Witness.n hn
      rw [hx, hy, hz] at h
      exact h
    · cases rows with
      | nil => simp at hlen
      | cons row0 rows' =>
        refine chainHolds_of_rows V endo fin (r' :: rest) rows' (by simpa using hlen)
          (fun k hk => hg (k + 1) (by simpa using hk)) (fun k hk nxt => hread (k + 1)
            (by simpa using hk) nxt) ?_
        exact hfin

/-- A multiplication's recorded reduction emits one row per round and a terminal row. -/
theorem endoMul_result_length (nv : Variable) (aux : AuxState F) (c : EndoMul F) :
    (recordReduction nv aux (EndoMul.reduce c)).result.length = c.state.length + 1 :=
  (recordReduction_of_records (records_endoMul_shape c) nv aux).1

/-- Every round's row a multiplication's recorded reduction emits is an `endoMul` row. -/
theorem endoMul_kind (nv : Variable) (aux : AuxState F) (c : EndoMul F)
    (k : Fin c.state.length) :
    ((recordReduction nv aux (EndoMul.reduce c)).result[k.val]'(by
      rw [endoMul_result_length]; omega)).kind = .endoMul :=
  (recordReduction_of_records (records_endoMul_shape c) nv aux).2 k.val _ k.isLt

/-- The gate's predicate at every round's row with its successor, read at a valuation where
the recorded events hold, is the source constraint's chain. -/
theorem endoMul_holds_of_reductionFacts (nv : Variable) (aux : AuxState F) (c : EndoMul F)
    (V : Valuation F) (h : ReductionFacts V (recordReduction nv aux (EndoMul.reduce c)).events)
    (hg : ∀ k : Fin c.state.length, Kimchi.Gate.EndoMul.Holds c.endo
      (Kimchi.Lift.Gate.EndoMul.cellMap
        (rowValues V ((recordReduction nv aux (EndoMul.reduce c)).result[k.val]'(by
          rw [endoMul_result_length]; omega)))
        (rowValues V ((recordReduction nv aux (EndoMul.reduce c)).result[k.val + 1]'(by
          rw [endoMul_result_length]; omega))))) :
    KimchiConstraint.Holds V (.endoMul c) := by
  show EndoMul.chainHolds V c.endo (c.s.x.val V, c.s.y.val V, c.nAcc.val V) c.state
  obtain ⟨hr, hfin⟩ := recordReduction_of_records (records_endoMul c) nv aux V h
  exact chainHolds_of_rows V c.endo _ c.state _ (endoMul_result_length nv aux c)
    (fun k hk => hg ⟨k, hk⟩) (fun k hk nxt => hr k _ hk nxt) (hfin _)

omit [Field F] [DecidableEq F] in
/-- The chunking of `5w + 1` pinned states: `w` window rows then the terminal row. -/
private theorem rowsFromStates_length (rc : ℕ → F × F × F) :
    (k w : ℕ) → (vs : List (Variable × Variable × Variable)) → vs.length = 5 * w + 1 →
      (rowsFromStates rc k vs).length = w + 1
  | _, 0, [_], _ => rfl
  | k, w + 1, _ :: _ :: _ :: _ :: _ :: rest, hw => by
    show (rowsFromStates rc (k + 1) rest).length + 1 = w + 1 + 1
    rw [rowsFromStates_length rc (k + 1) w rest (by simp only [List.length_cons] at hw; omega)]
  | _, 0, [], hw => absurd hw (show ¬ (0 = 5 * 0 + 1) by omega)
  | _, 0, _ :: _ :: rest, hw => absurd hw (show ¬ (rest.length + 1 + 1 = 5 * 0 + 1) by omega)
  | _, w + 1, [], hw => absurd hw (show ¬ (0 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_], hw => absurd hw (show ¬ (1 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_, _], hw => absurd hw (show ¬ (2 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_, _, _], hw => absurd hw (show ¬ (3 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_, _, _, _], hw => absurd hw (show ¬ (4 = 5 * (w + 1) + 1) by omega)

omit [Field F] [DecidableEq F] in
/-- Row `j` of the chunking from window `k` is the window at `k + j`, over the pinned states
`5j` to `5j + 4`. -/
private theorem rowsFromStates_window (rc : ℕ → F × F × F) :
    (k w : ℕ) → (vs : List (Variable × Variable × Variable)) → (hw : vs.length = 5 * w + 1) →
      (j : ℕ) → (hj : j < w) →
      (rowsFromStates rc k vs)[j]'(by rw [rowsFromStates_length rc k w vs hw]; omega) =
        addRoundState rc (k + j) (vs[5 * j]'(by omega)) (vs[5 * j + 1]'(by omega))
          (vs[5 * j + 2]'(by omega)) (vs[5 * j + 3]'(by omega)) (vs[5 * j + 4]'(by omega))
  | _, _ + 1, _ :: _ :: _ :: _ :: _ :: _, _, 0, _ => rfl
  | k, w + 1, q0 :: q1 :: q2 :: q3 :: q4 :: rest, hw, j + 1, hj => by
    have hw' : rest.length = 5 * w + 1 := by simp only [List.length_cons] at hw; omega
    have hb : j < (rowsFromStates rc (k + 1) rest).length := by
      rw [rowsFromStates_length rc (k + 1) w rest hw']
      omega
    show (rowsFromStates rc (k + 1) rest)[j]'hb =
      addRoundState rc (k + (j + 1)) (rest[5 * j]'(by omega)) (rest[5 * j + 1]'(by omega))
        (rest[5 * j + 2]'(by omega)) (rest[5 * j + 3]'(by omega)) (rest[5 * j + 4]'(by omega))
    rw [rowsFromStates_window rc (k + 1) w rest hw' j (by omega)]
    congr 1
    omega
  | _, 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | _, w + 1, [], hw, _, _ => absurd hw (show ¬ (0 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_], hw, _, _ => absurd hw (show ¬ (1 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_, _], hw, _, _ => absurd hw (show ¬ (2 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_, _, _], hw, _, _ => absurd hw (show ¬ (3 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_, _, _, _], hw, _, _ => absurd hw (show ¬ (4 = 5 * (w + 1) + 1) by omega)

omit [Field F] [DecidableEq F] in
/-- Row `w` of the chunking is the terminal row over the last pinned state. -/
private theorem rowsFromStates_final (rc : ℕ → F × F × F) :
    (k w : ℕ) → (vs : List (Variable × Variable × Variable)) → (hw : vs.length = 5 * w + 1) →
      (rowsFromStates rc k vs)[w]'(by rw [rowsFromStates_length rc k w vs hw]; omega) =
        PoseidonConstraint.finalRow (vs[5 * w]'(by omega))
  | _, 0, [_], _ => rfl
  | k, w + 1, _ :: _ :: _ :: _ :: _ :: rest, hw => by
    have hw' : rest.length = 5 * w + 1 := by simp only [List.length_cons] at hw; omega
    have hb : w < (rowsFromStates rc (k + 1) rest).length := by
      rw [rowsFromStates_length rc (k + 1) w rest hw']
      omega
    show (rowsFromStates rc (k + 1) rest)[w]'hb =
      PoseidonConstraint.finalRow (rest[5 * w]'(by omega))
    exact rowsFromStates_final rc (k + 1) w rest hw'
  | _, 0, [], hw => absurd hw (show ¬ (0 = 5 * 0 + 1) by omega)
  | _, 0, _ :: _ :: rest, hw => absurd hw (show ¬ (rest.length + 1 + 1 = 5 * 0 + 1) by omega)
  | _, w + 1, [], hw => absurd hw (show ¬ (0 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_], hw => absurd hw (show ¬ (1 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_, _], hw => absurd hw (show ¬ (2 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_, _, _], hw => absurd hw (show ¬ (3 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_, _, _, _], hw => absurd hw (show ¬ (4 = 5 * (w + 1) + 1) by omega)

/-- The reading of one state: its three variables read as its operands. -/
private theorem records_reduceState (t : FVar F × FVar F × FVar F) :
    Records (reduceState t : RecordingBuilder F (Variable × Variable × Variable)) fun v es =>
      ∀ V : Valuation F, ReductionFacts V es →
        V v.1 = t.1.val V ∧ V v.2.1 = t.2.1.val V ∧ V v.2.2 = t.2.2.val V := by
  unfold reduceState
  refine records_bind (records_reduceToVariable _) fun a es0 h0 => ?_
  refine records_bind (records_reduceToVariable _) fun b es1 h1 => ?_
  refine records_bind (records_reduceToVariable _) fun c es2 h2 => ?_
  refine records_pure _ fun V hV => ?_
  obtain ⟨f0, hV⟩ := facts_append hV
  obtain ⟨f1, hV⟩ := facts_append hV
  obtain ⟨f2, -⟩ := facts_append hV
  exact ⟨h0 V f0, h1 V f1, h2 V f2⟩

/-- The reading of the states: index by index. -/
private theorem records_reduceStates :
    (ts : List (FVar F × FVar F × FVar F)) →
      Records (reduceStates ts : RecordingBuilder F (List (Variable × Variable × Variable)))
        fun vs es => vs.length = ts.length ∧ ∀ V : Valuation F, ReductionFacts V es →
          ∀ (i : Nat) (hi : i < ts.length) (hi' : i < vs.length),
            V vs[i].1 = ts[i].1.val V ∧ V vs[i].2.1 = ts[i].2.1.val V ∧
              V vs[i].2.2 = ts[i].2.2.val V
  | [] => records_pure _ ⟨rfl, fun _ _ _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | t :: ts => by
    unfold reduceStates
    refine records_bind (records_reduceState t) fun v es1 h1 => ?_
    refine records_bind (records_reduceStates ts) fun vs es2 h2 => ?_
    refine records_pure _ ⟨by simp [h2.1], fun V hV i hi hi' => ?_⟩
    obtain ⟨f1, hV⟩ := facts_append hV
    obtain ⟨f2, -⟩ := facts_append hV
    cases i with
    | zero => exact h1 V f1
    | succ k => exact h2.2 V f2 k (by simpa using hi) (by simpa using hi')

/-- A Poseidon block's recorded reduction: its rows are the chunking of its pinned states,
which read as the states. -/
private theorem records_poseidon (c : PoseidonConstraint F) :
    Records (c.reduce : RecordingBuilder F (List (KimchiRow F))) fun rows es =>
      ∃ vs : List (Variable × Variable × Variable), vs.length = c.state.length ∧
        rows = rowsFromStates (fun i => c.rc.getD i (0, 0, 0)) 0 vs ∧
        ∀ V : Valuation F, ReductionFacts V es →
          ∀ (i : Nat) (hi : i < c.state.length) (hi' : i < vs.length),
            V vs[i].1 = c.state[i].1.val V ∧ V vs[i].2.1 = c.state[i].2.1.val V ∧
              V vs[i].2.2 = c.state[i].2.2.val V := by
  unfold PoseidonConstraint.reduce
  refine records_bind (records_reduceStates c.state) fun vs es h => ?_
  refine records_pure _ ⟨vs, h.1, rfl, fun V hV => h.2 V (facts_append hV).1⟩

private theorem poseidon_rows (nv : Variable) (aux : AuxState F) (c : PoseidonConstraint F) :
    ∃ vs : List (Variable × Variable × Variable), vs.length = c.state.length ∧
      (recordReduction nv aux c.reduce).result =
        rowsFromStates (fun i => c.rc.getD i (0, 0, 0)) 0 vs ∧
      ∀ V : Valuation F, ReductionFacts V (recordReduction nv aux c.reduce).events →
        ∀ (i : Nat) (hi : i < c.state.length) (hi' : i < vs.length),
          V vs[i].1 = c.state[i].1.val V ∧ V vs[i].2.1 = c.state[i].2.1.val V ∧
            V vs[i].2.2 = c.state[i].2.2.val V :=
  recordReduction_of_records (records_poseidon c) nv aux

/-- A Poseidon block's recorded reduction emits one row per window and a terminal row. -/
theorem poseidon_result_length (nv : Variable) (aux : AuxState F) (c : PoseidonConstraint F)
    (h : c.state.length % 5 = 1) :
    (recordReduction nv aux c.reduce).result.length = c.state.length / 5 + 1 := by
  obtain ⟨vs, hvs, hrows, -⟩ := poseidon_rows nv aux c
  rw [hrows, rowsFromStates_length _ 0 (c.state.length / 5) vs (by omega)]

/-- Every window's row a Poseidon block's recorded reduction emits is a `poseidon` row. -/
theorem poseidon_kind (nv : Variable) (aux : AuxState F) (c : PoseidonConstraint F)
    (h : c.state.length % 5 = 1) (k : Fin (c.state.length / 5)) :
    ((recordReduction nv aux c.reduce).result[k.val]'(by
      rw [poseidon_result_length nv aux c h]; omega)).kind = .poseidon := by
  obtain ⟨vs, hvs, hrows, -⟩ := poseidon_rows nv aux c
  rw [List.getElem_of_eq hrows, rowsFromStates_window _ 0 (c.state.length / 5) vs (by omega)
    k.val k.isLt]
  rfl

/-- A window's row carries its five rounds' constants as its coefficients, in the gate's
reading. -/
theorem poseidon_coeffs (nv : Variable) (aux : AuxState F) (c : PoseidonConstraint F)
    (h : c.state.length % 5 = 1) (k : Fin (c.state.length / 5)) (j : Fin 5) :
    (((recordReduction nv aux c.reduce).result[k.val]'(by
        rw [poseidon_result_length nv aux c h]; omega)).coeffs.getD (3 * j.val) 0,
      ((recordReduction nv aux c.reduce).result[k.val]'(by
        rw [poseidon_result_length nv aux c h]; omega)).coeffs.getD (3 * j.val + 1) 0,
      ((recordReduction nv aux c.reduce).result[k.val]'(by
        rw [poseidon_result_length nv aux c h]; omega)).coeffs.getD (3 * j.val + 2) 0) =
      Poseidon.rcRow c.rc k.val j := by
  obtain ⟨vs, hvs, hrows, -⟩ := poseidon_rows nv aux c
  rw [List.getElem_of_eq hrows, rowsFromStates_window _ 0 (c.state.length / 5) vs (by omega)
    k.val k.isLt, Nat.zero_add]
  fin_cases j <;> rfl

/-- Each window's row carries a variable in every cell. -/
theorem poseidon_cell_some_window (nv : Variable) (aux : AuxState F) (c : PoseidonConstraint F)
    (h : c.state.length % 5 = 1) (k : Fin (c.state.length / 5)) (j : Fin wCols) :
    ∃ v, ((recordReduction nv aux c.reduce).result[k.val]'(by
      rw [poseidon_result_length nv aux c h]; omega)).vars[j] = some v := by
  obtain ⟨vs, hvs, hrows, -⟩ := poseidon_rows nv aux c
  rw [List.getElem_of_eq hrows, rowsFromStates_window _ 0 (c.state.length / 5) vs (by omega)
    k.val k.isLt]
  fin_cases j <;> exact ⟨_, rfl⟩

/-- The row after each window's, the next window's or the terminal row, carries a variable in
its three output cells. -/
theorem poseidon_cell_some_next (nv : Variable) (aux : AuxState F) (c : PoseidonConstraint F)
    (h : c.state.length % 5 = 1) (k : Fin (c.state.length / 5)) (j : Fin wCols)
    (hj : j.val < 3) :
    ∃ v, ((recordReduction nv aux c.reduce).result[k.val + 1]'(by
      rw [poseidon_result_length nv aux c h]; omega)).vars[j] = some v := by
  obtain ⟨vs, hvs, hrows, -⟩ := poseidon_rows nv aux c
  rw [List.getElem_of_eq hrows]
  rcases Nat.lt_or_ge (k.val + 1) (c.state.length / 5) with hlt | hge
  · rw [rowsFromStates_window _ 0 (c.state.length / 5) vs (by omega) (k.val + 1) hlt]
    fin_cases j <;> exact ⟨_, rfl⟩
  · rw [getElem_congr_idx (show k.val + 1 = c.state.length / 5 by have := k.isLt; omega),
      rowsFromStates_final _ 0 (c.state.length / 5) vs (by omega)]
    fin_cases j
    all_goals first | exact ⟨_, rfl⟩ | exact absurd hj (by decide)

omit [DecidableEq F] in
/-- The chain from the rows: the gate holds at each window's row with its successor at the
window's constants, every window reads as its six states, and the state list has the shape. -/
private theorem poseidonChain_of_rows (M : Kimchi.Gate.Poseidon.Mds F) (rc : List (F × F × F))
    (V : Valuation F) :
    (k w : ℕ) → (states : List (F × F × F)) → (rows : List (KimchiRow F)) →
      (hw : states.length = 5 * w + 1) → (hlen : rows.length = w + 1) →
      (∀ (j : ℕ) (hj : j < w), Kimchi.Gate.Poseidon.Holds M (Poseidon.rcRow rc (k + j))
        (Kimchi.Lift.Gate.Poseidon.cellMap (rowValues V (rows[j]'(by omega)))
          (rowValues V (rows[j + 1]'(by omega))))) →
      (∀ (j : ℕ) (hj : j < w),
        Kimchi.Lift.Gate.Poseidon.cellMap (rowValues V (rows[j]'(by omega)))
          (rowValues V (rows[j + 1]'(by omega))) =
        ⟨states[5 * j]'(by omega), states[5 * j + 1]'(by omega), states[5 * j + 2]'(by omega),
          states[5 * j + 3]'(by omega), states[5 * j + 4]'(by omega),
          states[5 * (j + 1)]'(by omega)⟩) →
      Poseidon.chainHolds M rc k states
  | _, 0, [_], _, _, _, _, _ => trivial
  | k, w + 1, s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: rest, rows, hw, hlen, hg, hread => by
    have hw' : (s5 :: rest).length = 5 * w + 1 := by
      simp only [List.length_cons] at hw ⊢
      omega
    show Kimchi.Gate.Poseidon.Holds M (Poseidon.rcRow rc k) ⟨s0, s1, s2, s3, s4, s5⟩ ∧
      Poseidon.chainHolds M rc (k + 1) (s5 :: rest)
    refine ⟨?_, ?_⟩
    · have h := hg 0 (by omega)
      rw [hread 0 (by omega)] at h
      exact h
    · cases rows with
      | nil => simp at hlen
      | cons row0 rows' =>
        refine poseidonChain_of_rows M rc V (k + 1) w (s5 :: rest) rows' hw'
          (by simpa using hlen) (fun j hj => ?_) (fun j hj => ?_)
        · have e : k + 1 + j = k + (j + 1) := by omega
          rw [e]
          exact hg (j + 1) (by omega)
        · exact hread (j + 1) (by omega)
  | _, 0, [], _, hw, _, _, _ => absurd hw (show ¬ (0 = 5 * 0 + 1) by omega)
  | _, 0, _ :: _ :: rest, _, hw, _, _, _ =>
    absurd hw (show ¬ (rest.length + 1 + 1 = 5 * 0 + 1) by omega)
  | _, w + 1, [], _, hw, _, _, _ => absurd hw (show ¬ (0 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_], _, hw, _, _, _ => absurd hw (show ¬ (1 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_, _], _, hw, _, _, _ => absurd hw (show ¬ (2 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_, _, _], _, hw, _, _, _ => absurd hw (show ¬ (3 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_, _, _, _], _, hw, _, _, _ => absurd hw (show ¬ (4 = 5 * (w + 1) + 1) by omega)
  | _, w + 1, [_, _, _, _, _], _, hw, _, _, _ =>
    absurd hw (show ¬ (5 = 5 * (w + 1) + 1) by omega)

/-- The gate's predicate at every window's row with its successor and constants, read at a
valuation where the recorded events hold, is the source constraint's chain. -/
theorem poseidon_holds_of_reductionFacts (nv : Variable) (aux : AuxState F)
    (c : PoseidonConstraint F) (V : Valuation F) (h : c.state.length % 5 = 1)
    (hf : ReductionFacts V (recordReduction nv aux c.reduce).events)
    (hg : ∀ k : Fin (c.state.length / 5), Kimchi.Gate.Poseidon.Holds (Poseidon.mdsOf c.mds)
      (Poseidon.rcRow c.rc k.val) (Kimchi.Lift.Gate.Poseidon.cellMap
        (rowValues V ((recordReduction nv aux c.reduce).result[k.val]'(by
          rw [poseidon_result_length nv aux c h]; omega)))
        (rowValues V ((recordReduction nv aux c.reduce).result[k.val + 1]'(by
          rw [poseidon_result_length nv aux c h]; omega))))) :
    KimchiConstraint.Holds V (.poseidon c) := by
  show Poseidon.chainHolds (Poseidon.mdsOf c.mds) c.rc 0 (Poseidon.read V c)
  obtain ⟨vs, hvs, hrows, hV⟩ := poseidon_rows nv aux c
  have hV' := hV V hf
  have hw : c.state.length = 5 * (c.state.length / 5) + 1 := by omega
  refine poseidonChain_of_rows (Poseidon.mdsOf c.mds) c.rc V 0 (c.state.length / 5)
    (Poseidon.read V c) (recordReduction nv aux c.reduce).result
    (by simp only [Poseidon.read, List.length_map]; exact hw) (poseidon_result_length nv aux c h)
    (fun j hj => by rw [Nat.zero_add]; exact hg ⟨j, hj⟩) (fun j hj => ?_)
  obtain ⟨a0, b0, c0⟩ := hV' (5 * j) (by omega) (by omega)
  obtain ⟨a1, b1, c1⟩ := hV' (5 * j + 1) (by omega) (by omega)
  obtain ⟨a2, b2, c2⟩ := hV' (5 * j + 2) (by omega) (by omega)
  obtain ⟨a3, b3, c3⟩ := hV' (5 * j + 3) (by omega) (by omega)
  obtain ⟨a4, b4, c4⟩ := hV' (5 * j + 4) (by omega) (by omega)
  obtain ⟨a5, b5, c5⟩ := hV' (5 * (j + 1)) (by omega) (by omega)
  rw [List.getElem_of_eq hrows, List.getElem_of_eq hrows,
    rowsFromStates_window _ 0 (c.state.length / 5) vs (by omega) j hj]
  rcases Nat.lt_or_ge (j + 1) (c.state.length / 5) with hlt | hge
  · rw [rowsFromStates_window _ 0 (c.state.length / 5) vs (by omega) (j + 1) hlt]
    simp [Kimchi.Lift.Gate.Poseidon.cellMap, rowValues, addRoundState, Poseidon.read, a0, b0, c0,
      a1, b1, c1, a2, b2, c2, a3, b3, c3, a4, b4, c4, a5, b5, c5]
  · have e : j + 1 = c.state.length / 5 := by omega
    rw [getElem_congr_idx e, rowsFromStates_final _ 0 (c.state.length / 5) vs (by omega)]
    have e5 : 5 * (c.state.length / 5) = 5 * (j + 1) := by omega
    simp only [getElem_congr_idx e5]
    simp [Kimchi.Lift.Gate.Poseidon.cellMap, rowValues, addRoundState,
      PoseidonConstraint.finalRow, Poseidon.read, a0, b0, c0, a1, b1, c1, a2, b2, c2, a3, b3, c3,
      a4, b4, c4, a5, b5, c5]

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

omit [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] in
/-- An operand with a bare-variable form is that variable. -/
theorem _root_.Snarky.CVar.var?_isSome {x : CVar F} (h : x.var?.isSome) : ∃ v, x = .var v := by
  cases x with
  | var v => exact ⟨v, rfl⟩
  | _ => exact absurd h (by simp [CVar.var?])

omit [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] in
/-- A placed cell of a row is its operand. -/
theorem cellsOf_getElem_lt (ops : List (Option (FVar F))) (k : Nat) (hk : k < ops.length)
    (hk' : k < wCols) : (cellsOf ops)[k] = ops[k] := by
  show (ops.take wCols ++ List.replicate (wCols - (ops.take wCols).length) none)[k]'(by
    simp only [List.length_append, List.length_replicate, List.length_take]; omega) = ops[k]
  rw [List.getElem_append_left (by simp only [List.length_take]; omega), List.getElem_take]

omit [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] in
/-- The layout of `5w + 1` states: `w` window rows then the terminal row. -/
private theorem rowOperandsList_length :
    (w : ℕ) → (ts : List (FVar F × FVar F × FVar F)) → ts.length = 5 * w + 1 →
      (Poseidon.rowOperandsList ts).length = w + 1
  | 0, [_], _ => rfl
  | w + 1, _ :: _ :: _ :: _ :: _ :: rest, hw => by
    show (Poseidon.rowOperandsList rest).length + 1 = w + 1 + 1
    rw [rowOperandsList_length w rest (by simp only [List.length_cons] at hw; omega)]
  | 0, [], hw => absurd hw (show ¬ (0 = 5 * 0 + 1) by omega)
  | 0, _ :: _ :: rest, hw => absurd hw (show ¬ (rest.length + 1 + 1 = 5 * 0 + 1) by omega)
  | w + 1, [], hw => absurd hw (show ¬ (0 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_], hw => absurd hw (show ¬ (1 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_, _], hw => absurd hw (show ¬ (2 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_, _, _], hw => absurd hw (show ¬ (3 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_, _, _, _], hw => absurd hw (show ¬ (4 = 5 * (w + 1) + 1) by omega)

omit [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] in
/-- Row `j` of the layout is the window over states `5j` to `5j + 4`. -/
private theorem rowOperandsList_window :
    (w : ℕ) → (ts : List (FVar F × FVar F × FVar F)) → (hw : ts.length = 5 * w + 1) →
      (j : ℕ) → (hj : j < w) →
      (Poseidon.rowOperandsList ts)[j]'(by rw [rowOperandsList_length w ts hw]; omega) =
        cellsOf (PoseidonConstraint.windowCells (ts[5 * j]'(by omega)) (ts[5 * j + 1]'(by omega))
          (ts[5 * j + 2]'(by omega)) (ts[5 * j + 3]'(by omega)) (ts[5 * j + 4]'(by omega)))
  | _ + 1, _ :: _ :: _ :: _ :: _ :: _, _, 0, _ => rfl
  | w + 1, q0 :: q1 :: q2 :: q3 :: q4 :: rest, hw, j + 1, hj => by
    have hw' : rest.length = 5 * w + 1 := by simp only [List.length_cons] at hw; omega
    have hb : j < (Poseidon.rowOperandsList rest).length := by
      rw [rowOperandsList_length w rest hw']
      omega
    show (Poseidon.rowOperandsList rest)[j]'hb =
      cellsOf (PoseidonConstraint.windowCells (rest[5 * j]'(by omega)) (rest[5 * j + 1]'(by omega))
        (rest[5 * j + 2]'(by omega)) (rest[5 * j + 3]'(by omega)) (rest[5 * j + 4]'(by omega)))
    exact rowOperandsList_window w rest hw' j (by omega)
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | w + 1, [], hw, _, _ => absurd hw (show ¬ (0 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_], hw, _, _ => absurd hw (show ¬ (1 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_, _], hw, _, _ => absurd hw (show ¬ (2 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_, _, _], hw, _, _ => absurd hw (show ¬ (3 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_, _, _, _], hw, _, _ => absurd hw (show ¬ (4 = 5 * (w + 1) + 1) by omega)

omit [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] in
/-- Row `w` of the layout is the terminal row over the last state. -/
private theorem rowOperandsList_final :
    (w : ℕ) → (ts : List (FVar F × FVar F × FVar F)) → (hw : ts.length = 5 * w + 1) →
      (Poseidon.rowOperandsList ts)[w]'(by rw [rowOperandsList_length w ts hw]; omega) =
        cellsOf (PoseidonConstraint.finalCells (ts[5 * w]'(by omega)))
  | 0, [_], _ => rfl
  | w + 1, _ :: _ :: _ :: _ :: _ :: rest, hw => by
    have hw' : rest.length = 5 * w + 1 := by simp only [List.length_cons] at hw; omega
    have hb : w < (Poseidon.rowOperandsList rest).length := by
      rw [rowOperandsList_length w rest hw']
      omega
    show (Poseidon.rowOperandsList rest)[w]'hb =
      cellsOf (PoseidonConstraint.finalCells (rest[5 * w]'(by omega)))
    exact rowOperandsList_final w rest hw'
  | 0, [], hw => absurd hw (show ¬ (0 = 5 * 0 + 1) by omega)
  | 0, _ :: _ :: rest, hw => absurd hw (show ¬ (rest.length + 1 + 1 = 5 * 0 + 1) by omega)
  | w + 1, [], hw => absurd hw (show ¬ (0 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_], hw => absurd hw (show ¬ (1 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_, _], hw => absurd hw (show ¬ (2 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_, _, _], hw => absurd hw (show ¬ (3 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_, _, _, _], hw => absurd hw (show ¬ (4 = 5 * (w + 1) + 1) by omega)

/-- The operands a constraint places, in row and cell order. -/
def KimchiConstraint.placedOperands (c : KimchiConstraint F) : List (FVar F) :=
  c.rowOperands.toList.flatMap fun row => row.toList.filterMap id

omit [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] in
/-- An operand of a row within the column count is a cell of it. -/
theorem mem_cellsOf {ops : List (Option (FVar F))} (h : ops.length ≤ wCols) {o : Option (FVar F)}
    (ho : o ∈ ops) : o ∈ (cellsOf ops).toList := by
  show o ∈ ops.take wCols ++ List.replicate (wCols - (ops.take wCols).length) none
  rw [List.take_of_length_le h]
  exact List.mem_append_left _ ho

omit [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] in
/-- An operand in a cell of some row is a placed operand. -/
theorem mem_placedOperands {c : KimchiConstraint F} {row : Vector (Option (FVar F)) wCols}
    (hrow : row ∈ c.rowOperands.toList) {x : FVar F} (hx : some x ∈ row.toList) :
    x ∈ c.placedOperands :=
  List.mem_flatMap.mpr ⟨row, hrow, List.mem_filterMap.mpr ⟨some x, hx, rfl⟩⟩

omit [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] in
/-- Every state of a `5w + 1` list has its three operands in some row of the layout. -/
private theorem mem_rowOperandsList :
    (w : ℕ) → (ts : List (FVar F × FVar F × FVar F)) → ts.length = 5 * w + 1 →
      ∀ t ∈ ts, ∃ row ∈ Poseidon.rowOperandsList ts,
        some t.1 ∈ row.toList ∧ some t.2.1 ∈ row.toList ∧ some t.2.2 ∈ row.toList
  | 0, [s], _, t, ht => by
    rw [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_singleton_self _, mem_cellsOf (by simp [PoseidonConstraint.finalCells])
      (by simp [PoseidonConstraint.finalCells]), mem_cellsOf (by simp
      [PoseidonConstraint.finalCells]) (by simp [PoseidonConstraint.finalCells]),
      mem_cellsOf (by simp [PoseidonConstraint.finalCells])
      (by simp [PoseidonConstraint.finalCells])⟩
  | w + 1, q0 :: q1 :: q2 :: q3 :: q4 :: rest, hw, t, ht => by
    have hw' : rest.length = 5 * w + 1 := by simp only [List.length_cons] at hw; omega
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | ht
    · exact ⟨_, List.mem_cons_self .., mem_cellsOf (by simp [PoseidonConstraint.windowCells])
        (by simp [PoseidonConstraint.windowCells]), mem_cellsOf
        (by simp [PoseidonConstraint.windowCells]) (by simp [PoseidonConstraint.windowCells]),
        mem_cellsOf (by simp [PoseidonConstraint.windowCells])
        (by simp [PoseidonConstraint.windowCells])⟩
    · exact ⟨_, List.mem_cons_self .., mem_cellsOf (by simp [PoseidonConstraint.windowCells])
        (by simp [PoseidonConstraint.windowCells]), mem_cellsOf
        (by simp [PoseidonConstraint.windowCells]) (by simp [PoseidonConstraint.windowCells]),
        mem_cellsOf (by simp [PoseidonConstraint.windowCells])
        (by simp [PoseidonConstraint.windowCells])⟩
    · exact ⟨_, List.mem_cons_self .., mem_cellsOf (by simp [PoseidonConstraint.windowCells])
        (by simp [PoseidonConstraint.windowCells]), mem_cellsOf
        (by simp [PoseidonConstraint.windowCells]) (by simp [PoseidonConstraint.windowCells]),
        mem_cellsOf (by simp [PoseidonConstraint.windowCells])
        (by simp [PoseidonConstraint.windowCells])⟩
    · exact ⟨_, List.mem_cons_self .., mem_cellsOf (by simp [PoseidonConstraint.windowCells])
        (by simp [PoseidonConstraint.windowCells]), mem_cellsOf
        (by simp [PoseidonConstraint.windowCells]) (by simp [PoseidonConstraint.windowCells]),
        mem_cellsOf (by simp [PoseidonConstraint.windowCells])
        (by simp [PoseidonConstraint.windowCells])⟩
    · exact ⟨_, List.mem_cons_self .., mem_cellsOf (by simp [PoseidonConstraint.windowCells])
        (by simp [PoseidonConstraint.windowCells]), mem_cellsOf
        (by simp [PoseidonConstraint.windowCells]) (by simp [PoseidonConstraint.windowCells]),
        mem_cellsOf (by simp [PoseidonConstraint.windowCells])
        (by simp [PoseidonConstraint.windowCells])⟩
    · exact (mem_rowOperandsList w rest hw' t ht).imp fun row ⟨hrow, h⟩ =>
        ⟨List.mem_cons_of_mem _ hrow, h⟩
  | 0, [], hw, _, _ => absurd hw (show ¬ (0 = 5 * 0 + 1) by omega)
  | 0, _ :: _ :: rest, hw, _, _ => absurd hw (show ¬ (rest.length + 1 + 1 = 5 * 0 + 1) by omega)
  | w + 1, [], hw, _, _ => absurd hw (show ¬ (0 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_], hw, _, _ => absurd hw (show ¬ (1 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_, _], hw, _, _ => absurd hw (show ¬ (2 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_, _, _], hw, _, _ => absurd hw (show ¬ (3 = 5 * (w + 1) + 1) by omega)
  | w + 1, [_, _, _, _], hw, _, _ => absurd hw (show ¬ (4 = 5 * (w + 1) + 1) by omega)

omit [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] in
/-- A complete addition's unwired operands are the bare ones among `sameX`, `s`, `infZ`,
`x21Inv`. -/
theorem addComplete_unwiredVars (c : AddComplete F) :
    (KimchiConstraint.addComplete c).unwiredVars =
      (c.operands.toList.drop permCols).filterMap CVar.var? := by
  show (((cellsOf (c.operands.toList.map some)).toList.drop permCols).filterMap
    fun o => o.bind CVar.var?) ++ [] = _
  rw [List.append_nil]
  rfl

/-- A row cell against its placed operand, within the allocations `A`: both empty, or the
cell a variable that is a term of the operand or an allocation, and the operand's own
variable when the operand is bare. -/
def CellOf (A : List Variable) : Option Variable → Option (FVar F) → Prop
  | none, none => True
  | some v, some x => (v ∈ x.termVars ∨ v ∈ A) ∧ ∀ w, x = .var w → v = w
  | _, _ => False

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

/-- A constraint's recorded reduction placed: every name of its events is an allocation or a
term of a placed operand that is not that bare variable, and its gate rows correspond cell by
cell to its placed operands. -/
def Placed (nv : Variable) (aux : AuxState F) (c : KimchiConstraint F) : Prop :=
  (∀ e ∈ (recordReduction nv aux c.reduce).events, ∀ w ∈ e.names,
    w ∈ allocs (recordReduction nv aux c.reduce).events ∨
      ∃ x ∈ c.placedOperands, w ∈ x.termVars ∧ x ≠ .var w) ∧
  ∃ hlen : (toKimchiRows (F := F) (recordReduction nv aux c.reduce).result).length = c.rowCount,
    ∀ (i : Fin c.rowCount) (j : Fin wCols),
      CellOf (allocs (recordReduction nv aux c.reduce).events)
        ((toKimchiRows (F := F) (recordReduction nv aux c.reduce).result)[i.val]'(
          lt_of_lt_of_eq i.isLt hlen.symm)).vars[j]
        (c.rowOperands[i])[j]

/-- The walk of a complete addition: every name is an allocation or a term of an operand that
is not that bare variable, and the row's cells are its operands' variables cell by cell. -/
private theorem records_addComplete_names (c : AddComplete F) :
    Records (c.reduce : RecordingBuilder F (Rows F)) fun row es =>
      (∀ e ∈ es, ∀ w ∈ e.names, w ∈ allocs es ∨
        ∃ x ∈ c.operands.toList, w ∈ x.termVars ∧ x ≠ .var w) ∧
      ∀ j : Fin wCols, CellOf (allocs es) row.row.vars[j]
        (cellsOf (c.operands.toList.map some))[j] := by
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
  refine ⟨fun e he w hw => ?_, fun j => ?_⟩
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
    fin_cases j
    exacts [⟨h1'.2.1, h1'.2.2.2.1⟩, ⟨h1'.2.2.1, h1'.2.2.2.2⟩, ⟨h2'.2.1, h2'.2.2.2.1⟩,
      ⟨h2'.2.2.1, h2'.2.2.2.2⟩, ⟨h3'.2.1, h3'.2.2.2.1⟩, ⟨h3'.2.2.1, h3'.2.2.2.2⟩,
      ⟨h8'.2.1, h8'.2.2⟩, ⟨h7'.2.1, h7'.2.2⟩, ⟨h6'.2.1, h6'.2.2⟩, ⟨h5'.2.1, h5'.2.2⟩,
      ⟨h4'.2.1, h4'.2.2⟩, trivial, trivial, trivial, trivial]

/-- A complete addition's recorded reduction is placed: its names are allocations or terms
of operands that are not that bare variable, and its one row's cells are its operands'
variables cell by cell. -/
theorem addComplete_placed (nv : Variable) (aux : AuxState F) (c : AddComplete F) :
    Placed nv aux (.addComplete c) := by
  obtain ⟨hn, hc⟩ := recordReduction_of_records (records_addComplete_names c) nv aux
  have hplaced : (KimchiConstraint.addComplete c).placedOperands = c.operands.toList := rfl
  refine ⟨fun e he w hw => (hn e he w hw).imp_right fun ⟨x, hx, h⟩ => ⟨x, hplaced ▸ hx, h⟩, rfl,
    fun i j => ?_⟩
  fin_cases i
  exact hc j

/-- A cell's correspondence within more allocations. -/
private theorem cellOf_mono {A A' : List Variable} (hA : ∀ u ∈ A, u ∈ A') {cell : Option Variable}
    {o : Option (FVar F)} (h : CellOf A cell o) : CellOf A' cell o := by
  cases cell with
  | none =>
    cases o with
    | none => trivial
    | some _ => exact h.elim
  | some v =>
    cases o with
    | none => exact h.elim
    | some x => exact ⟨h.1.imp_right (hA v), h.2⟩

/-- The walk of one decomposition round: every name is an allocation or a term of an operand
that is not that bare variable, and the row's cells are its operands' variables cell by cell. -/
private theorem records_endoScalarRound_names (r : EndoScalarRound F) :
    Records (r.reduce : RecordingBuilder F (KimchiRow F)) fun row es =>
      (∀ e ∈ es, ∀ w ∈ e.names, w ∈ allocs es ∨
        ∃ x ∈ r.operands.toList, w ∈ x.termVars ∧ x ≠ .var w) ∧
      ∀ j : Fin wCols, CellOf (allocs es) row.vars[j]
        (cellsOf (r.operands.toList.map some))[j] := by
  unfold EndoScalarRound.reduce
  refine records_bind (records_reduceToVariable_names _) fun x0 es0 h0 => ?_
  refine records_bind (records_reduceToVariable_names _) fun x1 es1 h1 => ?_
  refine records_bind (records_reduceToVariable_names _) fun x2 es2 h2 => ?_
  refine records_bind (records_reduceToVariable_names _) fun x3 es3 h3 => ?_
  refine records_bind (records_reduceToVariable_names _) fun x4 es4 h4 => ?_
  refine records_bind (records_reduceToVariable_names _) fun x5 es5 h5 => ?_
  refine records_bind (records_reduceToVariable_names _) fun x6 es6 h6 => ?_
  refine records_bind (records_reduceToVariable_names _) fun x7 es7 h7 => ?_
  refine records_bind (records_reduceToVariable_names _) fun b8 es8 h8 => ?_
  refine records_bind (records_reduceToVariable_names _) fun a8 es9 h9 => ?_
  refine records_bind (records_reduceToVariable_names _) fun b0 es10 h10 => ?_
  refine records_bind (records_reduceToVariable_names _) fun a0 es11 h11 => ?_
  refine records_bind (records_reduceToVariable_names _) fun n8 es12 h12 => ?_
  refine records_bind (records_reduceToVariable_names _) fun n0 es13 h13 => ?_
  refine records_pure _ ?_
  have h0' := operandNames_of h0 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have h1' := operandNames_of h1 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have h2' := operandNames_of h2 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have h3' := operandNames_of h3 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have h4' := operandNames_of h4 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have h5' := operandNames_of h5 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have h6' := operandNames_of h6 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have h7' := operandNames_of h7 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have h8' := operandNames_of h8 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have h9' := operandNames_of h9 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have h10' := operandNames_of h10 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have h11' := operandNames_of h11 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have h12' := operandNames_of h12 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have h13' := operandNames_of h13 (A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++
    (es6 ++ (es7 ++ (es8 ++ (es9 ++ (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))))
    fun u hu => by simp [allocs_append, hu]
  have hops : r.operands.toList = [r.n0, r.n8, r.a0, r.b0, r.a8, r.b8, r.xs[0], r.xs[1], r.xs[2],
      r.xs[3], r.xs[4], r.xs[5], r.xs[6], r.xs[7]] := rfl
  refine ⟨fun e he w hw => ?_, fun j => ?_⟩
  · simp only [List.append_nil, List.mem_append] at he
    rw [hops]
    rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he
    · exact (h0'.1 e he w hw).imp_right fun h => ⟨r.xs[0], by simp, h⟩
    · exact (h1'.1 e he w hw).imp_right fun h => ⟨r.xs[1], by simp, h⟩
    · exact (h2'.1 e he w hw).imp_right fun h => ⟨r.xs[2], by simp, h⟩
    · exact (h3'.1 e he w hw).imp_right fun h => ⟨r.xs[3], by simp, h⟩
    · exact (h4'.1 e he w hw).imp_right fun h => ⟨r.xs[4], by simp, h⟩
    · exact (h5'.1 e he w hw).imp_right fun h => ⟨r.xs[5], by simp, h⟩
    · exact (h6'.1 e he w hw).imp_right fun h => ⟨r.xs[6], by simp, h⟩
    · exact (h7'.1 e he w hw).imp_right fun h => ⟨r.xs[7], by simp, h⟩
    · exact (h8'.1 e he w hw).imp_right fun h => ⟨r.b8, by simp, h⟩
    · exact (h9'.1 e he w hw).imp_right fun h => ⟨r.a8, by simp, h⟩
    · exact (h10'.1 e he w hw).imp_right fun h => ⟨r.b0, by simp, h⟩
    · exact (h11'.1 e he w hw).imp_right fun h => ⟨r.a0, by simp, h⟩
    · exact (h12'.1 e he w hw).imp_right fun h => ⟨r.n8, by simp, h⟩
    · exact (h13'.1 e he w hw).imp_right fun h => ⟨r.n0, by simp, h⟩
  · rw [hops]
    fin_cases j
    exacts [⟨h13'.2.1, h13'.2.2⟩, ⟨h12'.2.1, h12'.2.2⟩, ⟨h11'.2.1, h11'.2.2⟩,
      ⟨h10'.2.1, h10'.2.2⟩, ⟨h9'.2.1, h9'.2.2⟩, ⟨h8'.2.1, h8'.2.2⟩, ⟨h0'.2.1, h0'.2.2⟩,
      ⟨h1'.2.1, h1'.2.2⟩, ⟨h2'.2.1, h2'.2.2⟩, ⟨h3'.2.1, h3'.2.2⟩, ⟨h4'.2.1, h4'.2.2⟩,
      ⟨h5'.2.1, h5'.2.2⟩, ⟨h6'.2.1, h6'.2.2⟩, ⟨h7'.2.1, h7'.2.2⟩, trivial]

/-- The walk of a decomposition: round by round, each row against its round's operands. -/
private theorem records_endoScalar_names :
    (rounds : EndoScalar F) →
      Records (EndoScalar.reduce rounds : RecordingBuilder F (List (KimchiRow F))) fun rows es =>
        (∀ e ∈ es, ∀ w ∈ e.names, w ∈ allocs es ∨
          ∃ r ∈ rounds, ∃ x ∈ r.operands.toList, w ∈ x.termVars ∧ x ≠ .var w) ∧
        ∀ (i : Nat) (hi : i < rounds.length) (hi' : i < rows.length) (j : Fin wCols),
          CellOf (allocs es) rows[i].vars[j] (cellsOf (rounds[i].operands.toList.map some))[j]
  | [] => records_pure _ ⟨fun _ h => (List.not_mem_nil h).elim,
      fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | r :: rs => by
    unfold EndoScalar.reduce
    refine records_bind (records_endoScalarRound_names r) fun row es1 h1 => ?_
    refine records_bind (records_endoScalar_names rs) fun rest es2 h2 => ?_
    refine records_pure _ ⟨fun e he w hw => ?_, fun i hi hi' j => ?_⟩
    · simp only [List.append_nil, List.mem_append] at he
      rcases he with he | he
      · exact (h1.1 e he w hw).imp allocs_mono_left fun ⟨x, hx, h⟩ =>
          ⟨r, List.mem_cons_self .., x, hx, h⟩
      · exact (h2.1 e he w hw).imp (fun h => allocs_mono_right (allocs_mono_left h))
          fun ⟨r', hr', x, hx, h⟩ => ⟨r', List.mem_cons_of_mem _ hr', x, hx, h⟩
    · cases i with
      | zero => exact cellOf_mono (fun u hu => allocs_mono_left hu) (h1.2 j)
      | succ k =>
        exact cellOf_mono (fun u hu => allocs_mono_right (allocs_mono_left hu))
          (h2.2 k (by simpa using hi) (by simpa using hi') j)

/-- A decomposition's recorded reduction is placed: its names are allocations or terms of
its rounds' operands that are not that bare variable, and its rows' cells are the rounds'
operands' variables cell by cell. -/
theorem endoScalar_placed (nv : Variable) (aux : AuxState F) (rounds : EndoScalar F) :
    Placed nv aux (.endoScalar rounds) := by
  obtain ⟨hn, hc⟩ := recordReduction_of_records (records_endoScalar_names rounds) nv aux
  refine ⟨fun e he w hw => (hn e he w hw).imp_right fun ⟨r, hr, x, hx, h⟩ =>
    ⟨x, mem_placedOperands (List.mem_map.mpr ⟨r, hr, rfl⟩)
      (mem_cellsOf (by simp) (List.mem_map.mpr ⟨x, hx, rfl⟩)), h⟩, ?_, fun i j => ?_⟩
  · show (recordReduction nv aux (EndoScalar.reduce rounds)).result.length =
      (rounds.map fun r => cellsOf (r.operands.toList.map some)).length
    rw [List.length_map]
    exact endoScalar_result_length nv aux rounds
  · have hi : i.val < rounds.length := by
      have h := i.isLt
      simp only [KimchiConstraint.rowCount, KimchiConstraint.rowOperandsList,
        List.length_map] at h
      exact h
    have hrow : (KimchiConstraint.endoScalar rounds).rowOperands[i] =
        cellsOf (rounds[i.val].operands.toList.map some) := by
      show (rounds.map fun r => cellsOf (r.operands.toList.map some))[i.val] = _
      exact List.getElem_map _
    rw [hrow]
    exact hc i.val hi _ j

/-- Each emitted decomposition row's cells are its round's operands' variables cell by cell. -/
private theorem endoScalar_cells (nv : Variable) (aux : AuxState F) (rounds : EndoScalar F)
    (i : Fin rounds.length) (j : Fin wCols) :
    CellOf (allocs (recordReduction nv aux (EndoScalar.reduce rounds)).events)
      ((recordReduction nv aux (EndoScalar.reduce rounds)).result[i.val]'(by
        rw [endoScalar_result_length]; exact i.isLt)).vars[j]
      (cellsOf (rounds[i].operands.toList.map some))[j] :=
  (recordReduction_of_records (records_endoScalar_names rounds) nv aux).2 i.val i.isLt _ j

/-- Each emitted decomposition row carries a variable in each of its fourteen operand cells. -/
theorem endoScalar_cell_some (nv : Variable) (aux : AuxState F) (rounds : EndoScalar F)
    (i : Fin rounds.length) (k : Fin wCols) (hk : k.val < 14) :
    ∃ w, ((recordReduction nv aux (EndoScalar.reduce rounds)).result[i.val]'(by
      rw [endoScalar_result_length]; exact i.isLt)).vars[k] = some w := by
  have h := endoScalar_cells nv aux rounds i k
  have hop : (cellsOf (rounds[i].operands.toList.map some))[k] =
      some (rounds[i].operands.toList[k.val]'(by rw [Vector.length_toList]; omega)) := by
    show (cellsOf (rounds[i].operands.toList.map some))[k.val] = _
    rw [cellsOf_getElem_lt _ _ (by rw [List.length_map, Vector.length_toList]; omega) k.isLt,
      List.getElem_map]
  rw [hop] at h
  cases hlab : ((recordReduction nv aux (EndoScalar.reduce rounds)).result[i.val]'(by
      rw [endoScalar_result_length]; exact i.isLt)).vars[k] with
  | none =>
    rw [hlab] at h
    exact h.elim
  | some w => exact ⟨w, rfl⟩

/-- The walk of one scale round: every name is an allocation or a term of an operand that is
not that bare variable, and the two rows' cells are the round's operands' variables cell by
cell. -/
private theorem records_scaleRound_names (r : ScaleRound F) :
    Records (r.reduce : RecordingBuilder F (KimchiRow F × KimchiRow F)) fun pair es =>
      (∀ e ∈ es, ∀ w ∈ e.names, w ∈ allocs es ∨
        ∃ x, (some x ∈ r.cellsA ∨ some x ∈ r.cellsB) ∧ w ∈ x.termVars ∧ x ≠ .var w) ∧
      (∀ j : Fin wCols, CellOf (allocs es) pair.1.vars[j] (cellsOf r.cellsA)[j]) ∧
      ∀ j : Fin wCols, CellOf (allocs es) pair.2.vars[j] (cellsOf r.cellsB)[j] := by
  unfold ScaleRound.reduce
  refine records_bind (records_reduceToVariable_names _) fun a0x es0 h0 => ?_
  refine records_bind (records_reduceToVariable_names _) fun a0y es1 h1 => ?_
  refine records_bind (records_reduceToVariable_names _) fun a1x es2 h2 => ?_
  refine records_bind (records_reduceToVariable_names _) fun a1y es3 h3 => ?_
  refine records_bind (records_reduceToVariable_names _) fun a2x es4 h4 => ?_
  refine records_bind (records_reduceToVariable_names _) fun a2y es5 h5 => ?_
  refine records_bind (records_reduceToVariable_names _) fun a3x es6 h6 => ?_
  refine records_bind (records_reduceToVariable_names _) fun a3y es7 h7 => ?_
  refine records_bind (records_reduceToVariable_names _) fun a4x es8 h8 => ?_
  refine records_bind (records_reduceToVariable_names _) fun a4y es9 h9 => ?_
  refine records_bind (records_reduceToVariable_names _) fun a5x es10 h10 => ?_
  refine records_bind (records_reduceToVariable_names _) fun a5y es11 h11 => ?_
  refine records_bind (records_reduceToVariable_names _) fun b0 es12 h12 => ?_
  refine records_bind (records_reduceToVariable_names _) fun b1 es13 h13 => ?_
  refine records_bind (records_reduceToVariable_names _) fun b2 es14 h14 => ?_
  refine records_bind (records_reduceToVariable_names _) fun b3 es15 h15 => ?_
  refine records_bind (records_reduceToVariable_names _) fun b4 es16 h16 => ?_
  refine records_bind (records_reduceToVariable_names _) fun s0 es17 h17 => ?_
  refine records_bind (records_reduceToVariable_names _) fun s1 es18 h18 => ?_
  refine records_bind (records_reduceToVariable_names _) fun s2 es19 h19 => ?_
  refine records_bind (records_reduceToVariable_names _) fun s3 es20 h20 => ?_
  refine records_bind (records_reduceToVariable_names _) fun s4 es21 h21 => ?_
  refine records_bind (records_reduceToVariable_names _) fun np es22 h22 => ?_
  refine records_bind (records_reduceToVariable_names _) fun nn es23 h23 => ?_
  refine records_bind (records_reduceToVariable_names _) fun bx es24 h24 => ?_
  refine records_bind (records_reduceToVariable_names _) fun by_ es25 h25 => ?_
  refine records_pure _ ?_
  set A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++ (es6 ++ (es7 ++ (es8 ++ (es9 ++
    (es10 ++ (es11 ++ (es12 ++ (es13 ++ (es14 ++ (es15 ++ (es16 ++ (es17 ++ (es18 ++ (es19 ++
    (es20 ++ (es21 ++ (es22 ++ (es23 ++ (es24 ++ (es25 ++ [])))))))))))))))))))))))))) with hA
  have h0' := operandNames_of h0 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h1' := operandNames_of h1 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h2' := operandNames_of h2 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h3' := operandNames_of h3 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h4' := operandNames_of h4 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h5' := operandNames_of h5 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h6' := operandNames_of h6 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h7' := operandNames_of h7 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h8' := operandNames_of h8 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h9' := operandNames_of h9 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h10' := operandNames_of h10 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h11' := operandNames_of h11 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h12' := operandNames_of h12 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h13' := operandNames_of h13 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h14' := operandNames_of h14 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h15' := operandNames_of h15 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h16' := operandNames_of h16 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h17' := operandNames_of h17 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h18' := operandNames_of h18 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h19' := operandNames_of h19 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h20' := operandNames_of h20 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h21' := operandNames_of h21 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h22' := operandNames_of h22 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h23' := operandNames_of h23 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h24' := operandNames_of h24 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h25' := operandNames_of h25 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have hcA : r.cellsA = [some r.base.x, some r.base.y, some r.acc0.x, some r.acc0.y, some r.nPrev,
      some r.nNext, none, some r.acc1.x, some r.acc1.y, some r.acc2.x, some r.acc2.y,
      some r.acc3.x, some r.acc3.y, some r.acc4.x, some r.acc4.y] := rfl
  have hcB : r.cellsB = [some r.acc5.x, some r.acc5.y, some r.bit0, some r.bit1, some r.bit2,
      some r.bit3, some r.bit4, some r.slope0, some r.slope1, some r.slope2, some r.slope3,
      some r.slope4] := rfl
  refine ⟨fun e he w hw => ?_, fun j => ?_, fun j => ?_⟩
  · simp only [List.append_nil, List.mem_append] at he
    rw [hcA, hcB]
    rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he |
      he | he | he | he | he | he | he | he | he | he
    · exact (h0'.1 e he w hw).imp_right fun h => ⟨r.acc0.x, Or.inl (by simp), h⟩
    · exact (h1'.1 e he w hw).imp_right fun h => ⟨r.acc0.y, Or.inl (by simp), h⟩
    · exact (h2'.1 e he w hw).imp_right fun h => ⟨r.acc1.x, Or.inl (by simp), h⟩
    · exact (h3'.1 e he w hw).imp_right fun h => ⟨r.acc1.y, Or.inl (by simp), h⟩
    · exact (h4'.1 e he w hw).imp_right fun h => ⟨r.acc2.x, Or.inl (by simp), h⟩
    · exact (h5'.1 e he w hw).imp_right fun h => ⟨r.acc2.y, Or.inl (by simp), h⟩
    · exact (h6'.1 e he w hw).imp_right fun h => ⟨r.acc3.x, Or.inl (by simp), h⟩
    · exact (h7'.1 e he w hw).imp_right fun h => ⟨r.acc3.y, Or.inl (by simp), h⟩
    · exact (h8'.1 e he w hw).imp_right fun h => ⟨r.acc4.x, Or.inl (by simp), h⟩
    · exact (h9'.1 e he w hw).imp_right fun h => ⟨r.acc4.y, Or.inl (by simp), h⟩
    · exact (h10'.1 e he w hw).imp_right fun h => ⟨r.acc5.x, Or.inr (by simp), h⟩
    · exact (h11'.1 e he w hw).imp_right fun h => ⟨r.acc5.y, Or.inr (by simp), h⟩
    · exact (h12'.1 e he w hw).imp_right fun h => ⟨r.bit0, Or.inr (by simp), h⟩
    · exact (h13'.1 e he w hw).imp_right fun h => ⟨r.bit1, Or.inr (by simp), h⟩
    · exact (h14'.1 e he w hw).imp_right fun h => ⟨r.bit2, Or.inr (by simp), h⟩
    · exact (h15'.1 e he w hw).imp_right fun h => ⟨r.bit3, Or.inr (by simp), h⟩
    · exact (h16'.1 e he w hw).imp_right fun h => ⟨r.bit4, Or.inr (by simp), h⟩
    · exact (h17'.1 e he w hw).imp_right fun h => ⟨r.slope0, Or.inr (by simp), h⟩
    · exact (h18'.1 e he w hw).imp_right fun h => ⟨r.slope1, Or.inr (by simp), h⟩
    · exact (h19'.1 e he w hw).imp_right fun h => ⟨r.slope2, Or.inr (by simp), h⟩
    · exact (h20'.1 e he w hw).imp_right fun h => ⟨r.slope3, Or.inr (by simp), h⟩
    · exact (h21'.1 e he w hw).imp_right fun h => ⟨r.slope4, Or.inr (by simp), h⟩
    · exact (h22'.1 e he w hw).imp_right fun h => ⟨r.nPrev, Or.inl (by simp), h⟩
    · exact (h23'.1 e he w hw).imp_right fun h => ⟨r.nNext, Or.inl (by simp), h⟩
    · exact (h24'.1 e he w hw).imp_right fun h => ⟨r.base.x, Or.inl (by simp), h⟩
    · exact (h25'.1 e he w hw).imp_right fun h => ⟨r.base.y, Or.inl (by simp), h⟩
  · rw [hcA]
    fin_cases j
    exacts [⟨h24'.2.1, h24'.2.2⟩, ⟨h25'.2.1, h25'.2.2⟩, ⟨h0'.2.1, h0'.2.2⟩, ⟨h1'.2.1, h1'.2.2⟩,
      ⟨h22'.2.1, h22'.2.2⟩, ⟨h23'.2.1, h23'.2.2⟩, trivial, ⟨h2'.2.1, h2'.2.2⟩,
      ⟨h3'.2.1, h3'.2.2⟩, ⟨h4'.2.1, h4'.2.2⟩, ⟨h5'.2.1, h5'.2.2⟩, ⟨h6'.2.1, h6'.2.2⟩,
      ⟨h7'.2.1, h7'.2.2⟩, ⟨h8'.2.1, h8'.2.2⟩, ⟨h9'.2.1, h9'.2.2⟩]
  · rw [hcB]
    fin_cases j
    exacts [⟨h10'.2.1, h10'.2.2⟩, ⟨h11'.2.1, h11'.2.2⟩, ⟨h12'.2.1, h12'.2.2⟩,
      ⟨h13'.2.1, h13'.2.2⟩, ⟨h14'.2.1, h14'.2.2⟩, ⟨h15'.2.1, h15'.2.2⟩, ⟨h16'.2.1, h16'.2.2⟩,
      ⟨h17'.2.1, h17'.2.2⟩, ⟨h18'.2.1, h18'.2.2⟩, ⟨h19'.2.1, h19'.2.2⟩, ⟨h20'.2.1, h20'.2.2⟩,
      ⟨h21'.2.1, h21'.2.2⟩, trivial, trivial, trivial]

/-- The walk of a multiplication: round by round, each row pair against its round's two
rows. -/
private theorem records_varBaseMul_names :
    (rounds : VarBaseMul F) →
      Records (VarBaseMul.reduce rounds : RecordingBuilder F (List (KimchiRow F × KimchiRow F)))
        fun pairs es =>
          (∀ e ∈ es, ∀ w ∈ e.names, w ∈ allocs es ∨ ∃ r ∈ rounds, ∃ x,
            (some x ∈ r.cellsA ∨ some x ∈ r.cellsB) ∧ w ∈ x.termVars ∧ x ≠ .var w) ∧
          ∀ (i : Nat) (hi : i < rounds.length) (hi' : i < pairs.length) (j : Fin wCols),
            CellOf (allocs es) pairs[i].1.vars[j] (cellsOf rounds[i].cellsA)[j] ∧
              CellOf (allocs es) pairs[i].2.vars[j] (cellsOf rounds[i].cellsB)[j]
  | [] => records_pure _ ⟨fun _ h => (List.not_mem_nil h).elim,
      fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | r :: rs => by
    unfold VarBaseMul.reduce
    refine records_bind (records_scaleRound_names r) fun pair es1 h1 => ?_
    refine records_bind (records_varBaseMul_names rs) fun rest es2 h2 => ?_
    refine records_pure _ ⟨fun e he w hw => ?_, fun i hi hi' j => ?_⟩
    · simp only [List.append_nil, List.mem_append] at he
      rcases he with he | he
      · exact (h1.1 e he w hw).imp allocs_mono_left fun ⟨x, hx, h⟩ =>
          ⟨r, List.mem_cons_self .., x, hx, h⟩
      · exact (h2.1 e he w hw).imp (fun h => allocs_mono_right (allocs_mono_left h))
          fun ⟨r', hr', x, hx, h⟩ => ⟨r', List.mem_cons_of_mem _ hr', x, hx, h⟩
    · cases i with
      | zero =>
        exact ⟨cellOf_mono (fun u hu => allocs_mono_left hu) (h1.2.1 j),
          cellOf_mono (fun u hu => allocs_mono_left hu) (h1.2.2 j)⟩
      | succ k =>
        obtain ⟨c1, c2⟩ := h2.2 k (by simpa using hi) (by simpa using hi') j
        exact ⟨cellOf_mono (fun u hu => allocs_mono_right (allocs_mono_left hu)) c1,
          cellOf_mono (fun u hu => allocs_mono_right (allocs_mono_left hu)) c2⟩

/-- Each emitted scale row pair's cells are its round's two rows' operands' variables cell by
cell. -/
private theorem varBaseMul_cells (nv : Variable) (aux : AuxState F) (rounds : VarBaseMul F)
    (i : Fin rounds.length) (j : Fin wCols) :
    CellOf (allocs (recordReduction nv aux (VarBaseMul.reduce rounds)).events)
        ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[i.val]'(by
          rw [varBaseMul_result_length]; exact i.isLt)).1.vars[j]
        (cellsOf rounds[i].cellsA)[j] ∧
      CellOf (allocs (recordReduction nv aux (VarBaseMul.reduce rounds)).events)
        ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[i.val]'(by
          rw [varBaseMul_result_length]; exact i.isLt)).2.vars[j]
        (cellsOf rounds[i].cellsB)[j] :=
  (recordReduction_of_records (records_varBaseMul_names rounds) nv aux).2 i.val i.isLt _ j

/-- Each emitted scale round's first row carries a variable in every cell but the seventh. -/
theorem varBaseMul_cell_some_fst (nv : Variable) (aux : AuxState F) (rounds : VarBaseMul F)
    (i : Fin rounds.length) (k : Fin wCols) (hk : k.val ≠ 6) :
    ∃ w, ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[i.val]'(by
      rw [varBaseMul_result_length]; exact i.isLt)).1.vars[k] = some w := by
  have h := (varBaseMul_cells nv aux rounds i k).1
  have hsome : ∃ x, (cellsOf rounds[i].cellsA)[k] = some x := by
    fin_cases k
    all_goals first | exact ⟨_, rfl⟩ | exact absurd rfl hk
  obtain ⟨x, hx⟩ := hsome
  rw [hx] at h
  cases hlab : ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[i.val]'(by
      rw [varBaseMul_result_length]; exact i.isLt)).1.vars[k] with
  | none =>
    rw [hlab] at h
    exact h.elim
  | some w => exact ⟨w, rfl⟩

/-- Each emitted scale round's second row carries a variable in each of its twelve operand
cells. -/
theorem varBaseMul_cell_some_snd (nv : Variable) (aux : AuxState F) (rounds : VarBaseMul F)
    (i : Fin rounds.length) (k : Fin wCols) (hk : k.val < 12) :
    ∃ w, ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[i.val]'(by
      rw [varBaseMul_result_length]; exact i.isLt)).2.vars[k] = some w := by
  have h := (varBaseMul_cells nv aux rounds i k).2
  have hsome : ∃ x, (cellsOf rounds[i].cellsB)[k] = some x := by
    fin_cases k
    all_goals first | exact ⟨_, rfl⟩ | exact absurd hk (by decide)
  obtain ⟨x, hx⟩ := hsome
  rw [hx] at h
  cases hlab : ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[i.val]'(by
      rw [varBaseMul_result_length]; exact i.isLt)).2.vars[k] with
  | none =>
    rw [hlab] at h
    exact h.elim
  | some w => exact ⟨w, rfl⟩

/-- A multiplication's recorded reduction is placed: its names are allocations or terms of
its rounds' operands that are not that bare variable, and its rows' cells are the rounds'
operands' variables cell by cell. -/
theorem varBaseMul_placed (nv : Variable) (aux : AuxState F) (rounds : VarBaseMul F) :
    Placed nv aux (.varBaseMul rounds) := by
  obtain ⟨hn, hc⟩ := recordReduction_of_records (records_varBaseMul_names rounds) nv aux
  refine ⟨fun e he w hw => (hn e he w hw).imp_right ?_, ?_, fun i j => ?_⟩
  · rintro ⟨r, hr, x, hx, h⟩
    refine ⟨x, ?_, h⟩
    rcases hx with hx | hx
    · exact mem_placedOperands (List.mem_flatMap.mpr ⟨r, hr, by simp⟩)
        (mem_cellsOf (by simp [ScaleRound.cellsA]) hx)
    · exact mem_placedOperands (List.mem_flatMap.mpr ⟨r, hr, by simp⟩)
        (mem_cellsOf (by simp [ScaleRound.cellsB]) hx)
  · show ((recordReduction nv aux (VarBaseMul.reduce rounds)).result.flatMap
      fun p => [p.1, p.2]).length =
        (rounds.flatMap fun r => [cellsOf r.cellsA, cellsOf r.cellsB]).length
    rw [varBaseMul_rows_length, length_flatMap_pair]
  · have hi : i.val < 2 * rounds.length := by
      have h := i.isLt
      simp only [KimchiConstraint.rowCount, KimchiConstraint.rowOperandsList,
        length_flatMap_pair] at h
      exact h
    rcases Nat.even_or_odd' i.val with ⟨k, hk | hk⟩
    · have hk' : k < rounds.length := by omega
      have hrow : (KimchiConstraint.varBaseMul rounds).rowOperands[i] =
          cellsOf rounds[k].cellsA := by
        show (rounds.flatMap fun r => [cellsOf r.cellsA, cellsOf r.cellsB])[i.val] = _
        rw [getElem_congr_idx hk]
        exact getElem_flatMap_pair_fst _ _ rounds k hk'
      rw [hrow]
      have e : ((recordReduction nv aux (VarBaseMul.reduce rounds)).result.flatMap
          fun p => [p.1, p.2])[i.val]'(by rw [varBaseMul_rows_length]; omega) =
          ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[k]'(by
            rw [varBaseMul_result_length]; exact hk')).1 := by
        rw [getElem_congr_idx hk]
        exact varBaseMul_rows_fst nv aux rounds ⟨k, hk'⟩
      show CellOf _ (((recordReduction nv aux (VarBaseMul.reduce rounds)).result.flatMap
        fun p : KimchiRow F × KimchiRow F => [p.1, p.2])[i.val]'(by
          rw [varBaseMul_rows_length]; omega)).vars[j] _
      rw [e]
      exact (hc k hk' _ j).1
    · have hk' : k < rounds.length := by omega
      have hrow : (KimchiConstraint.varBaseMul rounds).rowOperands[i] =
          cellsOf rounds[k].cellsB := by
        show (rounds.flatMap fun r => [cellsOf r.cellsA, cellsOf r.cellsB])[i.val] = _
        rw [getElem_congr_idx hk]
        exact getElem_flatMap_pair_snd _ _ rounds k hk'
      rw [hrow]
      have e : ((recordReduction nv aux (VarBaseMul.reduce rounds)).result.flatMap
          fun p => [p.1, p.2])[i.val]'(by rw [varBaseMul_rows_length]; omega) =
          ((recordReduction nv aux (VarBaseMul.reduce rounds)).result[k]'(by
            rw [varBaseMul_result_length]; exact hk')).2 := by
        rw [getElem_congr_idx hk]
        exact varBaseMul_rows_snd nv aux rounds ⟨k, hk'⟩
      show CellOf _ (((recordReduction nv aux (VarBaseMul.reduce rounds)).result.flatMap
        fun p : KimchiRow F × KimchiRow F => [p.1, p.2])[i.val]'(by
          rw [varBaseMul_rows_length]; omega)).vars[j] _
      rw [e]
      exact (hc k hk' _ j).2

/-- The walk of one endomorphism round: every name is an allocation or a term of an operand
that is not that bare variable, and the row's cells are its operands' variables cell by
cell. -/
private theorem records_endoMulRound_names (r : EndoMulRound F) :
    Records (r.reduce : RecordingBuilder F (KimchiRow F)) fun row es =>
      (∀ e ∈ es, ∀ w ∈ e.names, w ∈ allocs es ∨
        ∃ x, some x ∈ r.cells ∧ w ∈ x.termVars ∧ x ≠ .var w) ∧
      ∀ j : Fin wCols, CellOf (allocs es) row.vars[j] (cellsOf r.cells)[j] := by
  unfold EndoMulRound.reduce
  refine records_bind (records_reduceToVariable_names _) fun tx es0 h0 => ?_
  refine records_bind (records_reduceToVariable_names _) fun ty es1 h1 => ?_
  refine records_bind (records_reduceToVariable_names _) fun px es2 h2 => ?_
  refine records_bind (records_reduceToVariable_names _) fun py es3 h3 => ?_
  refine records_bind (records_reduceToVariable_names _) fun na es4 h4 => ?_
  refine records_bind (records_reduceToVariable_names _) fun rx es5 h5 => ?_
  refine records_bind (records_reduceToVariable_names _) fun ry es6 h6 => ?_
  refine records_bind (records_reduceToVariable_names _) fun s1 es7 h7 => ?_
  refine records_bind (records_reduceToVariable_names _) fun s3 es8 h8 => ?_
  refine records_bind (records_reduceToVariable_names _) fun b1 es9 h9 => ?_
  refine records_bind (records_reduceToVariable_names _) fun b2 es10 h10 => ?_
  refine records_bind (records_reduceToVariable_names _) fun b3 es11 h11 => ?_
  refine records_bind (records_reduceToVariable_names _) fun b4 es12 h12 => ?_
  refine records_bind (records_reduceToVariable_names _) fun inv es13 h13 => ?_
  refine records_pure _ ?_
  set A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++ (es6 ++ (es7 ++ (es8 ++ (es9 ++
    (es10 ++ (es11 ++ (es12 ++ (es13 ++ [])))))))))))))) with hA
  have h0' := operandNames_of h0 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h1' := operandNames_of h1 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h2' := operandNames_of h2 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h3' := operandNames_of h3 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h4' := operandNames_of h4 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h5' := operandNames_of h5 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h6' := operandNames_of h6 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h7' := operandNames_of h7 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h8' := operandNames_of h8 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h9' := operandNames_of h9 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h10' := operandNames_of h10 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h11' := operandNames_of h11 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h12' := operandNames_of h12 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h13' := operandNames_of h13 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have hc : r.cells = [some r.t.x, some r.t.y, some r.inv, none, some r.p.x, some r.p.y,
      some r.nAcc, some r.r.x, some r.r.y, some r.s1, some r.s3, some r.bit0, some r.bit1,
      some r.bit2, some r.bit3] := rfl
  refine ⟨fun e he w hw => ?_, fun j => ?_⟩
  · simp only [List.append_nil, List.mem_append] at he
    rw [hc]
    rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he
    · exact (h0'.1 e he w hw).imp_right fun h => ⟨r.t.x, by simp, h⟩
    · exact (h1'.1 e he w hw).imp_right fun h => ⟨r.t.y, by simp, h⟩
    · exact (h2'.1 e he w hw).imp_right fun h => ⟨r.p.x, by simp, h⟩
    · exact (h3'.1 e he w hw).imp_right fun h => ⟨r.p.y, by simp, h⟩
    · exact (h4'.1 e he w hw).imp_right fun h => ⟨r.nAcc, by simp, h⟩
    · exact (h5'.1 e he w hw).imp_right fun h => ⟨r.r.x, by simp, h⟩
    · exact (h6'.1 e he w hw).imp_right fun h => ⟨r.r.y, by simp, h⟩
    · exact (h7'.1 e he w hw).imp_right fun h => ⟨r.s1, by simp, h⟩
    · exact (h8'.1 e he w hw).imp_right fun h => ⟨r.s3, by simp, h⟩
    · exact (h9'.1 e he w hw).imp_right fun h => ⟨r.bit0, by simp, h⟩
    · exact (h10'.1 e he w hw).imp_right fun h => ⟨r.bit1, by simp, h⟩
    · exact (h11'.1 e he w hw).imp_right fun h => ⟨r.bit2, by simp, h⟩
    · exact (h12'.1 e he w hw).imp_right fun h => ⟨r.bit3, by simp, h⟩
    · exact (h13'.1 e he w hw).imp_right fun h => ⟨r.inv, by simp, h⟩
  · rw [hc]
    fin_cases j
    exacts [⟨h0'.2.1, h0'.2.2⟩, ⟨h1'.2.1, h1'.2.2⟩, ⟨h13'.2.1, h13'.2.2⟩, trivial,
      ⟨h2'.2.1, h2'.2.2⟩, ⟨h3'.2.1, h3'.2.2⟩, ⟨h4'.2.1, h4'.2.2⟩, ⟨h5'.2.1, h5'.2.2⟩,
      ⟨h6'.2.1, h6'.2.2⟩, ⟨h7'.2.1, h7'.2.2⟩, ⟨h8'.2.1, h8'.2.2⟩, ⟨h9'.2.1, h9'.2.2⟩,
      ⟨h10'.2.1, h10'.2.2⟩, ⟨h11'.2.1, h11'.2.2⟩, ⟨h12'.2.1, h12'.2.2⟩]

/-- The walk of the rounds: round by round, each row against its round's cells. -/
private theorem records_endoMulRounds_names :
    (state : List (EndoMulRound F)) →
      Records (EndoMul.reduceRounds state : RecordingBuilder F (List (KimchiRow F)))
        fun rows es =>
          (∀ e ∈ es, ∀ w ∈ e.names, w ∈ allocs es ∨
            ∃ r ∈ state, ∃ x, some x ∈ r.cells ∧ w ∈ x.termVars ∧ x ≠ .var w) ∧
          rows.length = state.length ∧
          ∀ (i : Nat) (hi : i < state.length) (hi' : i < rows.length) (j : Fin wCols),
            CellOf (allocs es) rows[i].vars[j] (cellsOf state[i].cells)[j]
  | [] => records_pure _ ⟨fun _ h => (List.not_mem_nil h).elim, rfl,
      fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | r :: rs => by
    unfold EndoMul.reduceRounds
    refine records_bind (records_endoMulRound_names r) fun row es1 h1 => ?_
    refine records_bind (records_endoMulRounds_names rs) fun rest es2 h2 => ?_
    refine records_pure _ ⟨fun e he w hw => ?_, by simp [h2.2.1], fun i hi hi' j => ?_⟩
    · simp only [List.append_nil, List.mem_append] at he
      rcases he with he | he
      · exact (h1.1 e he w hw).imp allocs_mono_left fun ⟨x, hx, h⟩ =>
          ⟨r, List.mem_cons_self .., x, hx, h⟩
      · exact (h2.1 e he w hw).imp (fun h => allocs_mono_right (allocs_mono_left h))
          fun ⟨r', hr', x, hx, h⟩ => ⟨r', List.mem_cons_of_mem _ hr', x, hx, h⟩
    · cases i with
      | zero => exact cellOf_mono (fun u hu => allocs_mono_left hu) (h1.2 j)
      | succ k =>
        exact cellOf_mono (fun u hu => allocs_mono_right (allocs_mono_left hu))
          (h2.2.2 k (by simpa using hi) (by simpa using hi') j)

/-- The walk of a multiplication: the finals' operands, the rounds, and the terminal row
against the finals' cells. -/
private theorem records_endoMul_names (c : EndoMul F) :
    Records (EndoMul.reduce c : RecordingBuilder F (List (KimchiRow F))) fun rows es =>
      (∀ e ∈ es, ∀ w ∈ e.names, w ∈ allocs es ∨ ∃ x,
        (some x ∈ c.finalCells ∨ ∃ r ∈ c.state, some x ∈ r.cells) ∧
          w ∈ x.termVars ∧ x ≠ .var w) ∧
      (∀ (i : Nat) (hi : i < rows.length) (hi' : i < c.state.length) (j : Fin wCols),
        CellOf (allocs es) rows[i].vars[j] (cellsOf c.state[i].cells)[j]) ∧
      ∀ (hi : c.state.length < rows.length) (j : Fin wCols),
        CellOf (allocs es) rows[c.state.length].vars[j] (cellsOf c.finalCells)[j] := by
  unfold EndoMul.reduce
  refine records_bind (records_reduceToVariable_names _) fun xs es0 h0 => ?_
  refine records_bind (records_reduceToVariable_names _) fun ys es1 h1 => ?_
  refine records_bind (records_reduceToVariable_names _) fun na es2 h2 => ?_
  refine records_bind (records_endoMulRounds_names c.state) fun rows es3 h3 => ?_
  refine records_pure _ ?_
  set A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ [])))) with hA
  have h0' := operandNames_of h0 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h1' := operandNames_of h1 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h2' := operandNames_of h2 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have hcf : c.finalCells = [none, none, none, none, some c.s.x, some c.s.y, some c.nAcc] := rfl
  refine ⟨fun e he w hw => ?_, fun i hi hi' j => ?_, fun hi j => ?_⟩
  · simp only [List.append_nil, List.mem_append] at he
    rcases he with he | he | he | he
    · exact (h0'.1 e he w hw).imp_right fun h => ⟨c.s.x, Or.inl (by rw [hcf]; simp), h⟩
    · exact (h1'.1 e he w hw).imp_right fun h => ⟨c.s.y, Or.inl (by rw [hcf]; simp), h⟩
    · exact (h2'.1 e he w hw).imp_right fun h => ⟨c.nAcc, Or.inl (by rw [hcf]; simp), h⟩
    · exact (h3.1 e he w hw).imp (fun h => by rw [hA]; simp [allocs_append, h])
        fun ⟨r, hr, x, hx, h⟩ => ⟨x, Or.inr ⟨r, hr, hx⟩, h⟩
  · rw [List.getElem_append_left (by rw [h3.2.1]; exact hi')]
    exact cellOf_mono (fun u hu => by rw [hA]; simp [allocs_append, hu])
      (h3.2.2 i hi' (by rw [h3.2.1]; exact hi') j)
  · have hlen : rows.length = c.state.length := h3.2.1
    rw [List.getElem_concat_length hlen.symm, hcf]
    fin_cases j
    exacts [trivial, trivial, trivial, trivial, ⟨h0'.2.1, h0'.2.2⟩, ⟨h1'.2.1, h1'.2.2⟩,
      ⟨h2'.2.1, h2'.2.2⟩, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial]

/-- Each emitted round row's cells are its round's operands' variables cell by cell. -/
private theorem endoMul_cells (nv : Variable) (aux : AuxState F) (c : EndoMul F)
    (k : Fin c.state.length) (j : Fin wCols) :
    CellOf (allocs (recordReduction nv aux (EndoMul.reduce c)).events)
      ((recordReduction nv aux (EndoMul.reduce c)).result[k.val]'(by
        rw [endoMul_result_length]; omega)).vars[j]
      (cellsOf c.state[k].cells)[j] :=
  (recordReduction_of_records (records_endoMul_names c) nv aux).2.1 k.val _ k.isLt j

/-- The emitted terminal row's cells are the finals' variables cell by cell. -/
private theorem endoMul_final_cells (nv : Variable) (aux : AuxState F) (c : EndoMul F)
    (j : Fin wCols) :
    CellOf (allocs (recordReduction nv aux (EndoMul.reduce c)).events)
      ((recordReduction nv aux (EndoMul.reduce c)).result[c.state.length]'(by
        rw [endoMul_result_length]; omega)).vars[j]
      (cellsOf c.finalCells)[j] :=
  (recordReduction_of_records (records_endoMul_names c) nv aux).2.2 _ j

/-- Each emitted round row carries a variable in every cell but the fourth. -/
theorem endoMul_cell_some_round (nv : Variable) (aux : AuxState F) (c : EndoMul F)
    (k : Fin c.state.length) (j : Fin wCols) (hj : j.val ≠ 3) :
    ∃ w, ((recordReduction nv aux (EndoMul.reduce c)).result[k.val]'(by
      rw [endoMul_result_length]; omega)).vars[j] = some w := by
  have h := endoMul_cells nv aux c k j
  have hsome : ∃ x, (cellsOf c.state[k].cells)[j] = some x := by
    fin_cases j
    all_goals first | exact ⟨_, rfl⟩ | exact absurd rfl hj
  obtain ⟨x, hx⟩ := hsome
  rw [hx] at h
  cases hlab : ((recordReduction nv aux (EndoMul.reduce c)).result[k.val]'(by
      rw [endoMul_result_length]; omega)).vars[j] with
  | none =>
    rw [hlab] at h
    exact h.elim
  | some w => exact ⟨w, rfl⟩

/-- The row after each round's, the next round's or the terminal row, carries a variable in
its three output cells. -/
theorem endoMul_cell_some_next (nv : Variable) (aux : AuxState F) (c : EndoMul F)
    (k : Fin c.state.length) (j : Fin wCols) (hj : 4 ≤ j.val ∧ j.val ≤ 6) :
    ∃ w, ((recordReduction nv aux (EndoMul.reduce c)).result[k.val + 1]'(by
      rw [endoMul_result_length]; omega)).vars[j] = some w := by
  rcases Nat.lt_or_ge (k.val + 1) c.state.length with hlt | hge
  · have h := endoMul_cells nv aux c ⟨k.val + 1, hlt⟩ j
    have hsome : ∃ x, (cellsOf c.state[(⟨k.val + 1, hlt⟩ : Fin c.state.length)].cells)[j] =
        some x := by
      fin_cases j
      all_goals first | exact ⟨_, rfl⟩ | exact absurd hj (by decide)
    obtain ⟨x, hx⟩ := hsome
    rw [hx] at h
    cases hlab : ((recordReduction nv aux (EndoMul.reduce c)).result[k.val + 1]'(by
        rw [endoMul_result_length]; omega)).vars[j] with
    | none =>
      rw [hlab] at h
      exact h.elim
    | some w => exact ⟨w, rfl⟩
  · have heq : k.val + 1 = c.state.length := by
      have := k.isLt
      omega
    have h := endoMul_final_cells nv aux c j
    have hsome : ∃ x, (cellsOf c.finalCells)[j] = some x := by
      fin_cases j
      all_goals first | exact ⟨_, rfl⟩ | exact absurd hj (by decide)
    obtain ⟨x, hx⟩ := hsome
    rw [hx] at h
    rw [getElem_congr_idx heq]
    cases hlab : ((recordReduction nv aux (EndoMul.reduce c)).result[c.state.length]'(by
        rw [endoMul_result_length]; omega)).vars[j] with
    | none =>
      rw [hlab] at h
      exact h.elim
    | some w => exact ⟨w, rfl⟩

/-- A multiplication's recorded reduction is placed: its names are allocations or terms of
the finals' or its rounds' operands that are not that bare variable, and its rows' cells are
those operands' variables cell by cell. -/
theorem endoMul_placed (nv : Variable) (aux : AuxState F) (c : EndoMul F) :
    Placed nv aux (.endoMul c) := by
  obtain ⟨hn, hc, hfin⟩ := recordReduction_of_records (records_endoMul_names c) nv aux
  refine ⟨fun e he w hw => (hn e he w hw).imp_right ?_, ?_, fun i j => ?_⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, ?_, h⟩
    rcases hx with hx | ⟨r, hr, hx⟩
    · exact mem_placedOperands (List.mem_append_right _ (List.mem_singleton_self _))
        (mem_cellsOf (by simp [EndoMul.finalCells]) hx)
    · exact mem_placedOperands (List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
        (mem_cellsOf (by simp [EndoMulRound.cells]) hx)
  · show (recordReduction nv aux (EndoMul.reduce c)).result.length =
      ((c.state.map fun r => cellsOf r.cells) ++ [cellsOf c.finalCells]).length
    rw [List.length_append, List.length_map, List.length_singleton]
    exact endoMul_result_length nv aux c
  · have hi : i.val < c.state.length + 1 := by
      have h := i.isLt
      simp only [KimchiConstraint.rowCount, KimchiConstraint.rowOperandsList, List.length_append,
        List.length_map, List.length_singleton] at h
      exact h
    rcases Nat.lt_or_ge i.val c.state.length with hlt | hge
    · have hrow : (KimchiConstraint.endoMul c).rowOperands[i] =
          cellsOf (c.state[i.val]'hlt).cells := by
        show ((c.state.map fun r => cellsOf r.cells) ++ [cellsOf c.finalCells])[i.val] = _
        rw [List.getElem_append_left (by simpa using hlt), List.getElem_map]
      rw [hrow]
      exact hc i.val _ hlt j
    · have heq : i.val = c.state.length := by omega
      have hrow : (KimchiConstraint.endoMul c).rowOperands[i] = cellsOf c.finalCells := by
        show ((c.state.map fun r => cellsOf r.cells) ++ [cellsOf c.finalCells])[i.val] = _
        rw [List.getElem_concat_length
          (show i.val = (c.state.map fun r => cellsOf r.cells).length by simpa using heq)]
      rw [hrow]
      have h := hfin (by rw [endoMul_result_length]; omega) j
      show CellOf _ ((recordReduction nv aux (EndoMul.reduce c)).result[i.val]'(by
        rw [endoMul_result_length]; omega)).vars[j] _
      rw [getElem_congr_idx heq]
      exact h

/-- One state's cells within allocations `A`: its three variables against its three
operands. -/
private def TripleCells (A : List Variable) (v : Variable × Variable × Variable)
    (t : FVar F × FVar F × FVar F) : Prop :=
  CellOf A (some v.1) (some t.1) ∧ CellOf A (some v.2.1) (some t.2.1) ∧
    CellOf A (some v.2.2) (some t.2.2)

private theorem tripleCells_mono {A A' : List Variable} (hA : ∀ u ∈ A, u ∈ A')
    {v : Variable × Variable × Variable} {t : FVar F × FVar F × FVar F}
    (h : TripleCells A v t) : TripleCells A' v t :=
  ⟨cellOf_mono hA h.1, cellOf_mono hA h.2.1, cellOf_mono hA h.2.2⟩

/-- The walk of one state: every name is an allocation or a term of one of its operands that
is not that bare variable, and its variables are its operands' cell by cell. -/
private theorem records_reduceState_names (t : FVar F × FVar F × FVar F) :
    Records (reduceState t : RecordingBuilder F (Variable × Variable × Variable)) fun v es =>
      (∀ e ∈ es, ∀ w ∈ e.names, w ∈ allocs es ∨
        ∃ x, (x = t.1 ∨ x = t.2.1 ∨ x = t.2.2) ∧ w ∈ x.termVars ∧ x ≠ .var w) ∧
      TripleCells (allocs es) v t := by
  unfold reduceState
  refine records_bind (records_reduceToVariable_names _) fun a es0 h0 => ?_
  refine records_bind (records_reduceToVariable_names _) fun b es1 h1 => ?_
  refine records_bind (records_reduceToVariable_names _) fun c es2 h2 => ?_
  refine records_pure _ ?_
  set A := allocs (es0 ++ (es1 ++ (es2 ++ []))) with hA
  have h0' := operandNames_of h0 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h1' := operandNames_of h1 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h2' := operandNames_of h2 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  refine ⟨fun e he w hw => ?_, ⟨h0'.2.1, h0'.2.2⟩, ⟨h1'.2.1, h1'.2.2⟩, ⟨h2'.2.1, h2'.2.2⟩⟩
  simp only [List.append_nil, List.mem_append] at he
  rcases he with he | he | he
  · exact (h0'.1 e he w hw).imp_right fun h => ⟨t.1, Or.inl rfl, h⟩
  · exact (h1'.1 e he w hw).imp_right fun h => ⟨t.2.1, Or.inr (Or.inl rfl), h⟩
  · exact (h2'.1 e he w hw).imp_right fun h => ⟨t.2.2, Or.inr (Or.inr rfl), h⟩

/-- The walk of the states: index by index. -/
private theorem records_reduceStates_names :
    (ts : List (FVar F × FVar F × FVar F)) →
      Records (reduceStates ts : RecordingBuilder F (List (Variable × Variable × Variable)))
        fun vs es =>
          (∀ e ∈ es, ∀ w ∈ e.names, w ∈ allocs es ∨ ∃ t ∈ ts, ∃ x,
            (x = t.1 ∨ x = t.2.1 ∨ x = t.2.2) ∧ w ∈ x.termVars ∧ x ≠ .var w) ∧
          vs.length = ts.length ∧
          ∀ (i : Nat) (hi : i < ts.length) (hi' : i < vs.length),
            TripleCells (allocs es) vs[i] ts[i]
  | [] => records_pure _ ⟨fun _ h => (List.not_mem_nil h).elim, rfl,
      fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | t :: ts => by
    unfold reduceStates
    refine records_bind (records_reduceState_names t) fun v es1 h1 => ?_
    refine records_bind (records_reduceStates_names ts) fun vs es2 h2 => ?_
    refine records_pure _ ⟨fun e he w hw => ?_, by simp [h2.2.1], fun i hi hi' => ?_⟩
    · simp only [List.append_nil, List.mem_append] at he
      rcases he with he | he
      · exact (h1.1 e he w hw).imp allocs_mono_left fun ⟨x, hx, h⟩ =>
          ⟨t, List.mem_cons_self .., x, hx, h⟩
      · exact (h2.1 e he w hw).imp (fun h => allocs_mono_right (allocs_mono_left h))
          fun ⟨t', ht', x, hx, h⟩ => ⟨t', List.mem_cons_of_mem _ ht', x, hx, h⟩
    · cases i with
      | zero => exact tripleCells_mono (fun u hu => allocs_mono_left hu) h1.2
      | succ k =>
        exact tripleCells_mono (fun u hu => allocs_mono_right (allocs_mono_left hu))
          (h2.2.2 k (by simpa using hi) (by simpa using hi'))

/-- The walk of a Poseidon block: its rows are the chunking of its pinned states, every name
an allocation or a term of a state's operand that is not that bare variable, and the pinned
states the states' operands cell by cell. -/
private theorem records_poseidon_names (c : PoseidonConstraint F) :
    Records (c.reduce : RecordingBuilder F (List (KimchiRow F))) fun rows es =>
      ∃ vs : List (Variable × Variable × Variable), vs.length = c.state.length ∧
        rows = rowsFromStates (fun i => c.rc.getD i (0, 0, 0)) 0 vs ∧
        (∀ e ∈ es, ∀ w ∈ e.names, w ∈ allocs es ∨ ∃ t ∈ c.state, ∃ x,
          (x = t.1 ∨ x = t.2.1 ∨ x = t.2.2) ∧ w ∈ x.termVars ∧ x ≠ .var w) ∧
        ∀ (i : Nat) (hi : i < c.state.length) (hi' : i < vs.length),
          TripleCells (allocs es) vs[i] c.state[i] := by
  unfold PoseidonConstraint.reduce
  refine records_bind (records_reduceStates_names c.state) fun vs es h => ?_
  refine records_pure _ ⟨vs, h.2.1, rfl, fun e he w hw => ?_, fun i hi hi' => ?_⟩
  · rw [List.append_nil] at he ⊢
    exact h.1 e he w hw
  · rw [List.append_nil]
    exact h.2.2 i hi hi'

/-- A Poseidon block of the shape `5w + 1` is placed: its names are allocations or terms of
its states' operands that are not that bare variable, and its rows' cells are the states'
operands' variables cell by cell. -/
theorem poseidon_placed (nv : Variable) (aux : AuxState F) (c : PoseidonConstraint F)
    (h : c.state.length % 5 = 1) : Placed nv aux (.poseidon c) := by
  obtain ⟨vs, hvs, hrows, hn, hc⟩ := recordReduction_of_records (records_poseidon_names c) nv aux
  have hw : c.state.length = 5 * (c.state.length / 5) + 1 := by omega
  refine ⟨fun e he w hw' => (hn e he w hw').imp_right ?_, ?_, fun i j => ?_⟩
  · rintro ⟨t, ht, x, hx, hterm⟩
    obtain ⟨row, hrow, h1, h2, h3⟩ := mem_rowOperandsList _ c.state hw t ht
    refine ⟨x, mem_placedOperands hrow ?_, hterm⟩
    rcases hx with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  · show (recordReduction nv aux c.reduce).result.length =
      (Poseidon.rowOperandsList c.state).length
    rw [hrows, rowsFromStates_length _ 0 (c.state.length / 5) vs (by omega),
      rowOperandsList_length (c.state.length / 5) c.state hw]
  · have hi : i.val < c.state.length / 5 + 1 := by
      have h' := i.isLt
      simp only [KimchiConstraint.rowCount, KimchiConstraint.rowOperandsList] at h'
      exact Nat.lt_of_lt_of_eq h' (rowOperandsList_length (c.state.length / 5) c.state hw)
    rcases Nat.lt_or_ge i.val (c.state.length / 5) with hlt | hge
    · have hrow : (KimchiConstraint.poseidon c).rowOperands[i] =
          cellsOf (PoseidonConstraint.windowCells (c.state[5 * i.val]'(by omega))
            (c.state[5 * i.val + 1]'(by omega)) (c.state[5 * i.val + 2]'(by omega))
            (c.state[5 * i.val + 3]'(by omega)) (c.state[5 * i.val + 4]'(by omega))) := by
        show (Poseidon.rowOperandsList c.state)[i.val] = _
        exact rowOperandsList_window _ c.state hw i.val hlt
      rw [hrow]
      show CellOf _ ((recordReduction nv aux c.reduce).result[i.val]'(by
        rw [poseidon_result_length nv aux c h]; omega)).vars[j] _
      rw [List.getElem_of_eq hrows, rowsFromStates_window _ 0 _ vs (by omega) i.val hlt]
      obtain ⟨a0, b0, c0⟩ := hc (5 * i.val) (by omega) (by omega)
      obtain ⟨a1, b1, c1⟩ := hc (5 * i.val + 1) (by omega) (by omega)
      obtain ⟨a2, b2, c2⟩ := hc (5 * i.val + 2) (by omega) (by omega)
      obtain ⟨a3, b3, c3⟩ := hc (5 * i.val + 3) (by omega) (by omega)
      obtain ⟨a4, b4, c4⟩ := hc (5 * i.val + 4) (by omega) (by omega)
      fin_cases j
      exacts [a0, b0, c0, a4, b4, c4, a1, b1, c1, a2, b2, c2, a3, b3, c3]
    · have e : i.val = c.state.length / 5 := by omega
      have hrow : (KimchiConstraint.poseidon c).rowOperands[i] =
          cellsOf (PoseidonConstraint.finalCells (c.state[5 * (c.state.length / 5)]'(by
            omega))) := by
        show (Poseidon.rowOperandsList c.state)[i.val] = _
        rw [getElem_congr_idx e]
        exact rowOperandsList_final _ c.state hw
      rw [hrow]
      show CellOf _ ((recordReduction nv aux c.reduce).result[i.val]'(by
        rw [poseidon_result_length nv aux c h]; omega)).vars[j] _
      rw [List.getElem_of_eq hrows, getElem_congr_idx e,
        rowsFromStates_final _ 0 _ vs (by omega)]
      obtain ⟨a0, b0, c0⟩ := hc (5 * (c.state.length / 5)) (by omega) (by omega)
      fin_cases j
      exacts [a0, b0, c0, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
        trivial, trivial, trivial, trivial]

/-- The walk of a padding row: every name is an allocation or a term of an operand that is not
that bare variable, and the row's cells are its operands' variables cell by cell. -/
private theorem records_reducePad_names (vs : Vector (FVar F) 7) :
    Records (reducePad vs : RecordingBuilder F (Rows F)) fun row es =>
      (∀ e ∈ es, ∀ w ∈ e.names, w ∈ allocs es ∨
        ∃ x, some x ∈ padCells vs ∧ w ∈ x.termVars ∧ x ≠ .var w) ∧
      ∀ j : Fin wCols, CellOf (allocs es) row.row.vars[j] (cellsOf (padCells vs))[j] := by
  unfold reducePad
  refine records_bind (records_reduceToVariable_names _) fun v0 es0 h0 => ?_
  refine records_bind (records_reduceToVariable_names _) fun v1 es1 h1 => ?_
  refine records_bind (records_reduceToVariable_names _) fun v2 es2 h2 => ?_
  refine records_bind (records_reduceToVariable_names _) fun v3 es3 h3 => ?_
  refine records_bind (records_reduceToVariable_names _) fun v4 es4 h4 => ?_
  refine records_bind (records_reduceToVariable_names _) fun v5 es5 h5 => ?_
  refine records_bind (records_reduceToVariable_names _) fun v6 es6 h6 => ?_
  refine records_pure _ ?_
  set A := allocs (es0 ++ (es1 ++ (es2 ++ (es3 ++ (es4 ++ (es5 ++ (es6 ++ []))))))) with hA
  have h0' := operandNames_of h0 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h1' := operandNames_of h1 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h2' := operandNames_of h2 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h3' := operandNames_of h3 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h4' := operandNames_of h4 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h5' := operandNames_of h5 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have h6' := operandNames_of h6 (A := A) fun u hu => by rw [hA]; simp [allocs_append, hu]
  have hc : padCells vs = [some vs[0], some vs[1], some vs[2], some vs[3], some vs[4],
      some vs[5], some vs[6]] := rfl
  refine ⟨fun e he w hw => ?_, fun j => ?_⟩
  · simp only [List.append_nil, List.mem_append] at he
    rw [hc]
    rcases he with he | he | he | he | he | he | he
    · exact (h0'.1 e he w hw).imp_right fun h => ⟨vs[0], by simp, h⟩
    · exact (h1'.1 e he w hw).imp_right fun h => ⟨vs[1], by simp, h⟩
    · exact (h2'.1 e he w hw).imp_right fun h => ⟨vs[2], by simp, h⟩
    · exact (h3'.1 e he w hw).imp_right fun h => ⟨vs[3], by simp, h⟩
    · exact (h4'.1 e he w hw).imp_right fun h => ⟨vs[4], by simp, h⟩
    · exact (h5'.1 e he w hw).imp_right fun h => ⟨vs[5], by simp, h⟩
    · exact (h6'.1 e he w hw).imp_right fun h => ⟨vs[6], by simp, h⟩
  · rw [hc]
    fin_cases j
    exacts [⟨h0'.2.1, h0'.2.2⟩, ⟨h1'.2.1, h1'.2.2⟩, ⟨h2'.2.1, h2'.2.2⟩, ⟨h3'.2.1, h3'.2.2⟩,
      ⟨h4'.2.1, h4'.2.2⟩, ⟨h5'.2.1, h5'.2.2⟩, ⟨h6'.2.1, h6'.2.2⟩, trivial, trivial, trivial,
      trivial, trivial, trivial, trivial, trivial]

/-- A padding row's recorded reduction is placed: its names are allocations or terms of its
operands that are not that bare variable, and its one row's cells are its operands' variables
cell by cell, all seven in wired columns. -/
theorem pad_placed (nv : Variable) (aux : AuxState F) (vs : Vector (FVar F) 7) :
    Placed nv aux (.pad vs) := by
  obtain ⟨hn, hc⟩ := recordReduction_of_records (records_reducePad_names vs) nv aux
  refine ⟨fun e he w hw => (hn e he w hw).imp_right ?_, rfl, fun i j => ?_⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, mem_placedOperands (List.mem_singleton_self _)
      (mem_cellsOf (by simp [padCells]) hx), h⟩
  · fin_cases i
    exact hc j

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

private theorem records_endoScalarRound_absent (r : EndoScalarRound F) :
    Records (r.reduce : RecordingBuilder F (KimchiRow F)) fun _ es => AbsentAll es := by
  unfold EndoScalarRound.reduce
  records [records_reduceToVariable_absent _]
  absent_leaf

private theorem records_endoScalar_absent :
    (rounds : EndoScalar F) →
      Records (EndoScalar.reduce rounds : RecordingBuilder F (List (KimchiRow F))) fun _ es =>
        AbsentAll es
  | [] => records_pure _ absentAll_nil
  | r :: rs => by
    unfold EndoScalar.reduce
    records [records_endoScalarRound_absent r, records_endoScalar_absent rs]
    absent_leaf

private theorem records_scaleRound_absent (r : ScaleRound F) :
    Records (r.reduce : RecordingBuilder F (KimchiRow F × KimchiRow F)) fun _ es =>
      AbsentAll es := by
  unfold ScaleRound.reduce
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_pure _ ?_
  absent_leaf

private theorem records_varBaseMul_absent :
    (rounds : VarBaseMul F) →
      Records (VarBaseMul.reduce rounds : RecordingBuilder F (List (KimchiRow F × KimchiRow F)))
        fun _ es => AbsentAll es
  | [] => records_pure _ absentAll_nil
  | r :: rs => by
    unfold VarBaseMul.reduce
    records [records_scaleRound_absent r, records_varBaseMul_absent rs]
    absent_leaf

private theorem records_endoMulRound_absent (r : EndoMulRound F) :
    Records (r.reduce : RecordingBuilder F (KimchiRow F)) fun _ es => AbsentAll es := by
  unfold EndoMulRound.reduce
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_bind (records_reduceToVariable_absent _) fun _ _ _ => ?_
  refine records_pure _ ?_
  absent_leaf

private theorem records_endoMulRounds_absent :
    (state : List (EndoMulRound F)) →
      Records (EndoMul.reduceRounds state : RecordingBuilder F (List (KimchiRow F))) fun _ es =>
        AbsentAll es
  | [] => records_pure _ absentAll_nil
  | r :: rs => by
    unfold EndoMul.reduceRounds
    records [records_endoMulRound_absent r, records_endoMulRounds_absent rs]
    absent_leaf

private theorem records_endoMul_absent (c : EndoMul F) :
    Records (EndoMul.reduce c : RecordingBuilder F (List (KimchiRow F))) fun _ es =>
      AbsentAll es := by
  unfold EndoMul.reduce
  records [records_reduceToVariable_absent _, records_endoMulRounds_absent c.state]
  absent_leaf

private theorem records_reduceState_absent (t : FVar F × FVar F × FVar F) :
    Records (reduceState t : RecordingBuilder F (Variable × Variable × Variable)) fun _ es =>
      AbsentAll es := by
  unfold reduceState
  records [records_reduceToVariable_absent _]
  absent_leaf

private theorem records_reduceStates_absent :
    (ts : List (FVar F × FVar F × FVar F)) →
      Records (reduceStates ts : RecordingBuilder F (List (Variable × Variable × Variable)))
        fun _ es => AbsentAll es
  | [] => records_pure _ absentAll_nil
  | t :: ts => by
    unfold reduceStates
    records [records_reduceState_absent t, records_reduceStates_absent ts]
    absent_leaf

private theorem records_poseidon_absent (c : PoseidonConstraint F) :
    Records (c.reduce : RecordingBuilder F (List (KimchiRow F))) fun _ es => AbsentAll es := by
  unfold PoseidonConstraint.reduce
  records [records_reduceStates_absent c.state]
  absent_leaf

private theorem records_reducePad_absent (vs : Vector (FVar F) 7) :
    Records (reducePad vs : RecordingBuilder F (Rows F)) fun _ es => AbsentAll es := by
  unfold reducePad
  records [records_reduceToVariable_absent _]
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

/-- Every equation a decomposition's recorded reduction queues carries no coefficient on an
absent cell. -/
theorem endoScalar_absentZero (nv : Variable) (aux : AuxState F) (rounds : EndoScalar F) :
    ∀ e ∈ (recordReduction nv aux (EndoScalar.reduce rounds)).events, ∀ g, e.queued? = some g →
      g.AbsentZero :=
  recordReduction_of_records (records_endoScalar_absent rounds) nv aux

/-- Every equation a multiplication's recorded reduction queues carries no coefficient on an
absent cell. -/
theorem varBaseMul_absentZero (nv : Variable) (aux : AuxState F) (rounds : VarBaseMul F) :
    ∀ e ∈ (recordReduction nv aux (VarBaseMul.reduce rounds)).events, ∀ g, e.queued? = some g →
      g.AbsentZero :=
  recordReduction_of_records (records_varBaseMul_absent rounds) nv aux

/-- Every equation an endomorphism multiplication's recorded reduction queues carries no
coefficient on an absent cell. -/
theorem endoMul_absentZero (nv : Variable) (aux : AuxState F) (c : EndoMul F) :
    ∀ e ∈ (recordReduction nv aux (EndoMul.reduce c)).events, ∀ g, e.queued? = some g →
      g.AbsentZero :=
  recordReduction_of_records (records_endoMul_absent c) nv aux

/-- Every equation a Poseidon block's recorded reduction queues carries no coefficient on an
absent cell. -/
theorem poseidon_absentZero (nv : Variable) (aux : AuxState F) (c : PoseidonConstraint F) :
    ∀ e ∈ (recordReduction nv aux c.reduce).events, ∀ g, e.queued? = some g → g.AbsentZero :=
  recordReduction_of_records (records_poseidon_absent c) nv aux

/-- Every equation a padding row's recorded reduction queues carries no coefficient on an
absent cell. -/
theorem pad_absentZero (nv : Variable) (aux : AuxState F) (vs : Vector (FVar F) 7) :
    ∀ e ∈ (recordReduction nv aux (reducePad vs)).events, ∀ g, e.queued? = some g →
      g.AbsentZero :=
  recordReduction_of_records (records_reducePad_absent vs) nv aux

end NameWalks

end Snarky.Kimchi
