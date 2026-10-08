import Snarky.Kimchi.Backend.Admissibility

/-!
# The scope checker

`KimchiConstraint.Wired.Scoped` is decidable, but its instance counts every unwired operand
over the whole occurrence list. `checkScoped` decides the same condition in two passes over
the source, and `scopedFailure?` says why a source is rejected.

The first pass walks `occurrences` once, recording which variables it has met at least once
and which at least twice. The condition needs no more than that: an unwired operand occurs
exactly once when it has been met and has not been met twice. The second pass checks each
constraint: it is wired, and each of its unwired operands occurs exactly once.

## Main definitions

- `ScopedFailure`, `scopedFailure?`: the first reason a source is out of scope, if any.
- `checkScoped`: the source is in scope.

## Main results

- `checkScoped_eq_true_iff`: the checker accepts exactly the sources in scope.

## Implementation notes

The two sets are naturals read as bit sets, private to this module. A variable's bit is set
only after the variable is found below the counter, so a stray large identifier is reported
without allocating a set of its size.

Failures are reported in this order. First the range pass, in occurrence order: the source's
constraints in list order, each constraint's term variables in order, then the public
variables; the first variable at or above the counter is reported, with its constraint's
index or as a public variable. Only when every variable is in range, the constraints in list
order: a constraint that is not wired, otherwise its first unwired operand, in row and cell
order, that does not occur exactly once. The theorem is about acceptance alone; the reported
failure is decided on concrete sources by the checks.

The theorem is proved for every source and does not depend on running the checker. Running
it natively makes checked compilation usable; it does not by itself give a kernel-checked
proof that one particular large source is accepted. Evaluating the checker in the kernel on
a whole application's occurrence list in one step exceeded the memory this development
allows for a check, and how such a concrete fact is to be certified is not settled here.
-/

open Kimchi

namespace Snarky.Kimchi

open Snarky

variable {F : Type}

/-- Why a source is out of scope. -/
inductive ScopedFailure where
  /-- Constraint `i` names the variable `v`, at or above the counter. -/
  | outOfRange (i : Nat) (v : Variable)
  /-- The public variable `v` is at or above the counter. -/
  | publicOutOfRange (v : Variable)
  /-- Constraint `i` is not wired: a Poseidon block off the shape, or an operand in an unwired
  column that is not a bare variable. -/
  | notWired (i : Nat)
  /-- Constraint `i` places `v` in an unwired column, and `v` does not occur exactly once among
  the term occurrences and the public variables. -/
  | reused (i : Nat) (v : Variable)
  deriving DecidableEq

/-! ## The two sets -/

/-- The variables met so far, as two bit sets: `seen` at least once, `repeated` at least
twice. -/
private structure Seen where
  /-- The variables met at least once. -/
  seen : Nat
  /-- The variables met at least twice. -/
  repeated : Nat

/-- Meet `v`: it is repeated if it was seen, and it is seen. -/
private def Seen.mark (s : Seen) (v : Variable) : Seen :=
  ⟨s.seen ||| 1 <<< v, s.repeated ||| (s.seen &&& 1 <<< v)⟩

/-- `v` has been met exactly once. -/
private def Seen.once (s : Seen) (v : Variable) : Bool :=
  s.seen.testBit v && !s.repeated.testBit v

private theorem Seen.mark_seen (s : Seen) (w v : Variable) :
    (s.mark w).seen.testBit v = (s.seen.testBit v || decide (w = v)) := by
  simp [Seen.mark, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

private theorem Seen.mark_repeated (s : Seen) (w v : Variable) :
    (s.mark w).repeated.testBit v =
      (s.repeated.testBit v || (s.seen.testBit v && decide (w = v))) := by
  simp [Seen.mark, Nat.testBit_or, Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow]

/-- After a list is marked, the seen variables are those seen before and the list's. -/
private theorem foldl_mark_seen (xs : List Variable) (s : Seen) (v : Variable) :
    (xs.foldl Seen.mark s).seen.testBit v = true ↔ s.seen.testBit v = true ∨ v ∈ xs := by
  induction xs generalizing s with
  | nil => simp
  | cons w ws ih =>
    rw [List.foldl_cons, ih, Seen.mark_seen]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h

/-- After a list is marked, the repeated variables are those repeated before, those seen
before and in the list, and those the list holds twice. -/
private theorem foldl_mark_repeated (xs : List Variable) (s : Seen) (v : Variable) :
    (xs.foldl Seen.mark s).repeated.testBit v = true ↔
      s.repeated.testBit v = true ∨ (s.seen.testBit v = true ∧ v ∈ xs) ∨ 2 ≤ xs.count v := by
  induction xs generalizing s with
  | nil => simp
  | cons w ws ih =>
    rw [List.foldl_cons, ih, Seen.mark_repeated, Seen.mark_seen]
    have hmem : 2 ≤ ws.count v → v ∈ ws := fun h => List.one_le_count_iff.mp (by omega)
    by_cases hw : w = v
    · subst hw
      have hc : 2 ≤ (w :: ws).count w ↔ w ∈ ws := by
        rw [List.count_cons_self, ← List.one_le_count_iff]
        omega
      rw [hc]
      simp only [decide_true, Bool.and_true, Bool.or_true, Bool.or_eq_true, true_and,
        List.mem_cons, true_or, and_true]
      tauto
    · have hc : (w :: ws).count v = ws.count v := List.count_cons_of_ne hw
      have hv : v ≠ w := fun h => hw h.symm
      rw [hc]
      simp only [hw, decide_false, Bool.and_false, Bool.or_false, List.mem_cons, hv, false_or]

/-- A variable is seen after a list is marked from nothing when the list holds it. -/
private theorem seen_iff (xs : List Variable) (v : Variable) :
    (xs.foldl Seen.mark ⟨0, 0⟩).seen.testBit v = true ↔ v ∈ xs := by
  rw [foldl_mark_seen]
  simp

/-- A variable is repeated after a list is marked from nothing when the list holds it twice. -/
private theorem repeated_iff (xs : List Variable) (v : Variable) :
    (xs.foldl Seen.mark ⟨0, 0⟩).repeated.testBit v = true ↔ 2 ≤ xs.count v := by
  rw [foldl_mark_repeated]
  simp

/-- A variable is met exactly once by a list when the list holds it exactly once. -/
private theorem once_iff (xs : List Variable) (v : Variable) :
    (xs.foldl Seen.mark ⟨0, 0⟩).once v = true ↔ xs.count v = 1 := by
  have h1 := seen_iff xs v
  have h2 := repeated_iff xs v
  have h3 : v ∈ xs ↔ 1 ≤ xs.count v := List.one_le_count_iff.symm
  simp only [Seen.once, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true]
  rw [h1, h2, h3]
  omega

/-! ## The range pass -/

/-- Mark a list's variables, stopping at the first at or above the counter before it is
marked. -/
private def scanVars (nv : Variable) : Seen → List Variable → Except Variable Seen
  | s, [] => .ok s
  | s, v :: vs => if v < nv then scanVars nv (s.mark v) vs else .error v

private theorem scanVars_ok_iff (nv : Variable) (vs : List Variable) (s s' : Seen) :
    scanVars nv s vs = .ok s' ↔ (∀ v ∈ vs, v < nv) ∧ s' = vs.foldl Seen.mark s := by
  induction vs generalizing s with
  | nil => simp [scanVars, eq_comm]
  | cons v vs ih =>
    by_cases hv : v < nv
    · simp [scanVars, hv, ih]
    · simp [scanVars, hv]

section Source

variable [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]

/-- Mark the source's term variables constraint by constraint, stopping at the first at or
above the counter, reported with its constraint's index. -/
private def scanSource (nv : Variable) :
    Nat → Seen → List (KimchiConstraint F) → Except ScopedFailure Seen
  | _, s, [] => .ok s
  | i, s, c :: cs =>
    match scanVars nv s c.termVars with
    | .error v => .error (.outOfRange i v)
    | .ok s' => scanSource nv (i + 1) s' cs

private theorem scanSource_ok_iff (nv : Variable) (cs : List (KimchiConstraint F)) (i : Nat)
    (s s' : Seen) :
    scanSource nv i s cs = .ok s' ↔
      (∀ v ∈ cs.flatMap KimchiConstraint.termVars, v < nv) ∧
        s' = (cs.flatMap KimchiConstraint.termVars).foldl Seen.mark s := by
  induction cs generalizing i s with
  | nil => simp [scanSource, eq_comm]
  | cons c cs ih =>
    rw [scanSource, List.flatMap_cons, List.foldl_append, List.forall_mem_append]
    cases h : scanVars nv s c.termVars with
    | error v =>
      have hno : ¬ ∀ v ∈ c.termVars, v < nv := fun hall => by
        have := (scanVars_ok_iff nv c.termVars s _).mpr ⟨hall, rfl⟩
        rw [h] at this
        cases this
      simp [hno]
    | ok s1 =>
      obtain ⟨hall, rfl⟩ := (scanVars_ok_iff nv c.termVars s s1).mp h
      dsimp only
      rw [ih]
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨hall, h1⟩, h2⟩, fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, h2⟩⟩

/-! ## The constraint pass -/

/-- The first constraint that is not wired, or that places in an unwired column an operand
not met exactly once. -/
private def firstUnscoped (s : Seen) : Nat → List (KimchiConstraint F) → Option ScopedFailure
  | _, [] => none
  | i, c :: cs =>
    if c.Wired then
      match c.unwiredVars.find? fun v => !s.once v with
      | some v => some (.reused i v)
      | none => firstUnscoped s (i + 1) cs
    else some (.notWired i)

omit [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] in
private theorem firstUnscoped_eq_none_iff (s : Seen) (cs : List (KimchiConstraint F)) (i : Nat) :
    firstUnscoped s i cs = none ↔
      ∀ c ∈ cs, c.Wired ∧ ∀ v ∈ c.unwiredVars, s.once v = true := by
  induction cs generalizing i with
  | nil => simp [firstUnscoped]
  | cons c cs ih =>
    rw [firstUnscoped, List.forall_mem_cons]
    by_cases hw : c.Wired
    · rw [if_pos hw]
      cases hf : c.unwiredVars.find? fun v => !s.once v with
      | some v =>
        have hv := List.find?_some hf
        have hm := List.mem_of_find?_eq_some hf
        simp only [reduceCtorEq, false_iff]
        intro h
        have := h.1.2 v hm
        simp [this] at hv
      | none =>
        have hall : ∀ v ∈ c.unwiredVars, s.once v = true := fun v hv => by
          have := List.find?_eq_none.mp hf v hv
          simpa using this
        dsimp only
        rw [ih]
        exact ⟨fun h => ⟨⟨hw, hall⟩, h⟩, fun h => h.2⟩
    · simp [hw]

/-! ## The checker -/

/-- The first reason the source is out of scope at the counter and the public variables, or
`none` when it is in scope: a variable at or above the counter, in occurrence order; else the
first constraint that is not wired or has an unwired operand not occurring exactly once. -/
def scopedFailure? (nv : Variable) (source : List (KimchiConstraint F))
    (publicVars : List Variable) : Option ScopedFailure :=
  match scanSource nv 0 ⟨0, 0⟩ source with
  | .error f => some f
  | .ok s =>
    match scanVars nv s publicVars with
    | .error v => some (.publicOutOfRange v)
    | .ok s => firstUnscoped s 0 source

/-- The source is in scope at the counter and the public variables. -/
def checkScoped (nv : Variable) (source : List (KimchiConstraint F))
    (publicVars : List Variable) : Bool :=
  (scopedFailure? nv source publicVars).isNone

/-- The checker accepts exactly the sources in scope. -/
theorem checkScoped_eq_true_iff {nv : Variable} {source : List (KimchiConstraint F)}
    {publicVars : List Variable} :
    checkScoped nv source publicVars = true ↔
      KimchiConstraint.Wired.Scoped nv source publicVars := by
  have hocc : occurrences source publicVars =
      source.flatMap KimchiConstraint.termVars ++ publicVars := rfl
  rw [checkScoped, Option.isNone_iff_eq_none, scopedFailure?]
  cases h1 : scanSource nv 0 ⟨0, 0⟩ source with
  | error f =>
    simp only [reduceCtorEq, false_iff]
    intro hsc
    have := (scanSource_ok_iff nv source 0 ⟨0, 0⟩ _).mpr
      ⟨fun v hv => hsc.below v (by rw [hocc]; exact List.mem_append_left _ hv), rfl⟩
    rw [h1] at this
    cases this
  | ok s1 =>
    obtain ⟨hb1, rfl⟩ := (scanSource_ok_iff nv source 0 ⟨0, 0⟩ s1).mp h1
    dsimp only
    cases h2 : scanVars nv ((source.flatMap KimchiConstraint.termVars).foldl Seen.mark ⟨0, 0⟩)
        publicVars with
    | error v =>
      simp only [reduceCtorEq, false_iff]
      intro hsc
      have := (scanVars_ok_iff nv publicVars
        ((source.flatMap KimchiConstraint.termVars).foldl Seen.mark ⟨0, 0⟩) _).mpr
        ⟨fun v hv => hsc.below v (by rw [hocc]; exact List.mem_append_right _ hv), rfl⟩
      rw [h2] at this
      cases this
    | ok s2 =>
      obtain ⟨hb2, rfl⟩ := (scanVars_ok_iff nv publicVars _ s2).mp h2
      dsimp only
      rw [firstUnscoped_eq_none_iff, ← List.foldl_append, ← hocc]
      constructor
      · intro h
        refine ⟨fun c hc => (h c hc).1, fun v hv => ?_,
          fun c hc v hv => (once_iff _ v).mp ((h c hc).2 v hv)⟩
        rw [hocc] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact hb1 v hv
        · exact hb2 v hv
      · intro hsc c hc
        exact ⟨hsc.wired c hc, fun v hv => (once_iff _ v).mpr (hsc.unwiredOnce c hc v hv)⟩

end Source

end Snarky.Kimchi
