import Snarky.Circuit.CVar

/-!
# The prover's assignment store

Port of `Snarky.Backend.Assignments` (packages/snarky/src/Snarky/Backend/Assignments.purs):
the prover-side witness table mapping variables to field values, and its extension order.

The PS original is a dense mutable `STArray Global (Maybe f)` with write-once slots:
`fresh` creates the store, `set` writes a slot (grow with `Nothing` padding, then poke),
`lookup` reads it purely under a prose write-once CONTRACT (the branch's single sanctioned
`unsafePerformEffect`, justified there by a ~40% prove-time measurement), and
`Frozen`/`freeze`/`lookupFrozen`/`toLookup` snapshot it for pure consumers. The Lean
rendering is a pure function `Variable → Option F`, which collapses most of that surface:

- PS `fresh`  ↦ `Assignments.empty`
- PS `set`    ↦ `Assignments.extend` (pure functional update)
- PS `lookup` ↦ plain application (`env v`) — no effect escape hatch to justify
- PS `Frozen`/`freeze`/`lookupFrozen`/`toLookup` ↦ not ported: the pure function is its
  own snapshot
- `extendPairs` is Lean-only: a guarded batch write that ERRORS on re-assignment, turning
  the PS write-once contract from prose into an enforced invariant.

Lean-only additions with no PS analogue: the extension order `Assignments.Le` ("every
assigned variable keeps its value") with its lemmas and `CVar.eval_le` — an assignment
that only grows preserves successful evaluations; and `Valuation`, a total assignment,
with the completion maps in both directions (`Valuation.toAssignments`,
`Assignments.toValuation`) and the lemmas bridging the total and partial readings.
-/

namespace Snarky

/-- A partial assignment of field values to variables — the prover's witness table
(PS `Assignments f`, as a pure lookup instead of the mutable write-once store). -/
abbrev Assignments (F : Type u) := Variable → Option F

/-- A total assignment: every variable has a value, so evaluation cannot fail. -/
abbrev Valuation (F : Type u) := Variable → F

/-- Read a valuation as an everywhere-defined partial assignment, under which
evaluation never fails. -/
def Valuation.toAssignments (V : Valuation F) : Assignments F :=
  fun v => some (V v)

/-- Complete a partial table to a total valuation, defaulting unassigned slots to
zero — the reverse of `Valuation.toAssignments`. -/
def Assignments.toValuation [Zero F] (env : Assignments F) : Valuation F :=
  fun v => (env v).getD 0

namespace Assignments

/-- The empty assignment (PS `fresh`). -/
def empty : Assignments F := fun _ => none

/-- Assign `x` to `v`, leaving every other variable unchanged (PS `set`, as a pure
functional update). -/
def extend (a : Assignments F) (v : Variable) (x : F) : Assignments F :=
  fun w => if w = v then some x else a w

/-- The extended slot reads back its value. -/
@[circuitVal] theorem eval_var_extend [Add F] [Mul F] (a : Assignments F)
    (v : Variable) (x : F) : (CVar.var v).eval (a.extend v x) = .ok x := by
  simp [CVar.eval, extend]

/-- Guarded batch extension: assign each `(variable, value)` pair left to right, erroring
on any variable that is already assigned — extension by `extendPairs` is monotone in
`Assignments.Le`, and re-assignment is the only failure mode. -/
def extendPairs (a : Assignments F) : List (Variable × F) → Except EvalError (Assignments F)
  | [] => .ok a
  | (v, x) :: rest =>
    match a v with
    | some _ => .error (.conflict v)
    | none => (a.extend v x).extendPairs rest

/-- `a.Le a'` iff every variable assigned in `a` has the same value in `a'`. -/
protected def Le (a a' : Assignments F) : Prop :=
  ∀ v x, a v = some x → a' v = some x

/-- `a.FreshFrom nv`: nothing at or above the counter is assigned. -/
protected def FreshFrom (a : Assignments F) (nv : Nat) : Prop :=
  ∀ v, nv ≤ v → a v = none

protected theorem Le.refl (a : Assignments F) : a.Le a := fun _ _ h => h

protected theorem Le.trans {a b c : Assignments F} (h₁ : a.Le b) (h₂ : b.Le c) : a.Le c :=
  fun v x h => h₂ v x (h₁ v x h)

private theorem le_extend {a : Assignments F} {v : Variable} (hv : a v = none) (x : F) :
    a.Le (a.extend v x) := by
  intro w y hw
  simp only [extend]
  split
  · next hwv => rw [hwv, hv] at hw; cases hw
  · exact hw

/-- Completion extends the table: assigned slots keep their values. -/
theorem le_toValuation [Zero F] (env : Assignments F) :
    env.Le env.toValuation.toAssignments := by
  intro v x hv
  show some ((env v).getD 0) = some x
  rw [hv]
  rfl

/-- Extending a fresh slot only grows the table. -/
theorem le_extend_self {a : Assignments F} {nv : Nat} (h : a.FreshFrom nv) (x : F) :
    a.Le (a.extend nv x) :=
  le_extend (h nv (Nat.le_refl nv)) x

theorem le_extendPairs {a a' : Assignments F} :
    ∀ {l : List (Variable × F)}, a.extendPairs l = .ok a' → a.Le a' := by
  intro l
  induction l generalizing a with
  | nil =>
    intro h
    simp only [extendPairs, Except.ok.injEq] at h
    subst h
    exact Assignments.Le.refl a
  | cons vx rest ih =>
    obtain ⟨v, x⟩ := vx
    intro h
    simp only [extendPairs] at h
    split at h
    · cases h
    · next hnone => exact (le_extend hnone x).trans (ih h)

/-- A variable the batch never targets keeps its unassigned status. -/
theorem extendPairs_none {a a' : Assignments F} {v : Variable} :
    ∀ {l : List (Variable × F)}, a.extendPairs l = .ok a' →
      (∀ p ∈ l, p.1 ≠ v) → a v = none → a' v = none := by
  intro l
  induction l generalizing a with
  | nil =>
    intro h _ hv
    simp only [extendPairs, Except.ok.injEq] at h
    exact h ▸ hv
  | cons p rest ih =>
    intro h hne hv
    simp only [extendPairs] at h
    split at h
    · cases h
    · refine ih h (fun q hq => hne q (List.mem_cons_of_mem _ hq)) ?_
      simp only [extend]
      rw [if_neg (fun hv' => hne p (List.mem_cons_self ..) hv'.symm)]
      exact hv

end Assignments

/-! ## Evaluation is monotone in the extension order -/

namespace CVar

/-- Successful evaluations are stable under assignment extension: the value of an affine
expression cannot change once all its variables are assigned. -/
theorem eval_le [Add F] [Mul F] {a a' : Assignments F} (hle : a.Le a') {x : CVar F} {v : F}
    (h : x.eval a = .ok v) : x.eval a' = .ok v := by
  induction x generalizing v with
  | var w =>
    simp only [eval] at h ⊢
    split at h
    · next y hy => rw [hle w y hy]; exact h
    · cases h
  | const k => exact h
  | add p q ihp ihq =>
    simp only [eval] at h ⊢
    split at h
    · cases h
    · next xa hxa =>
      split at h
      · cases h
      · next xb hxb => rw [ihp hxa, ihq hxb]; exact h
  | scale k p ih =>
    simp only [eval] at h ⊢
    split at h
    · cases h
    · next y hy => rw [ih hy]; exact h

/-- On a total valuation, evaluation never fails and computes the total reading —
the bridge between the prover-side `Except` laws and the soundness-side `val`
statements. -/
theorem eval_toAssignments [Add F] [Mul F] (x : CVar F) (V : Valuation F) :
    x.eval V.toAssignments = .ok (x.val V) := by
  induction x with
  | var v => rfl
  | const k => rfl
  | add a b iha ihb => simp only [eval, val, iha, ihb]
  | scale k y ih => simp only [eval, val, ih]

/-- A successful evaluation persists at the completed valuation. -/
theorem val_toValuation [Add F] [Mul F] [Zero F] {env : Assignments F} {x : CVar F}
    {xv : F} (h : x.eval env = .ok xv) : x.val env.toValuation = xv := by
  have h' := eval_le (Assignments.le_toValuation env) h
  rw [eval_toAssignments] at h'
  injection h'

/-- `add_` reads as the sum — the fold-evaluation lemma `eval_add_`, carried through
the bridge to the total reading. -/
@[circuitVal] theorem val_add_ [Add F] [Mul F] (a b : CVar F) (V : Valuation F) :
    (CVar.add_ a b).val V = a.val V + b.val V := by
  have h := (CVar.eval_add_ a b V.toAssignments).trans
    (eval_toAssignments (CVar.add a b) V)
  rw [eval_toAssignments] at h
  injection h

/-- `scale_` reads as the scalar product — the fold-evaluation lemma `eval_scale_`,
carried through the bridge to the total reading. -/
@[circuitVal] theorem val_scale_ [Add F] [MulZeroOneClass F] [DecidableEq F] (k : F) (x : CVar F)
    (V : Valuation F) : (CVar.scale_ k x).val V = k * x.val V := by
  have h := CVar.eval_scale_ (eval_toAssignments x V) k
  rw [eval_toAssignments] at h
  injection h

/-- `sub_` reads as the difference — the fold-evaluation lemma `eval_sub_`, carried
through the bridge to the total reading. -/
@[circuitVal] theorem val_sub_ [CommRing F] [DecidableEq F] (a b : CVar F) (V : Valuation F) :
    (CVar.sub_ a b).val V = a.val V - b.val V := by
  have h := CVar.eval_sub_ (eval_toAssignments a V) (eval_toAssignments b V)
  rw [eval_toAssignments] at h
  injection h

end CVar

/-- Successful `mapM`-evaluation is stable under assignment extension — the list form
of `CVar.eval_le`. -/
theorem mapM_eval_le [Add F] [Mul F] {env env' : Assignments F}
    (hle : env.Le env') :
    ∀ {xs : List (CVar F)} {vs : List F},
      xs.mapM (CVar.eval · env) = .ok vs → xs.mapM (CVar.eval · env') = .ok vs
  | [], _, h => h
  | x :: xs, vs, h => by
    cases he : x.eval env with
    | error e => simp [List.mapM_cons, he, Bind.bind, Except.bind] at h
    | ok y =>
      cases hr : xs.mapM (CVar.eval · env) with
      | error e => simp [List.mapM_cons, he, hr, Bind.bind, Except.bind] at h
      | ok ys =>
        simp only [List.mapM_cons, he, hr, Bind.bind, Except.bind, Pure.pure,
          Except.pure] at h
        simp [List.mapM_cons, CVar.eval_le hle he, mapM_eval_le hle hr, Bind.bind,
          Except.bind, Pure.pure, Except.pure, h]

/-- Elementwise reads assemble into a `mapM`-evaluation — the introduction the bulk
witness grants feed. -/
theorem mapM_eval_ok [Add F] [Mul F] {env : Assignments F} :
    ∀ {xs : List (CVar F)} {vs : List F}, xs.length = vs.length →
      (∀ j (hj : j < xs.length) (hj' : j < vs.length), xs[j].eval env = .ok vs[j]) →
      xs.mapM (CVar.eval · env) = .ok vs
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | x :: xs, v :: vs, hlen, hj => by
    have h0 := hj 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    have ih := mapM_eval_ok (env := env) (xs := xs) (vs := vs) (by simpa using hlen)
      (fun j hj1 hj2 => by
        have := hj (j + 1) (by simpa using hj1) (by simpa using hj2)
        simpa only [List.getElem_cons_succ] using this)
    simp [List.mapM_cons, h0, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]

end Snarky
