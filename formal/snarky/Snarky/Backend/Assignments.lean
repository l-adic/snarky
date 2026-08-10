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
assigned variable keeps its value") and its lemmas, including `CVar.eval_le`. They are the
backbone of the interpreter laws in `Backend/{Builder,Prover}`: the prover only ever *extends*
assignments (via the guarded `extendPairs`), so constraint checks performed early in a run
remain valid against the final assignment. Also Lean-only: `Valuation`, the total
assignment the soundness laws quantify over (a deployed wire table assigns every
variable), with `toAssignments` and the bridge `CVar.eval_toAssignments` connecting it
to the `Except` layer.

Public results: the order `Assignments.Le` (with `Le.refl`/`Le.trans`), the monotonicity
law `Assignments.le_extendPairs`, the audited root `CVar.eval_le`, and the valuation
seam (`Valuation.toAssignments`, `CVar.eval_toAssignments`); `le_extend` is private
machinery.
-/

namespace Snarky

/-- A partial assignment of field values to variables — the prover's witness table
(PS `Assignments f`, as a pure lookup instead of the mutable write-once store). -/
abbrev Assignments (F : Type u) := Variable → Option F

/-- A total assignment — the adversarial-witness reading the soundness laws quantify
over. A deployed wire table assigns every variable, so the soundness layer takes
totality in the type instead of threading evaluation success through every statement;
partiality stays with the prover model above. -/
abbrev Valuation (F : Type u) := Variable → F

/-- Read a valuation as an everywhere-defined partial assignment — the seam to the
`Except`-based interpreter laws, under which evaluation never fails. -/
def Valuation.toAssignments (V : Valuation F) : Assignments F :=
  fun v => some (V v)

namespace Assignments

/-- The empty assignment (PS `fresh`). -/
def empty : Assignments F := fun _ => none

/-- Assign `x` to `v`, leaving every other variable unchanged (PS `set`, as a pure
functional update). -/
def extend (a : Assignments F) (v : Variable) (x : F) : Assignments F :=
  fun w => if w = v then some x else a w

/-- Guarded batch extension: assign each `(variable, value)` pair left to right, erroring
on any variable that is already assigned — this is what makes prover runs monotone in
`Assignments.Le`. Callers zip equal-length allocation and witness vectors, so pairing is
total by construction and the only failure mode is a re-assignment. -/
def extendPairs (a : Assignments F) : List (Variable × F) → Except EvalError (Assignments F)
  | [] => .ok a
  | (v, x) :: rest =>
    match a v with
    | some _ => .error (.conflict v)
    | none => (a.extend v x).extendPairs rest

/-- `a.Le a'` iff every variable assigned in `a` has the same value in `a'` — assignments
only ever grow during a prover run. -/
protected def Le (a a' : Assignments F) : Prop :=
  ∀ v x, a v = some x → a' v = some x

/-- `a.FreshFrom nv`: nothing at or above the counter is assigned. The invariant gadget
completeness runs from, and — since `prove` refuses to assign at or above its counter —
one every prover run preserves (`prove_freshFrom`). -/
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

/-- Extending a fresh slot only grows the table — the `Le` fact a one-variable
allocation hands its caller. -/
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

end Snarky
