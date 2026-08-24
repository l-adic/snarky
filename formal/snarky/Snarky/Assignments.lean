import Snarky.Circuit

namespace Snarky

universe u

/-- A partial assignment of field values to variables — the prover's witness table
(PS `Assignments f`, as a pure lookup instead of the mutable write-once store). -/
abbrev Assignments (F : Type u) := Variable → Option F

namespace Assignments

variable {F : Type u}

/-- The total reading of the table: an unassigned slot reads `0`. -/
def get [Zero F] (a : Assignments F) (v : Variable) : F := (a v).getD 0

/-- Assign `x` to `v`, leaving every other variable unchanged. -/
def extend (a : Assignments F) (v : Variable) (x : F) : Assignments F :=
  fun w => if w = v then some x else a w

/-- Write `xs` at consecutive slots from `nv`. -/
def extendList (a : Assignments F) (nv : Nat) : List F → Assignments F
  | [] => a
  | x :: xs => (a.extend nv x).extendList (nv + 1) xs

/-- The table is defined exactly below the counter. -/
protected def Dom (a : Assignments F) (nv : Nat) : Prop :=
  ∀ v, (a v).isSome ↔ v < nv

/-- The empty table. -/
def empty : Assignments F := fun _ => none

/-- The empty table is defined below `0`, vacuously. -/
theorem empty_dom : Assignments.Dom (empty : Assignments F) 0 := fun v => by simp [empty]

/-- `a.Le a'` iff every variable assigned in `a` has the same value in `a'`. -/
protected def Le (a a' : Assignments F) : Prop :=
  ∀ v x, a v = some x → a' v = some x

protected theorem Le.refl (a : Assignments F) : a.Le a := fun _ _ h => h

protected theorem Le.trans {a b c : Assignments F} (h₁ : a.Le b) (h₂ : b.Le c) : a.Le c :=
  fun v x h => h₂ v x (h₁ v x h)

@[simp] private theorem extend_self (a : Assignments F) (v : Variable) (x : F) :
    a.extend v x v = some x := by
  simp [extend]

@[simp] private theorem extend_ne (a : Assignments F) {v w : Variable} (x : F) (h : w ≠ v) :
    a.extend v x w = a w := by
  simp [extend, h]

/-- Write `x` at `v`, refusing a slot that is already assigned — the write-once
discipline, for tables that carry no counter invariant of their own. -/
def extendFresh (a : Assignments F) (v : Variable) (x : F) :
    Except EvalError (Assignments F) :=
  match a v with
  | some _ => .error (.custom "extendFresh: variable already assigned")
  | none => .ok (a.extend v x)

/-- A guarded write only extends the table. -/
theorem le_extendFresh {a a' : Assignments F} {v : Variable} {x : F}
    (h : a.extendFresh v x = .ok a') : a.Le a' := by
  unfold extendFresh at h
  split at h
  · cases h
  next hv =>
    cases h
    intro w y hw
    by_cases hwv : w = v
    · subst hwv
      rw [hv] at hw
      exact absurd hw (by simp)
    · rw [extend_ne _ _ hwv]
      exact hw

private theorem extendList_below {a : Assignments F} :
    ∀ {xs : List F} {nv v : Nat}, v < nv → a.extendList nv xs v = a v
  | [], _, _, _ => rfl
  | _ :: xs, nv, v, h => by
    simp only [extendList]
    rw [extendList_below (xs := xs) (show v < nv + 1 by omega)]
    exact extend_ne _ _ (show v ≠ nv by omega)

private theorem extendList_above {a : Assignments F} :
    ∀ {xs : List F} {nv v : Nat}, nv + xs.length ≤ v → a.extendList nv xs v = a v
  | [], _, _, _ => rfl
  | _ :: xs, nv, v, h => by
    simp only [extendList, List.length_cons] at h ⊢
    rw [extendList_above (xs := xs) (show nv + 1 + xs.length ≤ v by omega)]
    exact extend_ne _ _ (show v ≠ nv by omega)

theorem extendList_get {a : Assignments F} :
    ∀ {xs : List F} {nv i : Nat} (h : i < xs.length), a.extendList nv xs (nv + i) = some xs[i]
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: xs, nv, 0, _ => by
    simp only [extendList]
    rw [extendList_below (xs := xs) (show nv + 0 < nv + 1 by omega)]
    simp
  | _ :: _, nv, i + 1, h => by
    simp only [extendList]
    rw [show nv + (i + 1) = (nv + 1) + i by omega, extendList_get (Nat.lt_of_succ_lt_succ h)]
    rfl

/-- Writing at the counter extends the domain by the batch. -/
theorem Dom.extendList {a : Assignments F} {nv : Nat} (h : a.Dom nv) (xs : List F) :
    (a.extendList nv xs).Dom (nv + xs.length) := by
  intro v
  rcases Nat.lt_or_ge v nv with hlt | hge
  · rw [extendList_below hlt]
    exact iff_of_true ((h v).mpr hlt) (Nat.lt_add_right _ hlt)
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hge
    rcases Nat.lt_or_ge i xs.length with hi | hi
    · rw [extendList_get hi]
      exact iff_of_true rfl (Nat.add_lt_add_left hi _)
    · rw [extendList_above (Nat.add_le_add_left hi _)]
      exact iff_of_false
        (fun h' => absurd ((h _).mp h') (Nat.not_lt.mpr (Nat.le_add_right nv i)))
        (Nat.not_lt.mpr (Nat.add_le_add_left hi _))

/-- A slot below the counter holds its reading. -/
theorem Dom.get_eq [Zero F] {a : Assignments F} {nv v : Nat} (h : a.Dom nv) (hv : v < nv) :
    a v = some (a.get v) := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((h v).mpr hv)
  simp [get, hx]

/-- Writing at the counter only grows the table. -/
theorem Dom.le_extendList {a : Assignments F} {nv : Nat} (h : a.Dom nv) (xs : List F) :
    a.Le (a.extendList nv xs) := by
  intro v x hv
  rw [extendList_below ((h v).mp (by simp [hv]))]
  exact hv

/-- An assigned slot reads the same in any extension. -/
theorem get_of_le [Zero F] {a a' : Assignments F} (hle : a.Le a') {v : Variable}
    (hv : (a v).isSome) : a'.get v = a.get v := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hv
  simp [get, hx, hle v x hx]

end Assignments

end Snarky
