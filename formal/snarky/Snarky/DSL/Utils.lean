import Snarky.DSL.Assert

namespace Snarky

set_option mvcgen.warning false

variable {F c : Type}

/-! # Sealing

`sealVar` reduces an expression to one that does not grow under further operations: a
lone unit-coefficient variable or a lone constant, under `CVar.reduceToAffineExpression`,
passes through; anything else is witnessed into a fresh variable pinned by one `equal`
row. `seal` is a Lean token, hence the name. -/

/-- Seal an expression: pass through a lone unit-coefficient variable or a lone constant;
otherwise witness its value into a fresh variable and assert them equal. -/
def sealVar [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (x : FVar F) :
    CircuitM F c (FVar F) :=
  match x.reduceToAffineExpression with
  | ⟨none, [(v, k)]⟩ => if k = 1 then pure (.var v) else core x
  | ⟨some k, []⟩ => pure (.const k)
  | _ => core x
where
  /-- The witnessing branch: the expression's value in a fresh variable, one `equal` row. -/
  core (x : FVar F) : CircuitM F c (FVar F) := do
    let y ← witness (val := F) (readVar (val := F) x)
    assertEqual x y
    pure y

open Std.Do in
@[spec] private theorem sealVar.core_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) :
    ⦃⌜True⌝⦄
    sealVar.core (c := Builder V c) x
    ⦃⇓ r _ => ⌜r.val V = x.val V⌝⦄ := by
  simp only [sealVar.core]
  mvcgen
  exact ‹_ = _›.symm

open Std.Do in
/-- Sealing pins the result to the operand: the pass-through arms by the affine reading,
the witnessing arm by its `equal` row. -/
@[spec] theorem sealVar_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) :
    ⦃⌜True⌝⦄
    sealVar (c := Builder V c) x
    ⦃⇓ r _ => ⌜r.val V = x.val V⌝⦄ := by
  have hred := CVar.reduce_val x V
  simp only [sealVar]
  split
  · next v k heq =>
    rw [heq] at hred
    split
    · subst ‹k = 1›
      mvcgen
      simpa [AffineExpression.val] using hred
    · mvcgen
  · next k heq =>
    rw [heq] at hred
    mvcgen
    simpa [AffineExpression.val] using hred
  · mvcgen

attribute [irreducible] sealVar sealVar.core

/-- The rows the witnessing branch emits: one `equal` against the fresh variable. -/
example [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (x : FVar F) (nv : Nat) :
    build (sealVar.core (c := c) x) nv =
      ⟨.var nv, nv + 1, [BasicSystem.equal (c := c) x (.var nv)]⟩ := by
  unfold sealVar.core assertEqual
  cases x <;> rfl

/-- The pass-through arms emit no rows. -/
example [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (x : FVar F) (nv : Nat)
    (h : x.reduceToAffineExpression = ⟨none, [(v, 1)]⟩ ∨
      x.reduceToAffineExpression = ⟨some k, []⟩) :
    (build (sealVar (c := c) x) nv).constraints = [] := by
  unfold sealVar
  rcases h with h | h <;> rw [h] <;> simp [build]

/-! ## The state-relative completeness laws -/

section ProverReading

open Std.Do

/-- `readVar`'s witness at a field cell: the fresh cell reads the operand's entry reading. -/
@[spec] private def Prover.readVar_reg [Field F] [BasicSystem F c]
    [ConstraintHolds F c]
    (x : FVar F) :=
  Prover.register (Prover.witness_of_run (c := c) (readVar (val := F) x) (fun st => x.Scoped st)
    (fun st => st.read x)
    (fun _ h => by rw [readVar_run (CircuitType.scoped_fvar.mpr h), CircuitType.readVal_fvar])
    fun _ _ => by simp)

/-- `sealVar`'s completeness: the pass-through arms read the operand by the affine reading,
the witnessing arm through its fresh cell and `equal` row; the result reads the operand's
entry reading. -/
theorem Prover.sealVar_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x : FVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ x.Scoped st₀⌝⦄
    sealVar (c := Prover c) x
    ⦃⇓ r s' => ⌜r.Scoped s' ∧ s'.read r = st₀.read x ∧ st₀ ≤ s'⌝⦄ := by
  have hcore : ∀ st, ⦃fun s => ⌜s = st ∧ x.Scoped st⌝⦄ sealVar.core (c := Prover c) x
      ⦃⇓ r s' => ⌜r.Scoped s' ∧ s'.read r = st.read x ∧ st ≤ s'⌝⦄ := by
    intro st
    unfold sealVar.core
    mvcgen
    all_goals grind [Prover.Reg.iff, CircuitType.ReadsAs, CircuitType.scoped_fvar,
      CircuitType.reads_fvar, ProverState.read_of_le, CVar.Scoped.of_le]
  have hcore' := Prover.register hcore
  unfold sealVar
  split
  · next v k heq =>
    split
    · subst ‹k = 1›
      mvcgen
      rename_i s h
      obtain ⟨rfl, hxs⟩ := h
      have hred := CVar.reduce_val x s.env.get
      rw [heq] at hred
      have hv := CVar.ScopedBy.reduce hxs (v, 1) (by rw [heq]; exact List.mem_singleton_self _)
      refine ⟨(CVar.scoped_var ..).mpr hv, ?_, le_rfl⟩
      show (CVar.var v).val s.env.get = x.val s.env.get
      simpa [AffineExpression.val] using hred
    · mvcgen [hcore']
      all_goals grind [Prover.Reg.iff]
  · next k heq =>
    mvcgen
    rename_i s h
    obtain ⟨rfl, -⟩ := h
    have hred := CVar.reduce_val x s.env.get
    rw [heq] at hred
    refine ⟨CVar.scoped_const _ _, ?_, le_rfl⟩
    show (CVar.const k).val s.env.get = x.val s.env.get
    simpa [AffineExpression.val] using hred
  · mvcgen [hcore']
    all_goals grind [Prover.Reg.iff]

/-- Registered. -/
@[spec] private def Prover.sealVar_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x : FVar F) :=
  Prover.register (Prover.sealVar_spec (c := c) x)

end ProverReading

end Snarky
