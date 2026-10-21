import Snarky.DSL.Assert

namespace Snarky

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

open Std.WP in
@[spec] private theorem sealVar.core_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) :
    ⦃fun _ => True⦄
    sealVar.core (c := Builder V c) x
    ⦃fun r _ => r.val V = x.val V⦄ := by
  simp only [sealVar.core]
  vcgen
  exact ‹_ = _›.symm

open Std.WP in
/-- Sealing pins the result to the operand: the pass-through arms by the affine reading,
the witnessing arm by its `equal` row. -/
@[spec] theorem sealVar_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) :
    ⦃fun _ => True⦄
    sealVar (c := Builder V c) x
    ⦃fun r _ => r.val V = x.val V⦄ := by
  have hred := CVar.reduce_val x V
  simp only [sealVar]
  split
  · next v k heq =>
    rw [heq] at hred
    split
    · subst ‹k = 1›
      vcgen
      simpa [AffineExpression.val] using hred
    · vcgen
  · next k heq =>
    rw [heq] at hred
    vcgen
    simpa [AffineExpression.val] using hred
  · vcgen

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

/-! ## The completeness law -/

section ProverReading

open Snarky.Prover Std.WP

/-- `sealVar`'s completeness: the pass-through arms read the operand by the affine reading, the
witnessing arm through its fresh cell and `equal` row; the result reads the operand's reading. -/
theorem Prover.sealVar_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x : FVar F) (a : F) :
    ⦃Reads x a⦄ sealVar (c := Prover c) x ⦃fun r ↦ Reads r a⦄ := by
  have hcore : ⦃Reads x a⦄ sealVar.core (c := Prover c) x ⦃fun r ↦ Reads r a⦄ := by
    have hw := Spec.witness (c := c) (readVar (val := F) x) a valid_fvar
    have he := fun y : FVar F ↦ Prover.assertEqual_spec (c := c) x y a
    unfold sealVar.core
    vcgen [hw, he]
    all_goals prover_assert with (intros; simp_all [Reads.fvar_apply])
  unfold sealVar
  split
  · next v k heq =>
    split
    · subst ‹k = 1›
      vcgen
      all_goals prover_assert with
        intro s hs
        rw [Reads.fvar_apply] at hs ⊢
        have hred := CVar.reduce_val x s.env.get
        rw [heq] at hred
        have hv := CVar.ScopedBy.reduce hs.1 (v, 1) (by rw [heq]; exact List.mem_singleton_self _)
        refine ⟨(CVar.scoped_var ..).mpr hv, ?_⟩
        show (CVar.var v).val s.env.get = a
        rw [← hs.2]
        simpa [AffineExpression.val] using hred
    · exact hcore
  · next k heq =>
    vcgen
    all_goals prover_assert with
      intro s hs
      rw [Reads.fvar_apply] at hs ⊢
      have hred := CVar.reduce_val x s.env.get
      rw [heq] at hred
      refine ⟨CVar.scoped_const _ _, ?_⟩
      show (CVar.const k).val s.env.get = a
      rw [← hs.2]
      simpa [AffineExpression.val] using hred
  · exact hcore

end ProverReading

end Snarky
