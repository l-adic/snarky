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
def sealVar [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c] (x : FVar F) :
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

/-- `sealVar.core`'s completeness law: the witnessed value reads as the operand, so its
`equal` row is satisfied at every extension of the final table; the result is scoped. -/
private theorem sealVar.core_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) (xv : F) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st x xv) (sealVar.core (c := c) x)
      (fun a st' => CircuitType.ReadsAs (val := F) st' a xv) := by
  intro st hx
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar] at hx ⊢
  obtain ⟨hx, hvx⟩ := hx
  subst hvx
  simp only [sealVar.core]
  obtain ⟨r, st₁, hrun, hsat, hnv, hle, hscope, hreads⟩ :=
    witness_complete (c := c) (readVar (val := F) x) (st := st) (v := x.val st.env.get)
      (by simp [hx])
  have hr : r.Scoped st₁ := CircuitType.scoped_fvar.mp hscope
  have hval : r.val st₁.env.get = x.val st.env.get := (CircuitType.reads_iff.mp hreads).2
  obtain ⟨_, st₂, hrun₂, hsat₂, -⟩ :=
    assertEqual_complete (c := c) x r (x.val st.env.get) st₁
      ⟨⟨CircuitType.scoped_fvar.mpr (hx.mono hnv),
          CircuitType.reads_fvar.mpr (CVar.val_of_le hle hx)⟩,
        ⟨CircuitType.scoped_fvar.mpr hr, CircuitType.reads_fvar.mpr hval⟩⟩
  exact ⟨r, st₂, hrun.bind (hrun₂.bind rfl), fun hnv' hle' =>
    Sat.bind hrun (hsat (hrun₂.nv_le.trans hnv') (hrun₂.le.trans hle'))
      (Sat.bind hrun₂ (hsat₂ hnv' hle') Sat.pure), hr.mono hrun₂.nv_le,
    by rw [CVar.val_of_le hrun₂.le hr, hval]⟩

/-- `sealVar`'s completeness law: the pass-through arms allocate nothing and stay within
the operand's variables; the witnessing arm is `sealVar.core`'s. -/
theorem sealVar_complete [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x : FVar F) (xv : F) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st x xv) (sealVar (c := c) x)
      (fun a st' => CircuitType.ReadsAs (val := F) st' a xv) := by
  intro st hx
  have hx' := hx
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar] at hx'
  obtain ⟨hxs, hvx⟩ := hx'
  subst hvx
  have hred := CVar.reduce_val x st.env.get
  simp only [sealVar]
  split
  · next v k heq =>
    rw [heq] at hred
    split
    · subst ‹k = 1›
      have hv := CVar.ScopedBy.reduce hxs (v, 1) (by rw [heq]; exact List.mem_singleton_self _)
      refine ⟨_, st, rfl, by simp [Sat, build], ?_⟩
      simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]
      exact ⟨(CVar.scoped_var ..).mpr hv, by simpa [AffineExpression.val] using hred⟩
    · exact sealVar.core_complete x _ st hx
  · next k heq =>
    rw [heq] at hred
    refine ⟨_, st, rfl, by simp [Sat, build], ?_⟩
    simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]
    exact ⟨trivial, by simpa [AffineExpression.val] using hred⟩
  · exact sealVar.core_complete x _ st hx

attribute [irreducible] sealVar sealVar.core

/-- The rows the witnessing branch emits: one `equal` against the fresh variable. -/
example [Field F] [DecidableEq F] [BasicSystem F c] (x : FVar F) (nv : Nat) :
    build (sealVar.core (c := c) x) nv =
      ⟨.var nv, nv + 1, [BasicSystem.equal (c := c) x (.var nv)]⟩ := by
  unfold sealVar.core assertEqual
  cases x <;> rfl

/-- The pass-through arms emit no rows. -/
example [Field F] [DecidableEq F] [BasicSystem F c] (x : FVar F) (nv : Nat)
    (h : x.reduceToAffineExpression = ⟨none, [(v, 1)]⟩ ∨
      x.reduceToAffineExpression = ⟨some k, []⟩) :
    (build (sealVar (c := c) x) nv).constraints = [] := by
  unfold sealVar
  rcases h with h | h <;> rw [h] <;> simp [build]

end Snarky
