import Snarky.Circuit.DSL.Assert
import Snarky.Backend.WP

/-!
# Sealing an expression to a single variable

Port of `Snarky.Circuit.DSL.Utils` (packages/snarky/src/Snarky/Circuit/DSL/Utils.purs):
`seal` reduces an expression to something that will not
expand under further operations — a lone unit-coefficient variable or a lone constant
passes through; anything else is witnessed into a fresh variable pinned by one `equal`
constraint.

Name map: `seal` becomes `sealVar` — `seal` is Lean's irreducibility command token,
unusable as a definition name (the `exists` → `witness` precedent); the witnessing
branch stays the named helper `sealCore` (the `mulCore`/`invCore` manner).

The laws are the spec pair: any satisfying assignment pins the sealed result to the
operand's value (the pass-through branches by the affine-form reading, the witnessing
branch by its `equal` row through the lawful backend), and the honest run lands at
`sealRun`, whose result reads as the operand's value.
-/

namespace Snarky

variable {F c : Type u}

/-- `seal`'s witnessing branch: witness the expression's value into a fresh variable
and pin it with one `equal` constraint. Split out as a named unit
uniformly. -/
private def sealCore [Add F] [Mul F] [DecidableEq F] [BasicSystem F c] (x : FVar F) :
    CircuitM F c (FVar F) := do
  let y ← witness (val := F) (AsProver.readCVar x)
  assertEqual x y
  pure y

/-- Reduce an expression to a single variable if it is complex (PS `seal`; see the
name map above): a lone
unit-coefficient variable or a lone constant (under `CVar.reduceToAffineExpression`)
passes through unchanged; otherwise the value is witnessed into a fresh variable
constrained equal to the expression. -/
def sealVar [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
    (x : FVar F) : CircuitM F c (FVar F) :=
  match x.reduceToAffineExpression with
  | ⟨none, [(v, k)]⟩ => if k = 1 then pure (.var v) else sealCore x
  | ⟨some k, []⟩ => pure (.const k)
  | _ => sealCore x

/-! ## The laws -/

/-- The built form of the witnessing branch: one fresh variable, one `equal` row. -/
private theorem build_sealCore [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [BasicSystem F c] (x : FVar F) (nv : Nat) :
    build (sealCore (c := c) x) nv =
      ⟨.var nv, nv + 1, [BasicSystem.equal (c := c) x (.var nv)]⟩ := by
  cases x <;> rfl

open Std.Do

/-- Sealing pins the result to the operand: the pass-through branches carry the value
by the affine-form reading, the witnessing branch by its `equal` row. -/
@[spec] theorem sealVar_spec {F c : Type} {V : Valuation F} [CommSemiring F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x : FVar F) :
    ⦃⌜True⌝⦄
    sealVar (c := Builder V c) x
    ⦃⇓ r _ => ⌜r.val V = x.val V⌝⦄ := by
  intro nv _
  have hred := CVar.reduce_eval (CVar.eval_toAssignments x V)
  simp only [sealVar]
  split
  · next v k heq =>
    rw [heq] at hred
    split_ifs with h1
    · subst h1
      obtain ⟨a, σ, henv, hnil, hval⟩ := AffineExpression.eval_none_cons.mp hred
      cases (AffineExpression.eval_nil (env := V.toAssignments)).symm.trans hnil
      intro _
      injection henv with ha
      show V v = x.val V
      rw [hval, ← ha]
      simp
    · intro hsat
      rw [build_sealCore] at hsat ⊢
      have h := LawfulBasicSystem.holds_equal V x (.var nv)
        (hsat _ (List.mem_cons_self ..))
      exact h.symm
  · next k heq =>
    rw [heq, AffineExpression.eval_nil] at hred
    injection hred with hk
    intro _
    simpa using hk
  · intro hsat
    rw [build_sealCore] at hsat ⊢
    have h := LawfulBasicSystem.holds_equal V x (.var nv)
      (hsat _ (List.mem_cons_self ..))
    exact h.symm

/-- The state and result of `sealVar`'s honest run — its `match` on the affine form:
the pass-through shapes allocate nothing; otherwise the operand's value is allocated. -/
def sealRun {F : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] (st : ProverState F)
    (x : FVar F) : ProverState F × FVar F :=
  match x.reduceToAffineExpression with
  | ⟨none, [(v, k)]⟩ =>
    if k = 1 then (st, .var v) else (st.extendMany [x.val st.env.toValuation], .var st.nv)
  | ⟨some k, []⟩ => (st, .const k)
  | _ => (st.extendMany [x.val st.env.toValuation], .var st.nv)

/-- `sealCore`'s honest run: one slot, the operand's value, its `equal` row accepted. -/
private theorem sealCore_run {F c : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {x : FVar F}
    (st : ProverState F) (hx : x.Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (sealCore (c := c) x) st.nv st.env
      = .ok ((st.extendMany [x.val st.env.toValuation]).out (.var st.nv)) := by
  have hle := st.le_extendMany [x.val st.env.toValuation]
  simp only [sealCore, prove_bind]
  rw [prove_witness_run (w := AsProver.readCVar x) st (.readCVar hx)
    (v := x.val st.env.toValuation) (by simp)]
  simp only [valueToFields_fvar_toList, fieldsToVar_fvar_alloc, Except.bind]
  rw [assertEqual_run _ (hx.of_le hle) (by simp) (by simp [CVar.val, CVar.val_of_le hle hx])]
  rfl

/-- `sealVar`'s honest run lands at `sealRun`. -/
theorem sealVar_run {F c : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {x : FVar F}
    (st : ProverState F) (hx : x.Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (sealVar (c := c) x) st.nv st.env
      = .ok ((sealRun st x).1.out (sealRun st x).2) := by
  unfold sealVar sealRun
  rcases hr : x.reduceToAffineExpression with ⟨_ | k, _ | ⟨⟨v, k'⟩, _ | ⟨p, rest⟩⟩⟩ <;>
    (try dsimp only) <;> (try split_ifs) <;> first | rfl | exact sealCore_run st hx

/-- `sealRun` reads as the operand. -/
theorem sealRun_grants {F : Type} [CommSemiring F] [DecidableEq F] {st : ProverState F}
    {x : FVar F} (hx : x.Scoped st) : Grants F st (sealRun st x) (x.val st.env.toValuation) := by
  have hred := CVar.reduce_eval (CVar.eval_eq_val hx)
  have hcore : Grants F st (st.extendMany [x.val st.env.toValuation], .var st.nv)
      (x.val st.env.toValuation) :=
    Grants.fvar (st.le_extendMany _) (by simp) (by simp [CVar.val])
  unfold sealRun
  rcases hr : x.reduceToAffineExpression with ⟨_ | k, _ | ⟨⟨v, k'⟩, _ | ⟨p, rest⟩⟩⟩ <;>
    (try dsimp only) <;> rw [hr] at hred
  case none.cons.nil =>
    split_ifs with h1
    · subst h1
      obtain ⟨a, σ, henv, hnil, hval⟩ := AffineExpression.eval_none_cons.mp hred
      cases (AffineExpression.eval_nil (env := st.env)).symm.trans hnil
      refine Grants.fvar (Assignments.Le.refl _) (ProverState.mem_of_assigned henv) ?_
      show st.env.toValuation v = _
      simp only [Assignments.toValuation, henv, Option.getD_some]
      rw [hval]
      simp
    · exact hcore
  case some.nil =>
    rw [AffineExpression.eval_nil] at hred
    injection hred with hk
    exact Grants.fvar (Assignments.Le.refl _) trivial (by simpa [CVar.val] using hk)
  all_goals exact hcore

end Snarky
