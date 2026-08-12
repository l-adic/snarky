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
branch by its `equal` row through the lawful backend), and the honest run succeeds
with the sealed result reading as the operand's value.
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

/-- The honest `sealCore` run: the prover succeeds, assigning the value at `nv`. -/
private theorem sealCore_run [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {x : FVar F} {nv : Nat} {env : Assignments F} {xv : F}
    (hx : x.eval env = .ok xv) (hfresh : env.FreshFrom nv) :
    prove Basic.holds (sealCore (c := Basic F) x) nv env
      = .ok ⟨.var nv, nv + 1, env.extend nv xv⟩ := by
  have hnv : env nv = none := hfresh nv (Nat.le_refl nv)
  have hle : env.Le (env.extend nv xv) := by
    intro v w hv
    simp only [Assignments.extend]
    split
    · next h => rw [h, hnv] at hv; cases hv
    · exact hv
  have hw : AsProver.readCVar x env = .ok xv := by
    simpa [AsProver.readCVar] using hx
  have hch : Basic.holds (.equal x (.var nv)) (env.extend nv xv) = true := by
    simp [Basic.holds, CVar.eval, CVar.eval_le hle hx, Assignments.extend]
  have hcore := prove_witnessCore (mk := fun z => Basic.equal x z) hw hfresh hch
  cases x <;> exact hcore

open Std.Do

/-- Sealing pins the result to the operand: the pass-through branches carry the value
by the affine-form reading, the witnessing branch by its `equal` row. -/
@[spec] theorem sealVar_spec {F c : Type} [CommSemiring F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x : FVar F) (Q : PostCond (FVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F) => r.val V = x.val V) Q⦄
    sealVar (c := c) x
    ⦃Q⦄ := by
  intro s hpre
  obtain ⟨V, nv⟩ := s
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
      refine hpre (.var v) _ ?_
      injection henv with ha
      show V v = x.val V
      rw [hval, ← ha]
      simp
    · intro hsat
      rw [build_sealCore] at hsat ⊢
      have h := LawfulBasicSystem.holds_equal V x (.var nv)
        (hsat _ (List.mem_cons_self ..))
      exact hpre (.var nv) _ h.symm
  · next k heq =>
    rw [heq, AffineExpression.eval_nil] at hred
    injection hred with hk
    intro _
    refine hpre (.const k) _ ?_
    simpa using hk
  · intro hsat
    rw [build_sealCore] at hsat ⊢
    have h := LawfulBasicSystem.holds_equal V x (.var nv)
      (hsat _ (List.mem_cons_self ..))
    exact hpre (.var nv) _ h.symm

/-- The honest run succeeds on an evaluable operand; the sealed result reads as the
operand's value in the final table. -/
@[spec] theorem sealVar_complete_spec {F : Type} [CommSemiring F] [DecidableEq F]
    (x : FVar F)
    (Q : PostCond (FVar F) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (x.eval env).isOk)
        (fun env r env' => ∀ xv, x.eval env = .ok xv → r.eval env' = .ok xv) Q⦄
    sealVar (c := ProverC F) x
    ⦃Q⦄ := by
  intro st hpre
  rw [show (sealVar (c := ProverC F) x : CircuitM F (ProverC F) _)
      = (sealVar (c := Basic F) x : CircuitM F (Basic F) _) from rfl]
  obtain ⟨hokx, hk⟩ := hpre
  obtain ⟨xv, hx⟩ := CVar.evalOk hokx
  have hred := CVar.reduce_eval hx
  have hval : ∀ {r : FVar F} {env' : Assignments F}, r.eval env' = .ok xv →
      ∀ x', x.eval st.env = .ok x' → r.eval env' = .ok x' := by
    intro r env' heval x' hx'
    rw [hx] at hx'
    injection hx' with hx'
    exact hx' ▸ heval
  simp only [sealVar]
  split
  · next v k heq =>
    rw [heq] at hred
    split_ifs with h1
    · subst h1
      obtain ⟨a, σ, henv, hnil, hval'⟩ := AffineExpression.eval_none_cons.mp hred
      cases (AffineExpression.eval_nil (env := st.env)).symm.trans hnil
      simp only [wp, PredTrans.apply, prove]
      intro hf
      refine hk (.var v) ⟨st.nv, st.env, hf⟩ (hval ?_) (Assignments.Le.refl st.env)
      show (CVar.var v).eval st.env = _
      simp only [CVar.eval, henv, hval']
      norm_num
    · simp only [wp, PredTrans.apply]
      rw [sealCore_run hx st.fresh]
      intro hf
      refine hk _ ⟨_, _, hf⟩ (hval ?_) (Assignments.le_extend_self st.fresh _)
      show (CVar.var st.nv).eval _ = _
      simp [circuitVal]
  · next k heq =>
    rw [heq, AffineExpression.eval_nil] at hred
    injection hred with hk'
    simp only [wp, PredTrans.apply, prove]
    intro hf
    refine hk (.const k) ⟨st.nv, st.env, hf⟩ (hval ?_) (Assignments.Le.refl st.env)
    show Except.ok k = _
    rw [← hk']
    simp
  · simp only [wp, PredTrans.apply]
    rw [sealCore_run hx st.fresh]
    intro hf
    refine hk _ ⟨_, _, hf⟩ (hval ?_) (Assignments.le_extend_self st.fresh _)
    show (CVar.var st.nv).eval _ = _
    simp [circuitVal]

end Snarky
