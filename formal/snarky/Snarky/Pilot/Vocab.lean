import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.Boolean
import Snarky.Circuit.DSL.Assert

/-!
# Pilot: the completeness vocabulary

What a run-equation proof needs and nothing else: transport of scope, growth and readings
to a later state (by search, `recall`), the witness leaf at each encoding with its
allocation written out, and grants stated at the readings a consumer names.
-/

namespace Snarky

variable {F c : Type}

/-! ## Transport -/

/-- Scope, at a later state. The scope fact comes first so it fixes the origin state. -/
theorem CVar.Scoped.at {st st' : ProverState F} {x : CVar F} (h : x.Scoped st)
    (hle : st.env.Le st'.env) : x.Scoped st' :=
  h.of_le hle

/-- A reading, at a later state. The reading comes first so it fixes the origin state. -/
theorem CVar.val_at [Add F] [Mul F] [Zero F] {st st' : ProverState F} {x : CVar F} {v : F}
    (hv : x.val st.env.toValuation = v) (hle : st.env.Le st'.env) (hs : x.Scoped st) :
    x.val st'.env.toValuation = v :=
  (CVar.val_of_le hle hs).trans hv

/-- A conditional witness block is scoped when both branches are. -/
theorem AsProver.Scoped.ite {α : Type} {st : ProverState F} {p : Prop} [Decidable p]
    {a b : AsProver F α} (ha : a.Scoped st) (hb : b.Scoped st) :
    (if p then a else b).Scoped st := by
  split <;> assumption

/-- Growth between two states: the per-step growth facts, chained. -/
macro "le_chain" : tactic =>
  `(tactic| solve_by_elim (config := { maxDepth := 64 }) only
      [*, ProverState.le_extendMany, Grants.le, Assignments.Le.trans, Assignments.Le.refl])

/-- Scope, growth and readings at any state: the structural and origin facts first, the
transport to a later state last. -/
macro "recall" : tactic =>
  `(tactic| solve_by_elim (config := { maxDepth := 40 })
      [CVar.scoped_const, CVar.Scoped.add_, CVar.Scoped.sub_, CVar.Scoped.scale_, not_scoped,
       ProverState.mem_extendMany_head, Grants.fvar_scoped, Grants.fvar_val,
       ProverState.le_extendMany, Grants.le, Assignments.Le.trans, Assignments.Le.refl,
       CVar.Scoped.at, CVar.val_at])

/-- A witness block's scope, by search over its structure. -/
macro "scoped_wit" : tactic =>
  `(tactic| solve_by_elim (config := { maxDepth := 12 })
      [AsProver.Scoped.bind, AsProver.Scoped.readCVar, AsProver.scoped_pure,
       AsProver.scoped_fail, AsProver.Scoped.ite, CVar.scoped_const, CVar.Scoped.add_,
       CVar.Scoped.sub_, CVar.Scoped.scale_, not_scoped, Grants.fvar_scoped,
       ProverState.mem_extendMany_head, ProverState.le_extendMany, Grants.le,
       Assignments.Le.refl, Assignments.Le.trans, CVar.Scoped.at])

/-! ## The witness leaves, by encoding -/

/-- A field witness: the value at the counter. -/
theorem prove_witnessF_run [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
    [Checker F c] [LawfulChecker F c] {w : AsProver F F} (st : ProverState F) (hs : w.Scoped st)
    {v : F} (hv : w.eval st.env.toValuation = .ok v) :
    prove (Checker.holds (F := F) (c := c)) (witness (val := F) w) st.nv st.env
      = .ok ((st.extendMany [v]).out (.var st.nv)) := by
  rw [prove_witness_run st hs hv]
  rfl

/-- An unchecked bit witness: the bit at the counter, retagged. -/
theorem prove_witnessUB_run [Field F] [DecidableEq F] [BasicSystem F c]
    [Checker F c] [LawfulChecker F c] {w : AsProver F (UnChecked Bool)} (st : ProverState F)
    (hs : w.Scoped st) {b : Bool} (hv : w.eval st.env.toValuation = .ok ⟨b⟩) :
    prove (Checker.holds (F := F) (c := c)) (witness (val := UnChecked Bool) w) st.nv st.env
      = .ok ((st.extendMany [bit b]).out ⟨.unchecked (.var st.nv)⟩) := by
  rw [prove_witness_run st hs hv]
  rfl

/-- A checked bit witness: the bit at the counter, its `boolean` row accepted. -/
theorem prove_witnessB_run [Field F] [DecidableEq F] [BasicSystem F c]
    [Checker F c] [LawfulChecker F c] {w : AsProver F Bool} (st : ProverState F)
    (hs : w.Scoped st) {b : Bool} (hv : w.eval st.env.toValuation = .ok b) :
    prove (Checker.holds (F := F) (c := c)) (witness (val := Bool) w) st.nv st.env
      = .ok ((st.extendMany [bit b]).out (.unchecked (.var st.nv))) := by
  rw [prove_witness_run st hs hv]
  rfl

/-! ## Grants at named readings -/

/-- A grant, its value renamed. -/
theorem Grants.cast [Add F] [Mul F] [Zero F] {val var : Type} [CircuitType F val var]
    {st : ProverState F} {p : ProverState F × var} {v v' : val} (g : Grants val st p v)
    (h : v = v') : Grants val st p v' :=
  h ▸ g

/-- `mulRun` at named operand readings. -/
theorem mulRun_grants' [Add F] [CommMonoidWithZero F] [DecidableEq F] {st : ProverState F}
    {x y : FVar F} {a b : F} (hx : x.Scoped st) (hy : y.Scoped st)
    (hxv : x.val st.env.toValuation = a) (hyv : y.val st.env.toValuation = b) :
    Grants F st (mulRun st x y) (a * b) :=
  (mulRun_grants hx hy).cast (by simp only [hxv, hyv])

/-- `invRun` at a named operand reading. -/
theorem invRun_grants' [Field F] [DecidableEq F] {st : ProverState F} {x : FVar F} {a : F}
    (hx : x.Scoped st) (hxv : x.val st.env.toValuation = a) :
    Grants F st (invRun st x) a⁻¹ :=
  (invRun_grants hx).cast (by simp only [hxv])

/-- `divRun` at named operand readings. -/
theorem divRun_grants' [Field F] [DecidableEq F] {st : ProverState F} {x y : FVar F} {a b : F}
    (hx : x.Scoped st) (hy : y.Scoped st) (hxv : x.val st.env.toValuation = a)
    (hyv : y.val st.env.toValuation = b) : Grants F st (divRun st x y) (a / b) :=
  (divRun_grants hx hy).cast (by simp only [hxv, hyv])

/-- `squareRun` at a named operand reading. -/
theorem squareRun_grants' [Add F] [Mul F] [Zero F] {st : ProverState F} {x : FVar F} {a : F}
    (hx : x.Scoped st) (hxv : x.val st.env.toValuation = a) :
    Grants F st (squareRun st x) (a * a) :=
  (squareRun_grants hx).cast (by simp only [hxv])

/-- `selectRun` at named operand readings. -/
theorem selectRun_grants' [Field F] [DecidableEq F] {st : ProverState F} {b : BoolVar F}
    {t e : FVar F} {bb : Bool} {tv ev : F} (hb : (↑b : CVar F).Scoped st) (ht : t.Scoped st)
    (he : e.Scoped st) (hbv : (↑b : CVar F).val st.env.toValuation = bit bb)
    (htv : t.val st.env.toValuation = tv) (hev : e.val st.env.toValuation = ev) :
    Grants F st (selectRun st b t e) (selectPure bb tv ev) :=
  (selectRun_grants hb ht he hbv).cast (by simp only [htv, hev])

end Snarky
