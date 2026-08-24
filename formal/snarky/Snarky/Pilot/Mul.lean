import Snarky.Pilot.Vocab

/-!
# Pilot: `mul`

Field arithmetic with three folds and a field witness.
-/

namespace Snarky.Pilot

open Snarky Std.Do

variable {F c : Type}

/-- PS's constant folding for `mul`: constants multiply out, a constant scales. -/
def mulFold [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] (x y : FVar F) : Option (FVar F) :=
  match x, y with
  | .const a, .const b => some (.const (a * b))
  | .const a, y => some (CVar.scale_ a y)
  | x, .const b => some (CVar.scale_ b x)
  | _, _ => none

private def mulWit [Add F] [Mul F] (x y : FVar F) : AsProver F F := do
  let xv ← AsProver.readCVar x
  let yv ← AsProver.readCVar y
  pure (xv * yv)

private def mulCore [Add F] [Mul F] [BasicSystem F c] (x y : FVar F) : CircuitM F c (FVar F) := do
  let z ← witness (val := F) (mulWit x y)
  addConstraint (BasicSystem.r1cs x y z)
  pure z

/-- `mul`: the fold's answer, else the witnessing core. -/
def mul [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) :
    CircuitM F c (FVar F) :=
  match mulFold x y with
  | some r => pure r
  | none => mulCore x y

/-- The pilot gadget is the deployed one. -/
theorem mul_eq [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
    (x y : FVar F) : mul (c := c) x y = Snarky.mul x y := by
  unfold mul mulFold Snarky.mul
  cases x <;> cases y <;> rfl

/-! ## The fold's two laws -/

/-- The fold's answer reads as the product. -/
theorem mulFold_val [CommMonoidWithZero F] [Add F] [DecidableEq F] {V : Valuation F}
    {x y r : FVar F} (h : mulFold x y = some r) : r.val V = x.val V * y.val V := by
  revert h
  unfold mulFold
  cases x <;> cases y <;> intro h <;> cases h <;> simp [CVar.val, CVar.val_scale_, mul_comm]

/-- The fold's answer is in scope when the operands are. -/
theorem mulFold_scoped [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] {st : ProverState F}
    {x y r : FVar F} (h : mulFold x y = some r) (hx : x.Scoped st) (hy : y.Scoped st) :
    r.Scoped st := by
  revert h
  unfold mulFold
  cases x <;> cases y <;> intro h <;> cases h <;>
    first | trivial | exact CVar.Scoped.scale_ _ hy | exact CVar.Scoped.scale_ _ hx

/-! ## Soundness -/

/-- The core's row pins the product. -/
private theorem mulCore_spec {V : Valuation F} [Add F] [CommMonoidWithZero F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :
    ⦃⌜True⌝⦄
    mulCore (c := Builder V c) x y
    ⦃⇓ r _ => ⌜r.val V = x.val V * y.val V⌝⦄ := by
  intro nv _ hsat
  exact (LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))).symm

/-- `mul`: the result reads as the product. -/
@[spec] theorem mul_spec {V : Valuation F} [Add F] [CommMonoidWithZero F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :
    ⦃⌜True⌝⦄
    mul (c := Builder V c) x y
    ⦃⇓ r _ => ⌜r.val V = x.val V * y.val V⌝⦄ := by
  unfold mul
  cases h : mulFold x y
  · exact mulCore_spec x y
  · exact fun _ _ _ => mulFold_val h

/-! ## Completeness -/

/-- The core's run: the product, allocated. -/
private def mulCoreRun [Add F] [Mul F] [Zero F] (st : ProverState F) (x y : FVar F) :
    ProverState F × FVar F :=
  (st.extendMany [x.val st.env.toValuation * y.val st.env.toValuation], .var st.nv)

/-- `mul`'s run: the fold's answer at the same state, else the core's run. -/
def mulRun [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] (st : ProverState F) (x y : FVar F) :
    ProverState F × FVar F :=
  match mulFold x y with
  | some r => (st, r)
  | none => mulCoreRun st x y

/-- The core's run: the row accepted, the slot reading the product. -/
private theorem mulCore_facts [Add F] [CommMonoidWithZero F] [DecidableEq F] [BasicSystem F c]
    [Checker F c] [LawfulChecker F c] {x y : FVar F} (st : ProverState F) (hx : x.Scoped st)
    (hy : y.Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (mulCore (c := c) x y) st.nv st.env
        = .ok ((mulCoreRun st x y).1.out (mulCoreRun st x y).2) ∧
      Grants F st (mulCoreRun st x y) (x.val st.env.toValuation * y.val st.env.toValuation) := by
  have hle := st.le_extendMany [x.val st.env.toValuation * y.val st.env.toValuation]
  have hr : (CVar.var st.nv).val
      (st.extendMany [x.val st.env.toValuation * y.val st.env.toValuation]).env.toValuation
      = x.val st.env.toValuation * y.val st.env.toValuation := by
    simp [CVar.val]
  refine ⟨?_, Grants.fvar hle (ProverState.mem_extendMany_head ..) hr⟩
  simp only [mulCore, mulCoreRun, prove_bind]
  rw [prove_witnessF_run st (v := x.val st.env.toValuation * y.val st.env.toValuation)
    (by simp only [mulWit, AsProver.bind_eq]; scoped_wit) (by simp [mulWit, Except.bind])]
  simp only [Except.bind]
  rw [prove_addConstraint _ (LawfulChecker.holds_r1cs (by recall) (by recall) (by recall)
    (by simp [CVar.val, CVar.val_at (rfl : x.val _ = _) hle hx,
      CVar.val_at (rfl : y.val _ = _) hle hy]))]
  rfl

/-- `mul`'s run: accepted, landing at `mulRun`, reading the product. -/
theorem mul_facts [Add F] [CommMonoidWithZero F] [DecidableEq F] [BasicSystem F c]
    [Checker F c] [LawfulChecker F c] {x y : FVar F} (st : ProverState F) (hx : x.Scoped st)
    (hy : y.Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (mul (c := c) x y) st.nv st.env
        = .ok ((mulRun st x y).1.out (mulRun st x y).2) ∧
      Grants F st (mulRun st x y) (x.val st.env.toValuation * y.val st.env.toValuation) := by
  unfold mul mulRun
  cases h : mulFold x y
  · exact mulCore_facts st hx hy
  · exact ⟨rfl, Grants.fvar (Assignments.Le.refl _) (mulFold_scoped h hx hy) (mulFold_val h)⟩

end Snarky.Pilot
