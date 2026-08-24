import Snarky.Pilot.Vocab

/-!
# Pilot: `select`

Three operands, two folds (a constant selector; two constant branches), one core.
-/

namespace Snarky.Pilot

open Snarky Std.Do

variable {F c : Type}

/-- PS's constant folding for `select`: a constant selector picks; two constant branches
fold to the affine mux. -/
def selectFold [Field F] [DecidableEq F] (b : BoolVar F) (t e : FVar F) : Option (FVar F) :=
  match (↑b : CVar F) with
  | .const bv => some (if bv = 1 then t else e)
  | _ =>
    match t, e with
    | .const tv, .const ev =>
      some (CVar.add_ (.scale tv ↑b) (CVar.scale_ ev (CVar.sub_ (.const 1) ↑b)))
    | _, _ => none

private def selectWit [Field F] [DecidableEq F] (b : BoolVar F) (t e : FVar F) :
    AsProver F F := do
  let bv ← AsProver.readCVar ↑b
  if bv = 1 then AsProver.readCVar t else AsProver.readCVar e

private def selectCore [Field F] [DecidableEq F] [BasicSystem F c] (b : BoolVar F)
    (t e : FVar F) : CircuitM F c (FVar F) := do
  let r ← witness (val := F) (selectWit b t e)
  addConstraint (BasicSystem.r1cs ↑b (CVar.sub_ t e) (CVar.sub_ r e))
  pure r

/-- `select`: the fold's answer, else the witnessing core. -/
def select [Field F] [DecidableEq F] [BasicSystem F c] (b : BoolVar F) (t e : FVar F) :
    CircuitM F c (FVar F) :=
  match selectFold b t e with
  | some r => pure r
  | none => selectCore b t e

/-- The pilot gadget is the deployed one. -/
theorem select_eq [Field F] [DecidableEq F] [BasicSystem F c] (b : BoolVar F) (t e : FVar F) :
    select (c := c) b t e = Snarky.select b t e := by
  unfold select selectFold
  delta Snarky.select instIfThenElseFVarOfFieldOfDecidableEqOfBasicSystem
  dsimp only
  cases (↑b : CVar F) <;> (try simp only []) <;> (try (cases t <;> cases e)) <;>
    (try simp only []) <;> rfl

/-! ## The fold's two laws -/

/-- The fold's answer reads as the chosen branch. -/
theorem selectFold_val [Field F] [DecidableEq F] {V : Valuation F} {b : BoolVar F}
    {t e r : FVar F} {bb : Bool} (h : selectFold b t e = some r)
    (hbv : (↑b : CVar F).val V = bit bb) : r.val V = selectPure bb (t.val V) (e.val V) := by
  revert h hbv
  unfold selectFold
  cases hB : (↑b : CVar F) <;> (try simp only []) <;> (try (cases t <;> cases e)) <;>
    (try simp only []) <;> intro h hbv <;> cases h <;> cases bb <;>
    simp only [CVar.val, CVar.val_add_, CVar.val_scale_, CVar.val_sub_, bit, selectPure]
      at hbv ⊢ <;> (try rw [hbv]) <;> simp [CVar.val]

/-- The fold's answer is in scope when the operands are. -/
theorem selectFold_scoped [Field F] [DecidableEq F] {st : ProverState F} {b : BoolVar F}
    {t e r : FVar F} (h : selectFold b t e = some r) (hb : (↑b : CVar F).Scoped st)
    (ht : t.Scoped st) (he : e.Scoped st) : r.Scoped st := by
  revert h
  unfold selectFold
  cases hB : (↑b : CVar F) <;> (try simp only []) <;> (try (cases t <;> cases e)) <;>
    (try simp only []) <;> intro h <;> cases h <;>
    first
    | (split <;> assumption)
    | exact CVar.Scoped.add_ (hB ▸ hb) (CVar.Scoped.scale_ _ (CVar.Scoped.sub_ trivial (hB ▸ hb)))

/-! ## Soundness -/

/-- The core's row pins the choice. -/
private theorem selectCore_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (b : BoolVar F)
    (t e : FVar F) :
    ⦃⌜True⌝⦄
    selectCore (c := Builder V c) b t e
    ⦃⇓ r _ => ⌜∀ bb : Bool, (↑b : CVar F).val V = bit bb →
        r.val V = selectPure bb (t.val V) (e.val V)⌝⦄ := by
  intro nv _ hsat bb hbv
  have h := LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))
  simp only [circuitVal] at h
  rw [hbv] at h
  exact (sub_eq_iff_eq_add.mp h.symm).trans (by cases bb <;> simp [bit, selectPure])

/-- `select`: on a bit selector the result reads as the chosen branch. -/
@[spec] theorem select_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (b : BoolVar F)
    (t e : FVar F) :
    ⦃⌜True⌝⦄
    select (c := Builder V c) b t e
    ⦃⇓ r _ => ⌜∀ bb : Bool, (↑b : CVar F).val V = bit bb →
        r.val V = selectPure bb (t.val V) (e.val V)⌝⦄ := by
  unfold select
  cases h : selectFold b t e
  · exact selectCore_spec b t e
  · exact fun _ _ _ bb hbv => selectFold_val h hbv

/-! ## Completeness -/

/-- The core's run: the chosen value, allocated. -/
private def selectCoreRun [Field F] [DecidableEq F] (st : ProverState F) (b : BoolVar F)
    (t e : FVar F) : ProverState F × FVar F :=
  (st.extendMany [if (↑b : CVar F).val st.env.toValuation = 1 then t.val st.env.toValuation
      else e.val st.env.toValuation],
    .var st.nv)

/-- `select`'s run: the fold's answer at the same state, else the core's run. -/
def selectRun [Field F] [DecidableEq F] (st : ProverState F) (b : BoolVar F) (t e : FVar F) :
    ProverState F × FVar F :=
  match selectFold b t e with
  | some r => (st, r)
  | none => selectCoreRun st b t e

/-- The core's run on a bit selector: the row accepted, the slot reading the choice. -/
private theorem selectCore_facts [Field F] [DecidableEq F] [BasicSystem F c] [Checker F c]
    [LawfulChecker F c] {b : BoolVar F} {t e : FVar F} {bb : Bool} (st : ProverState F)
    (hb : (↑b : CVar F).Scoped st) (ht : t.Scoped st) (he : e.Scoped st)
    (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    prove (Checker.holds (F := F) (c := c)) (selectCore (c := c) b t e) st.nv st.env
        = .ok ((selectCoreRun st b t e).1.out (selectCoreRun st b t e).2) ∧
      Grants F st (selectCoreRun st b t e)
        (selectPure bb (t.val st.env.toValuation) (e.val st.env.toValuation)) := by
  have hle := st.le_extendMany [if (↑b : CVar F).val st.env.toValuation = 1
    then t.val st.env.toValuation else e.val st.env.toValuation]
  have hr : (CVar.var st.nv).val (st.extendMany [if (↑b : CVar F).val st.env.toValuation = 1
      then t.val st.env.toValuation else e.val st.env.toValuation]).env.toValuation
      = selectPure bb (t.val st.env.toValuation) (e.val st.env.toValuation) := by
    simp only [CVar.val, ProverState.get_extendMany_head, hbv, selectPure]
    cases bb <;> simp [bit]
  refine ⟨?_, Grants.fvar hle (ProverState.mem_extendMany_head ..) hr⟩
  simp only [selectCore, selectCoreRun, prove_bind]
  rw [prove_witnessF_run st (v := if (↑b : CVar F).val st.env.toValuation = 1
      then t.val st.env.toValuation else e.val st.env.toValuation)
    (by simp only [selectWit, AsProver.bind_eq]; scoped_wit)
    (by simp only [selectWit, AsProver.bind_eq, AsProver.eval_bind, AsProver.eval_readCVar,
          Except.bind]
        split_ifs <;> simp)]
  simp only [Except.bind]
  rw [prove_addConstraint _ (LawfulChecker.holds_r1cs (by recall) (by recall) (by recall)
    (by simp only [CVar.val_sub_, CVar.val_at hbv hle hb, CVar.val_at (rfl : t.val _ = _) hle ht,
          CVar.val_at (rfl : e.val _ = _) hle he, hr]
        cases bb <;> simp [bit, selectPure]))]
  rfl

/-- `select`'s run on a bit selector: accepted, landing at `selectRun`, reading the choice. -/
theorem select_facts [Field F] [DecidableEq F] [BasicSystem F c] [Checker F c]
    [LawfulChecker F c] {b : BoolVar F} {t e : FVar F} {bb : Bool} (st : ProverState F)
    (hb : (↑b : CVar F).Scoped st) (ht : t.Scoped st) (he : e.Scoped st)
    (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    prove (Checker.holds (F := F) (c := c)) (select (c := c) b t e) st.nv st.env
        = .ok ((selectRun st b t e).1.out (selectRun st b t e).2) ∧
      Grants F st (selectRun st b t e)
        (selectPure bb (t.val st.env.toValuation) (e.val st.env.toValuation)) := by
  unfold select selectRun
  cases h : selectFold b t e
  · exact selectCore_facts st hb ht he hbv
  · exact ⟨rfl, Grants.fvar (Assignments.Le.refl _) (selectFold_scoped h hb ht he)
      (selectFold_val h hbv)⟩

theorem select_run [Field F] [DecidableEq F] [BasicSystem F c] [Checker F c]
    [LawfulChecker F c] {b : BoolVar F} {t e : FVar F} {bb : Bool} (st : ProverState F)
    (hb : (↑b : CVar F).Scoped st) (ht : t.Scoped st) (he : e.Scoped st)
    (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    prove (Checker.holds (F := F) (c := c)) (select (c := c) b t e) st.nv st.env
      = .ok ((selectRun st b t e).1.out (selectRun st b t e).2) :=
  (select_facts st hb ht he hbv).1

theorem selectRun_grants [Field F] [DecidableEq F] {st : ProverState F} {b : BoolVar F}
    {t e : FVar F} {bb : Bool} (hb : (↑b : CVar F).Scoped st) (ht : t.Scoped st)
    (he : e.Scoped st) (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    Grants F st (selectRun st b t e)
      (selectPure bb (t.val st.env.toValuation) (e.val st.env.toValuation)) :=
  (select_facts (c := Basic F) st hb ht he hbv).2

end Snarky.Pilot
