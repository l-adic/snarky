import Snarky.Pilot.Vocab

/-!
# Pilot: `sqrtFlagged`

A four-leaf composite with two witness encodings: a checked bit, a `select`, a field
witness, an assertion. The readings are the consumer's vocabulary.
-/

namespace Snarky.Pilot

open Snarky

variable {F c : Type}

private def isQRWit [Field F] (sqrtF : F → Option F) (x : FVar F) : AsProver F Bool := do
  let v ← AsProver.readCVar x
  pure (sqrtF v).isSome

private def sqrtWit [Field F] (sqrtF : F → Option F) (x : FVar F) : AsProver F F := do
  let v ← AsProver.readCVar x
  pure ((sqrtF v).getD 0)

/-- In-circuit square root with a residuosity flag. -/
def sqrtFlagged [Field F] [DecidableEq F] [BasicSystem F c] (sqrtF : F → Option F)
    (nonResidue : F) (x : FVar F) : CircuitM F c (FVar F × BoolVar F) := do
  let isQR ← witness (val := Bool) (isQRWit sqrtF x)
  let mX := CVar.scale_ nonResidue x
  let xOrMx ← select isQR x mX
  let sqrtVal ← witness (val := F) (sqrtWit sqrtF xOrMx)
  assertSquare sqrtVal xOrMx
  pure (sqrtVal, isQR)

/-- The flag-selected operand. -/
def twist [Field F] (sqrtF : F → Option F) (nonResidue xv : F) : F :=
  if (sqrtF xv).isSome then xv else nonResidue * xv

/-- The run: the flag at the counter, the `select`, the root at the next counter. -/
def sqrtFlaggedRun [Field F] [DecidableEq F] (sqrtF : F → Option F) (nonResidue : F)
    (st : ProverState F) (x : FVar F) : ProverState F × (FVar F × BoolVar F) :=
  let st₁ := st.extendMany [bit (sqrtF (x.val st.env.toValuation)).isSome]
  let r := selectRun st₁ (.unchecked (.var st.nv)) x (CVar.scale_ nonResidue x)
  (r.1.extendMany [(sqrtF (twist sqrtF nonResidue (x.val st.env.toValuation))).getD 0],
    (.var r.1.nv, .unchecked (.var st.nv)))

/-- The run on an in-scope operand, when roots are genuine and a rootless operand's twist
has a root: accepted, landing at `sqrtFlaggedRun`, the root and flag in scope reading the
advice's root of the twist and the operand's residuosity. -/
theorem sqrtFlagged_facts [Field F] [DecidableEq F] [BasicSystem F c] [Checker F c]
    [LawfulChecker F c] (sqrtF : F → Option F) (nonResidue : F) {x : FVar F}
    (st : ProverState F) (hx : x.Scoped st)
    (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : sqrtF (x.val st.env.toValuation) = none →
      (sqrtF (nonResidue * x.val st.env.toValuation)).isSome) :
    prove (Checker.holds (F := F) (c := c)) (sqrtFlagged (c := c) sqrtF nonResidue x) st.nv st.env
        = .ok ((sqrtFlaggedRun sqrtF nonResidue st x).1.out
            (sqrtFlaggedRun sqrtF nonResidue st x).2) ∧
      Grants F st ((sqrtFlaggedRun sqrtF nonResidue st x).1,
          (sqrtFlaggedRun sqrtF nonResidue st x).2.1)
        ((sqrtF (twist sqrtF nonResidue (x.val st.env.toValuation))).getD 0) ∧
      Grants F st ((sqrtFlaggedRun sqrtF nonResidue st x).1,
          ↑(sqrtFlaggedRun sqrtF nonResidue st x).2.2)
        (bit (sqrtF (x.val st.env.toValuation)).isSome) := by
  -- the states, named
  generalize hG : sqrtFlaggedRun sqrtF nonResidue st x = G
  unfold sqrtFlaggedRun at hG
  extract_lets +lift st₁ r at hG
  have h₁ : st.extendMany [bit (sqrtF (x.val st.env.toValuation)).isSome] = st₁ := rfl
  have hr : selectRun st₁ (.unchecked (.var st.nv)) x (CVar.scale_ nonResidue x) = r := rfl
  clear_value r st₁
  subst hG
  -- the flag
  have l₁ : st.env.Le st₁.env := by rw [← h₁]; recall
  have hb : (CVar.var st.nv).Scoped st₁ := by rw [← h₁]; recall
  have hbv : (CVar.var st.nv).val st₁.env.toValuation
      = bit (sqrtF (x.val st.env.toValuation)).isSome := by
    rw [← h₁]; exact ProverState.get_extendMany_head ..
  -- the selection
  have g := selectRun_grants' (bb := (sqrtF (x.val st.env.toValuation)).isSome)
    (b := .unchecked (.var st.nv)) (e := CVar.scale_ nonResidue x)
    (ev := nonResidue * x.val st.env.toValuation) hb (by recall) (by recall) hbv
    (CVar.val_at rfl l₁ hx) (by rw [CVar.val_scale_, CVar.val_at rfl l₁ hx])
  rw [hr] at g
  have hsel : r.2.val r.1.env.toValuation = twist sqrtF nonResidue (x.val st.env.toValuation) :=
    g.fvar_val
  -- the root
  have l₂ := r.1.le_extendMany [(sqrtF (twist sqrtF nonResidue (x.val st.env.toValuation))).getD 0]
  have hsq : (sqrtF (twist sqrtF nonResidue (x.val st.env.toValuation))).getD 0
        * (sqrtF (twist sqrtF nonResidue (x.val st.env.toValuation))).getD 0
      = twist sqrtF nonResidue (x.val st.env.toValuation) := by
    unfold twist
    rcases hc : sqrtF (x.val st.env.toValuation) with _ | y
    · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (htwist hc)
      simp [hz, hroot _ z hz]
    · simp [hc, hroot _ y hc]
  refine ⟨?_, Grants.fvar (l₁.trans (g.le.trans l₂)) (by recall)
      (ProverState.get_extendMany_head ..),
    Grants.fvar (l₁.trans (g.le.trans l₂)) (by recall) (by recall)⟩
  -- the run
  simp only [sqrtFlagged, prove_bind]
  rw [prove_witnessB_run st (b := (sqrtF (x.val st.env.toValuation)).isSome)
    (by simp only [isQRWit, AsProver.bind_eq]; scoped_wit) (by simp [isQRWit, Except.bind]), h₁]
  simp only [Except.bind]
  rw [select_run (bb := (sqrtF (x.val st.env.toValuation)).isSome) (b := .unchecked (.var st.nv))
    st₁ hb (by recall) (by recall) hbv, hr]
  simp only [Except.bind]
  rw [prove_witnessF_run r.1 (v := (sqrtF (twist sqrtF nonResidue (x.val st.env.toValuation))).getD 0)
    (by simp only [sqrtWit, AsProver.bind_eq]; scoped_wit) (by simp [sqrtWit, Except.bind, hsel])]
  simp only [Except.bind]
  rw [assertSquare_run _ (by recall) (by recall)
    (by simp only [CVar.val, ProverState.get_extendMany_head, CVar.val_at hsel l₂ g.fvar_scoped, hsq])]
  rfl

end Snarky.Pilot
