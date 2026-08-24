import Snarky.Pilot.SqrtFlagged
import Snarky.Kimchi.Circuit.GroupMap

/-!
# Pilot: the BW19 chain

Twenty-nine leaf runs. Every run state is an opaque name fixed by its equation; every
grant is stated at the closed-form reading a consumer names; transport is `recall` and
`le_chain`. One theorem: the run equation, growth, scope, and the two readings.
-/

namespace Snarky.Pilot

open Snarky Snarky.Kimchi

variable {F c : Type}

/-- The in-circuit BW19 map, over the pilot's `sqrtFlagged`. -/
def groupMapCircuit [Field F] [DecidableEq F] [BasicSystem F c] (sqrtF : F → Option F)
    (params : GroupMapParams F) (t : FVar F) : CircuitM F c (AffinePoint (FVar F)) := do
  let t2 ← mul t t
  let t2PlusFu := CVar.add_ t2 (.const params.fu)
  let alphaInv ← mul t2PlusFu t2
  let alpha ← div (.const 1) alphaInv
  let t4 ← mul t2 t2
  let t4Alpha ← mul t4 alpha
  let temp1 ← mul t4Alpha (.const params.sqrtNeg3U2)
  let x1 := CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) temp1
  let x2 := CVar.sub_ (.const (-params.u)) x1
  let t2Inv ← mul alpha t2PlusFu
  let t2PlusFuSq ← mul t2PlusFu t2PlusFu
  let temp2a ← mul t2PlusFuSq t2Inv
  let temp2 ← mul temp2a (.const params.inv3U2)
  let x3 := CVar.sub_ (.const params.u) temp2
  let ySquared := fun (x : FVar F) => do
    let xSq ← mul x x
    let xCu ← mul xSq x
    pure (CVar.add_ xCu (.const params.b))
  let y1Sq ← ySquared x1
  let (y1, b1) ← sqrtFlagged sqrtF params.nonResidue y1Sq
  let y2Sq ← ySquared x2
  let (y2, b2) ← sqrtFlagged sqrtF params.nonResidue y2Sq
  let y3Sq ← ySquared x3
  let (y3, b3) ← sqrtFlagged sqrtF params.nonResidue y3Sq
  assertNonZero (CVar.add_ (CVar.add_ (↑b1) (↑b2)) (↑b3))
  let nb1 := Snarky.not b1
  let x2First ← Snarky.and nb1 b2
  let nb2AndB3 ← Snarky.and (Snarky.not b2) b3
  let x3First ← Snarky.and nb1 nb2AndB3
  let t3y ← mul (↑x3First) y3
  let t2y ← mul (↑x2First) y2
  let t1y ← mul (↑b1) y1
  let yResult := CVar.add_ (CVar.add_ t1y t2y) t3y
  let t3x ← mul (↑x3First) x3
  let t2x ← mul (↑x2First) x2
  let t1x ← mul (↑b1) x1
  let xResult := CVar.add_ (CVar.add_ t1x t2x) t3x
  pure ⟨xResult, yResult⟩

/-- The pilot gadget is the deployed one. -/
theorem groupMapCircuit_eq [Field F] [DecidableEq F] [BasicSystem F c] (sqrtF : F → Option F)
    (params : GroupMapParams F) (t : FVar F) :
    groupMapCircuit (c := c) sqrtF params t = Snarky.Kimchi.groupMapCircuit sqrtF params t :=
  rfl

/-- The run: each leaf at the state the previous left. -/
def groupMapCircuitRun [Field F] [DecidableEq F] (sqrtF : F → Option F)
    (params : GroupMapParams F) (st : ProverState F) (t : FVar F) :
    ProverState F × AffinePoint (FVar F) :=
  let r1 := mulRun st t t
  let r2 := mulRun r1.1 (CVar.add_ r1.2 (.const params.fu)) r1.2
  let r3 := divRun r2.1 (.const 1) r2.2
  let r4 := mulRun r3.1 r1.2 r1.2
  let r5 := mulRun r4.1 r4.2 r3.2
  let r6 := mulRun r5.1 r5.2 (.const params.sqrtNeg3U2)
  let r7 := mulRun r6.1 r3.2 (CVar.add_ r1.2 (.const params.fu))
  let r8 := mulRun r7.1 (CVar.add_ r1.2 (.const params.fu)) (CVar.add_ r1.2 (.const params.fu))
  let r9 := mulRun r8.1 r8.2 r7.2
  let r10 := mulRun r9.1 r9.2 (.const params.inv3U2)
  let r11 := mulRun r10.1 (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2)
    (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2)
  let r12 := mulRun r11.1 r11.2 (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2)
  let s1 := sqrtFlaggedRun sqrtF params.nonResidue r12.1 (CVar.add_ r12.2 (.const params.b))
  let r13 := mulRun s1.1 (CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
    (CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
  let r14 := mulRun r13.1 r13.2
    (CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
  let s2 := sqrtFlaggedRun sqrtF params.nonResidue r14.1 (CVar.add_ r14.2 (.const params.b))
  let r15 := mulRun s2.1 (CVar.sub_ (.const params.u) r10.2) (CVar.sub_ (.const params.u) r10.2)
  let r16 := mulRun r15.1 r15.2 (CVar.sub_ (.const params.u) r10.2)
  let s3 := sqrtFlaggedRun sqrtF params.nonResidue r16.1 (CVar.add_ r16.2 (.const params.b))
  let rNZ := invRun s3.1 (CVar.add_ (CVar.add_ ↑s1.2.2 ↑s2.2.2) ↑s3.2.2)
  let a1 := andRun rNZ.1 (Snarky.not s1.2.2) s2.2.2
  let a2 := andRun a1.1 (Snarky.not s2.2.2) s3.2.2
  let a3 := andRun a2.1 (Snarky.not s1.2.2) a2.2
  let m1 := mulRun a3.1 ↑a3.2 s3.2.1
  let m2 := mulRun m1.1 ↑a1.2 s2.2.1
  let m3 := mulRun m2.1 ↑s1.2.2 s1.2.1
  let m4 := mulRun m3.1 ↑a3.2 (CVar.sub_ (.const params.u) r10.2)
  let m5 := mulRun m4.1 ↑a1.2
    (CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
  let m6 := mulRun m5.1 ↑s1.2.2 (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2)
  (m6.1, ⟨CVar.add_ (CVar.add_ m6.2 m5.2) m4.2, CVar.add_ (CVar.add_ m3.2 m2.2) m1.2⟩)

/-- `groupMapPure`, branch by branch. -/
private theorem groupMapPure_eq [Field F] (sqrtF : F → Option F) (params : GroupMapParams F)
    (t : F) :
    groupMapPure sqrtF params t =
      if (sqrtF (ySquared params (potentialXs params t).1)).isSome then
        ((potentialXs params t).1, (sqrtF (ySquared params (potentialXs params t).1)).getD 0)
      else if (sqrtF (ySquared params (potentialXs params t).2.1)).isSome then
        ((potentialXs params t).2.1, (sqrtF (ySquared params (potentialXs params t).2.1)).getD 0)
      else if (sqrtF (ySquared params (potentialXs params t).2.2)).isSome then
        ((potentialXs params t).2.2, (sqrtF (ySquared params (potentialXs params t).2.2)).getD 0)
      else (0, 0) := by
  rcases h : potentialXs params t with ⟨x1, x2, x3⟩
  simp only [groupMapPure, h]
  rcases hc1 : sqrtF (ySquared params x1) with _ | y1 <;>
    rcases hc2 : sqrtF (ySquared params x2) with _ | y2 <;>
    rcases hc3 : sqrtF (ySquared params x3) with _ | y3 <;>
    simp [hc1, hc2, hc3]

/-- `twist` at a root's presence. -/
private theorem twist_of_isSome [Field F] {sqrtF : F → Option F} {nr a : F}
    (h : (sqrtF a).isSome = true) : twist sqrtF nr a = a := by
  simp [twist, h]

/-- The honest run: accepted, landing at `groupMapCircuitRun`; the point in scope at the
state after, reading the pure map's point. -/
theorem groupMap_facts [Field F] [DecidableEq F] [BasicSystem F c] [Checker F c]
    [LawfulChecker F c] (sqrtF : F → Option F) (params : GroupMapParams F) {t : FVar F}
    (st : ProverState F) (ht : t.Scoped st)
    (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : ∀ a, sqrtF a = none → (sqrtF (params.nonResidue * a)).isSome)
    (htwo : (2 : F) ≠ 0) (hthree : (3 : F) ≠ 0)
    (hne : (t.val st.env.toValuation * t.val st.env.toValuation + params.fu)
      * (t.val st.env.toValuation * t.val st.env.toValuation) ≠ 0)
    (hdisj : (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome ∨
      (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome ∨
      (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome) :
    prove (Checker.holds (F := F) (c := c)) (groupMapCircuit (c := c) sqrtF params t) st.nv st.env
        = .ok ((groupMapCircuitRun sqrtF params st t).1.out
            (groupMapCircuitRun sqrtF params st t).2) ∧
      st.env.Le (groupMapCircuitRun sqrtF params st t).1.env ∧
      (groupMapCircuitRun sqrtF params st t).2.x.Scoped (groupMapCircuitRun sqrtF params st t).1 ∧
      (groupMapCircuitRun sqrtF params st t).2.y.Scoped (groupMapCircuitRun sqrtF params st t).1 ∧
      (groupMapCircuitRun sqrtF params st t).2.x.val
          (groupMapCircuitRun sqrtF params st t).1.env.toValuation
        = (groupMapPure sqrtF params (t.val st.env.toValuation)).1 ∧
      (groupMapCircuitRun sqrtF params st t).2.y.val
          (groupMapCircuitRun sqrtF params st t).1.env.toValuation
        = (groupMapPure sqrtF params (t.val st.env.toValuation)).2 := by
  set tv := t.val st.env.toValuation with htv
  set X1 := (potentialXs params tv).1 with hX1
  set X2 := (potentialXs params tv).2.1 with hX2
  set X3 := (potentialXs params tv).2.2 with hX3
  set B1 := (sqrtF (ySquared params X1)).isSome with hB1
  set B2 := (sqrtF (ySquared params X2)).isSome with hB2
  set B3 := (sqrtF (ySquared params X3)).isSome with hB3
  -- the flag sum is nonzero
  have hsumne : (bit B1 + bit B2 + bit B3 : F) ≠ 0 := by
    clear_value B1 B2 B3
    cases B1 <;> cases B2 <;> cases B3 <;> simp [bit] at hdisj ⊢ <;>
      first
      | exact one_ne_zero
      | (rw [one_add_one_eq_two]; exact htwo)
      | (rw [one_add_one_eq_two, two_add_one_eq_three]; exact hthree)
  -- the states, named
  generalize hG : groupMapCircuitRun sqrtF params st t = G
  unfold groupMapCircuitRun at hG
  extract_lets +lift r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 s1 r13 r14 s2 r15 r16 s3 rNZ a1 a2
    a3 m1 m2 m3 m4 m5 m6 at hG
  have hr1 : mulRun st t t = r1 := rfl
  have hr2 : mulRun r1.1 (CVar.add_ r1.2 (.const params.fu)) r1.2 = r2 := rfl
  have hr3 : divRun r2.1 (.const 1) r2.2 = r3 := rfl
  have hr4 : mulRun r3.1 r1.2 r1.2 = r4 := rfl
  have hr5 : mulRun r4.1 r4.2 r3.2 = r5 := rfl
  have hr6 : mulRun r5.1 r5.2 (.const params.sqrtNeg3U2) = r6 := rfl
  have hr7 : mulRun r6.1 r3.2 (CVar.add_ r1.2 (.const params.fu)) = r7 := rfl
  have hr8 : mulRun r7.1 (CVar.add_ r1.2 (.const params.fu)) (CVar.add_ r1.2 (.const params.fu))
    = r8 := rfl
  have hr9 : mulRun r8.1 r8.2 r7.2 = r9 := rfl
  have hr10 : mulRun r9.1 r9.2 (.const params.inv3U2) = r10 := rfl
  have hr11 : mulRun r10.1 (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2)
    (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2) = r11 := rfl
  have hr12 : mulRun r11.1 r11.2 (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2) = r12 :=
    rfl
  have hs1 : sqrtFlaggedRun sqrtF params.nonResidue r12.1 (CVar.add_ r12.2 (.const params.b))
    = s1 := rfl
  have hr13 : mulRun s1.1
    (CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
    (CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
    = r13 := rfl
  have hr14 : mulRun r13.1 r13.2
    (CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
    = r14 := rfl
  have hs2 : sqrtFlaggedRun sqrtF params.nonResidue r14.1 (CVar.add_ r14.2 (.const params.b))
    = s2 := rfl
  have hr15 : mulRun s2.1 (CVar.sub_ (.const params.u) r10.2) (CVar.sub_ (.const params.u) r10.2)
    = r15 := rfl
  have hr16 : mulRun r15.1 r15.2 (CVar.sub_ (.const params.u) r10.2) = r16 := rfl
  have hs3 : sqrtFlaggedRun sqrtF params.nonResidue r16.1 (CVar.add_ r16.2 (.const params.b))
    = s3 := rfl
  have hrNZ : invRun s3.1 (CVar.add_ (CVar.add_ ↑s1.2.2 ↑s2.2.2) ↑s3.2.2) = rNZ := rfl
  have ha1 : andRun rNZ.1 (Snarky.not s1.2.2) s2.2.2 = a1 := rfl
  have ha2 : andRun a1.1 (Snarky.not s2.2.2) s3.2.2 = a2 := rfl
  have ha3 : andRun a2.1 (Snarky.not s1.2.2) a2.2 = a3 := rfl
  have hm1 : mulRun a3.1 ↑a3.2 s3.2.1 = m1 := rfl
  have hm2 : mulRun m1.1 ↑a1.2 s2.2.1 = m2 := rfl
  have hm3 : mulRun m2.1 ↑s1.2.2 s1.2.1 = m3 := rfl
  have hm4 : mulRun m3.1 ↑a3.2 (CVar.sub_ (.const params.u) r10.2) = m4 := rfl
  have hm5 : mulRun m4.1 ↑a1.2
    (CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
    = m5 := rfl
  have hm6 : mulRun m5.1 ↑s1.2.2 (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2) = m6 :=
    rfl
  clear_value m6 m5 m4 m3 m2 m1 a3 a2 a1 rNZ s3 r16 r15 s2 r14 r13 s1 r12 r11 r10 r9 r8 r7 r6
    r5 r4 r3 r2 r1
  subst hG
  -- the candidate abscissae
  have g1 : Grants F st r1 (tv * tv) := by
    have h := mulRun_grants' (st := st) (x := t) (y := t) ht ht rfl rfl
    rwa [hr1] at h
  have htpf : (CVar.add_ r1.2 (.const params.fu)).Scoped r1.1 := by recall
  have htpfv : (CVar.add_ r1.2 (.const params.fu)).val r1.1.env.toValuation
      = tv * tv + params.fu := by
    rw [CVar.val_add_, g1.fvar_val]; rfl
  have g2 : Grants F r1.1 r2 ((tv * tv + params.fu) * (tv * tv)) := by
    have h := mulRun_grants' (st := r1.1) (x := CVar.add_ r1.2 (.const params.fu)) (y := r1.2)
      htpf g1.fvar_scoped htpfv g1.fvar_val
    rwa [hr2] at h
  have g3 : Grants F r2.1 r3 (1 / ((tv * tv + params.fu) * (tv * tv))) := by
    have h := divRun_grants' (st := r2.1) (x := .const 1) (y := r2.2) (CVar.scoped_const _ _)
      g2.fvar_scoped rfl g2.fvar_val
    rwa [hr3] at h
  have g4 : Grants F r3.1 r4 (tv * tv * (tv * tv)) := by
    have h := mulRun_grants' (st := r3.1) (x := r1.2) (y := r1.2) (by recall) (by recall)
      (CVar.val_at g1.fvar_val (by le_chain) g1.fvar_scoped)
      (CVar.val_at g1.fvar_val (by le_chain) g1.fvar_scoped)
    rwa [hr4] at h
  have g5 : Grants F r4.1 r5 (tv * tv * (tv * tv) * (1 / ((tv * tv + params.fu) * (tv * tv)))) := by
    have h := mulRun_grants' (st := r4.1) (x := r4.2) (y := r3.2) g4.fvar_scoped (by recall)
      g4.fvar_val (CVar.val_at g3.fvar_val (by le_chain) g3.fvar_scoped)
    rwa [hr5] at h
  have g6 : Grants F r5.1 r6 (tv * tv * (tv * tv) * (1 / ((tv * tv + params.fu) * (tv * tv)))
      * params.sqrtNeg3U2) := by
    have h := mulRun_grants' (st := r5.1) (x := r5.2) (y := .const params.sqrtNeg3U2)
      g5.fvar_scoped (CVar.scoped_const _ _) g5.fvar_val rfl
    rwa [hr6] at h
  have hx1 : (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2).Scoped r6.1 := by recall
  have hx1v : (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2).val r6.1.env.toValuation
      = X1 := by
    rw [CVar.val_sub_, g6.fvar_val]; rfl
  have hx2 : (CVar.sub_ (.const (-params.u))
      (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2)).Scoped r6.1 := by recall
  have hx2v : (CVar.sub_ (.const (-params.u))
      (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2)).val r6.1.env.toValuation = X2 := by
    rw [CVar.val_sub_, hx1v]; rfl
  have g7 : Grants F r6.1 r7 (1 / ((tv * tv + params.fu) * (tv * tv)) * (tv * tv + params.fu)) := by
    have h := mulRun_grants' (st := r6.1) (x := r3.2) (y := CVar.add_ r1.2 (.const params.fu))
      (by recall) (by recall) (CVar.val_at g3.fvar_val (by le_chain) g3.fvar_scoped)
      (CVar.val_at htpfv (by le_chain) htpf)
    rwa [hr7] at h
  have g8 : Grants F r7.1 r8 ((tv * tv + params.fu) * (tv * tv + params.fu)) := by
    have h := mulRun_grants' (st := r7.1) (x := CVar.add_ r1.2 (.const params.fu))
      (y := CVar.add_ r1.2 (.const params.fu)) (by recall) (by recall)
      (CVar.val_at htpfv (by le_chain) htpf) (CVar.val_at htpfv (by le_chain) htpf)
    rwa [hr8] at h
  have g9 : Grants F r8.1 r9 ((tv * tv + params.fu) * (tv * tv + params.fu)
      * (1 / ((tv * tv + params.fu) * (tv * tv)) * (tv * tv + params.fu))) := by
    have h := mulRun_grants' (st := r8.1) (x := r8.2) (y := r7.2) g8.fvar_scoped (by recall)
      g8.fvar_val (CVar.val_at g7.fvar_val (by le_chain) g7.fvar_scoped)
    rwa [hr9] at h
  have g10 : Grants F r9.1 r10 ((tv * tv + params.fu) * (tv * tv + params.fu)
      * (1 / ((tv * tv + params.fu) * (tv * tv)) * (tv * tv + params.fu)) * params.inv3U2) := by
    have h := mulRun_grants' (st := r9.1) (x := r9.2) (y := .const params.inv3U2) g9.fvar_scoped
      (CVar.scoped_const _ _) g9.fvar_val rfl
    rwa [hr10] at h
  have hx3 : (CVar.sub_ (.const params.u) r10.2).Scoped r10.1 := by recall
  have hx3v : (CVar.sub_ (.const params.u) r10.2).val r10.1.env.toValuation = X3 := by
    rw [CVar.val_sub_, g10.fvar_val]; rfl
  -- the three flagged roots
  have g11 : Grants F r10.1 r11 (X1 * X1) := by
    have h := mulRun_grants' (st := r10.1)
      (x := CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2)
      (y := CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2) (by recall) (by recall)
      (CVar.val_at hx1v (by le_chain) hx1) (CVar.val_at hx1v (by le_chain) hx1)
    rwa [hr11] at h
  have g12 : Grants F r11.1 r12 (X1 * X1 * X1) := by
    have h := mulRun_grants' (st := r11.1) (x := r11.2)
      (y := CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2) g11.fvar_scoped (by recall)
      g11.fvar_val (CVar.val_at hx1v (by le_chain) hx1)
    rwa [hr12] at h
  have hy1 : (CVar.add_ r12.2 (.const params.b)).Scoped r12.1 := by recall
  have hy1v : (CVar.add_ r12.2 (.const params.b)).val r12.1.env.toValuation
      = ySquared params X1 := by
    rw [CVar.val_add_, g12.fvar_val]; rfl
  obtain ⟨hs1run, gs1r, gs1b⟩ := sqrtFlagged_facts (c := c) sqrtF params.nonResidue r12.1 hy1
    hroot (htwist _)
  rw [hs1] at hs1run gs1r gs1b
  rw [hy1v] at hs1run gs1r gs1b
  have g13 : Grants F s1.1 r13 (X2 * X2) := by
    have h := mulRun_grants' (st := s1.1)
      (x := CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
      (y := CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
      (by recall) (by recall) (CVar.val_at hx2v (by le_chain) hx2) (CVar.val_at hx2v (by le_chain) hx2)
    rwa [hr13] at h
  have g14 : Grants F r13.1 r14 (X2 * X2 * X2) := by
    have h := mulRun_grants' (st := r13.1) (x := r13.2)
      (y := CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
      g13.fvar_scoped (by recall) g13.fvar_val (CVar.val_at hx2v (by le_chain) hx2)
    rwa [hr14] at h
  have hy2 : (CVar.add_ r14.2 (.const params.b)).Scoped r14.1 := by recall
  have hy2v : (CVar.add_ r14.2 (.const params.b)).val r14.1.env.toValuation
      = ySquared params X2 := by
    rw [CVar.val_add_, g14.fvar_val]; rfl
  obtain ⟨hs2run, gs2r, gs2b⟩ := sqrtFlagged_facts (c := c) sqrtF params.nonResidue r14.1 hy2
    hroot (htwist _)
  rw [hs2] at hs2run gs2r gs2b
  rw [hy2v] at hs2run gs2r gs2b
  have g15 : Grants F s2.1 r15 (X3 * X3) := by
    have h := mulRun_grants' (st := s2.1) (x := CVar.sub_ (.const params.u) r10.2)
      (y := CVar.sub_ (.const params.u) r10.2) (by recall) (by recall)
      (CVar.val_at hx3v (by le_chain) hx3) (CVar.val_at hx3v (by le_chain) hx3)
    rwa [hr15] at h
  have g16 : Grants F r15.1 r16 (X3 * X3 * X3) := by
    have h := mulRun_grants' (st := r15.1) (x := r15.2) (y := CVar.sub_ (.const params.u) r10.2)
      g15.fvar_scoped (by recall) g15.fvar_val (CVar.val_at hx3v (by le_chain) hx3)
    rwa [hr16] at h
  have hy3 : (CVar.add_ r16.2 (.const params.b)).Scoped r16.1 := by recall
  have hy3v : (CVar.add_ r16.2 (.const params.b)).val r16.1.env.toValuation
      = ySquared params X3 := by
    rw [CVar.val_add_, g16.fvar_val]; rfl
  obtain ⟨hs3run, gs3r, gs3b⟩ := sqrtFlagged_facts (c := c) sqrtF params.nonResidue r16.1 hy3
    hroot (htwist _)
  rw [hs3] at hs3run gs3r gs3b
  rw [hy3v] at hs3run gs3r gs3b
  -- the flag sum and the selectors
  have hsum : (CVar.add_ (CVar.add_ (↑s1.2.2 : CVar F) ↑s2.2.2) ↑s3.2.2).Scoped s3.1 := by recall
  have hsumv : (CVar.add_ (CVar.add_ (↑s1.2.2 : CVar F) ↑s2.2.2) ↑s3.2.2).val s3.1.env.toValuation
      = bit B1 + bit B2 + bit B3 := by
    rw [CVar.val_add_, CVar.val_add_, gs3b.fvar_val,
      CVar.val_at gs2b.fvar_val (by le_chain) gs2b.fvar_scoped,
      CVar.val_at gs1b.fvar_val (by le_chain) gs1b.fvar_scoped]
  have gNZ : Grants F s3.1 rNZ (bit B1 + bit B2 + bit B3)⁻¹ := by
    have h := invRun_grants' hsum hsumv
    rwa [hrNZ] at h
  have ga1 : Grants F rNZ.1 (a1.1, ↑a1.2) (bit (!B1 && B2)) := by
    have h := andRun_grants (st := rNZ.1) (a := Snarky.not s1.2.2) (b := s2.2.2) (by recall)
      (by recall) (not_val (CVar.val_at gs1b.fvar_val (by le_chain) gs1b.fvar_scoped))
      (CVar.val_at gs2b.fvar_val (by le_chain) gs2b.fvar_scoped)
    rwa [ha1] at h
  have ga2 : Grants F a1.1 (a2.1, ↑a2.2) (bit (!B2 && B3)) := by
    have h := andRun_grants (st := a1.1) (a := Snarky.not s2.2.2) (b := s3.2.2) (by recall)
      (by recall) (not_val (CVar.val_at gs2b.fvar_val (by le_chain) gs2b.fvar_scoped))
      (CVar.val_at gs3b.fvar_val (by le_chain) gs3b.fvar_scoped)
    rwa [ha2] at h
  have ga3 : Grants F a2.1 (a3.1, ↑a3.2) (bit (!B1 && (!B2 && B3))) := by
    have h := andRun_grants (st := a2.1) (a := Snarky.not s1.2.2) (b := a2.2) (by recall)
      ga2.fvar_scoped (not_val (CVar.val_at gs1b.fvar_val (by le_chain) gs1b.fvar_scoped))
      ga2.fvar_val
    rwa [ha3] at h
  -- the selection products
  have gm1 : Grants F a3.1 m1 (bit (!B1 && (!B2 && B3))
      * (sqrtF (twist sqrtF params.nonResidue (ySquared params X3))).getD 0) := by
    have h := mulRun_grants' (st := a3.1) (x := ↑a3.2) (y := s3.2.1) ga3.fvar_scoped (by recall)
      ga3.fvar_val (CVar.val_at gs3r.fvar_val (by le_chain) gs3r.fvar_scoped)
    rwa [hm1] at h
  have gm2 : Grants F m1.1 m2 (bit (!B1 && B2)
      * (sqrtF (twist sqrtF params.nonResidue (ySquared params X2))).getD 0) := by
    have h := mulRun_grants' (st := m1.1) (x := ↑a1.2) (y := s2.2.1) (by recall) (by recall)
      (CVar.val_at ga1.fvar_val (by le_chain) ga1.fvar_scoped)
      (CVar.val_at gs2r.fvar_val (by le_chain) gs2r.fvar_scoped)
    rwa [hm2] at h
  have gm3 : Grants F m2.1 m3 (bit B1
      * (sqrtF (twist sqrtF params.nonResidue (ySquared params X1))).getD 0) := by
    have h := mulRun_grants' (st := m2.1) (x := ↑s1.2.2) (y := s1.2.1) (by recall) (by recall)
      (CVar.val_at gs1b.fvar_val (by le_chain) gs1b.fvar_scoped)
      (CVar.val_at gs1r.fvar_val (by le_chain) gs1r.fvar_scoped)
    rwa [hm3] at h
  have gm4 : Grants F m3.1 m4 (bit (!B1 && (!B2 && B3)) * X3) := by
    have h := mulRun_grants' (st := m3.1) (x := ↑a3.2) (y := CVar.sub_ (.const params.u) r10.2)
      (by recall) (by recall) (CVar.val_at ga3.fvar_val (by le_chain) ga3.fvar_scoped)
      (CVar.val_at hx3v (by le_chain) hx3)
    rwa [hm4] at h
  have gm5 : Grants F m4.1 m5 (bit (!B1 && B2) * X2) := by
    have h := mulRun_grants' (st := m4.1) (x := ↑a1.2)
      (y := CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
      (by recall) (by recall) (CVar.val_at ga1.fvar_val (by le_chain) ga1.fvar_scoped)
      (CVar.val_at hx2v (by le_chain) hx2)
    rwa [hm5] at h
  have gm6 : Grants F m5.1 m6 (bit B1 * X1) := by
    have h := mulRun_grants' (st := m5.1) (x := ↑s1.2.2)
      (y := CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2) (by recall) (by recall)
      (CVar.val_at gs1b.fvar_val (by le_chain) gs1b.fvar_scoped)
      (CVar.val_at hx1v (by le_chain) hx1)
    rwa [hm6] at h
  -- the readings
  have hxR : (CVar.add_ (CVar.add_ m6.2 m5.2) m4.2).val m6.1.env.toValuation
      = bit B1 * X1 + bit (!B1 && B2) * X2 + bit (!B1 && (!B2 && B3)) * X3 := by
    rw [CVar.val_add_, CVar.val_add_, gm6.fvar_val,
      CVar.val_at gm5.fvar_val (by le_chain) gm5.fvar_scoped,
      CVar.val_at gm4.fvar_val (by le_chain) gm4.fvar_scoped]
  have hyR : (CVar.add_ (CVar.add_ m3.2 m2.2) m1.2).val m6.1.env.toValuation
      = bit B1 * (sqrtF (twist sqrtF params.nonResidue (ySquared params X1))).getD 0
        + bit (!B1 && B2) * (sqrtF (twist sqrtF params.nonResidue (ySquared params X2))).getD 0
        + bit (!B1 && (!B2 && B3))
          * (sqrtF (twist sqrtF params.nonResidue (ySquared params X3))).getD 0 := by
    rw [CVar.val_add_, CVar.val_add_,
      CVar.val_at gm3.fvar_val (by le_chain) gm3.fvar_scoped,
      CVar.val_at gm2.fvar_val (by le_chain) gm2.fvar_scoped,
      CVar.val_at gm1.fvar_val (by le_chain) gm1.fvar_scoped]
  refine ⟨?_, by le_chain, by recall, by recall, ?_, ?_⟩
  · -- the run
    simp only [groupMapCircuit, prove_bind]
    rw [mul_run (c := c) (x := t) (y := t) st ht ht, hr1]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := CVar.add_ r1.2 (.const params.fu)) (y := r1.2) r1.1 htpf
      g1.fvar_scoped, hr2]
    simp only [Except.bind]
    rw [div_run (c := c) (x := .const 1) (y := r2.2) r2.1 (CVar.scoped_const _ _) g2.fvar_scoped
      (by rw [g2.fvar_val]; exact hne), hr3]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := r1.2) (y := r1.2) r3.1 (by recall) (by recall), hr4]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := r4.2) (y := r3.2) r4.1 g4.fvar_scoped (by recall), hr5]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := r5.2) (y := .const params.sqrtNeg3U2) r5.1 g5.fvar_scoped
      (CVar.scoped_const _ _), hr6]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := r3.2) (y := CVar.add_ r1.2 (.const params.fu)) r6.1 (by recall)
      (by recall), hr7]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := CVar.add_ r1.2 (.const params.fu))
      (y := CVar.add_ r1.2 (.const params.fu)) r7.1 (by recall) (by recall), hr8]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := r8.2) (y := r7.2) r8.1 g8.fvar_scoped (by recall), hr9]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := r9.2) (y := .const params.inv3U2) r9.1 g9.fvar_scoped
      (CVar.scoped_const _ _), hr10]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2)
      (y := CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2) r10.1 (by recall) (by recall),
      hr11]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := r11.2) (y := CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2)
      r11.1 g11.fvar_scoped (by recall), hr12]
    simp only [Except.bind, prove_pure]
    rw [hs1run]
    simp only [Except.bind]
    rw [mul_run (c := c)
      (x := CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
      (y := CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
      s1.1 (by recall) (by recall), hr13]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := r13.2)
      (y := CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
      r13.1 g13.fvar_scoped (by recall), hr14]
    simp only [Except.bind, prove_pure]
    rw [hs2run]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := CVar.sub_ (.const params.u) r10.2)
      (y := CVar.sub_ (.const params.u) r10.2) s2.1 (by recall) (by recall), hr15]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := r15.2) (y := CVar.sub_ (.const params.u) r10.2) r15.1
      g15.fvar_scoped (by recall), hr16]
    simp only [Except.bind, prove_pure]
    rw [hs3run]
    simp only [Except.bind]
    rw [assertNonZero_run (c := c) s3.1 hsum (by rw [hsumv]; exact hsumne), hrNZ]
    simp only [Except.bind]
    rw [and_run (c := c) (a := Snarky.not s1.2.2) (b := s2.2.2) rNZ.1 (by recall) (by recall), ha1]
    simp only [Except.bind]
    rw [and_run (c := c) (a := Snarky.not s2.2.2) (b := s3.2.2) a1.1 (by recall) (by recall), ha2]
    simp only [Except.bind]
    rw [and_run (c := c) (a := Snarky.not s1.2.2) (b := a2.2) a2.1 (by recall) ga2.fvar_scoped,
      ha3]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := ↑a3.2) (y := s3.2.1) a3.1 ga3.fvar_scoped (by recall), hm1]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := ↑a1.2) (y := s2.2.1) m1.1 (by recall) (by recall), hm2]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := ↑s1.2.2) (y := s1.2.1) m2.1 (by recall) (by recall), hm3]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := ↑a3.2) (y := CVar.sub_ (.const params.u) r10.2) m3.1 (by recall)
      (by recall), hm4]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := ↑a1.2)
      (y := CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2))
      m4.1 (by recall) (by recall), hm5]
    simp only [Except.bind]
    rw [mul_run (c := c) (x := ↑s1.2.2) (y := CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2)
      m5.1 (by recall) (by recall), hm6]
    simp only [Except.bind, prove_pure]
  · -- the abscissa
    rw [hxR, groupMapPure_eq]
    clear_value B1 B2 B3
    cases B1 <;> cases B2 <;> cases B3 <;> simp [bit]
  · -- the ordinate
    rw [hyR, groupMapPure_eq]
    clear_value B1 B2 B3
    cases B1 <;> cases B2 <;> cases B3 <;> simp [bit, twist_of_isSome, twist]

end Snarky.Pilot
