import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.Assert
import Snarky.Circuit.DSL.Boolean
import Snarky.Kimchi.Semantics

/-!
# The BW19 hash-to-curve gadget

Port of `Snarky.Circuit.Kimchi.GroupMap`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/GroupMap.purs; mina
`group_map/bw19.ml`; Wahby–Boneh 2019, https://eprint.iacr.org/2019/403): map a
field element onto a curve `y² = x³ + b`. Three candidate abscissae are computed
from the `setup()` parameters; per candidate, `sqrtFlagged` witnesses a
residuosity flag and a root of either the candidate ordinate square or its
non-residue twist; at least one flag is asserted set, and the point is the
first-flagged candidate, selected by mutually exclusive boolean products.

The value level (`potentialXs`, `groupMapPure`) is the same map the poseidon package's
fixture-validated `Poseidon.GroupMap` computes at the deployed Pasta fields; the
laws here stay generic and quote the module's own pure model, PS-parity.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS `groupMapParams` builds the parameter record from the `HasBW19` FFI and a
  non-residue search; the port takes `GroupMapParams` as data — the deployed
  values live with their curves (the poseidon package's `setup()` constants).
- PS's advice consults the `HasSqrt` class; the port threads an explicit
  `sqrtF : F → Option F` — like `endoInv`'s advice parameters, soundness never
  consults it, and completeness states the coherence it needs.
- PS's advice throws on an impossible root (`unsafeThrow`); the port is total
  (`Option.getD 0`, the pure map falling back to `(0, 0)`) — unreachable for
  honest inputs, where a flagged candidate always has its root.
-/

namespace Snarky.Kimchi

open Snarky Std.Do

variable {F c : Type}

/-- The BW19 `setup()` parameters (PS `GroupMapParams`): the seed `u`, its curve
image `f(u) = u³ + b`, the square-root and inverse constants, the curve constant,
and a known quadratic non-residue for the flagged-root trick. -/
structure GroupMapParams (F : Type) where
  /-- The SvdW seed `u`. -/
  u : F
  /-- `f(u) = u³ + b`. -/
  fu : F
  /-- `(√(-3u²) − u) / 2`. -/
  sqrtNeg3U2MinusUOver2 : F
  /-- `√(-3u²)`. -/
  sqrtNeg3U2 : F
  /-- `(3u²)⁻¹`. -/
  inv3U2 : F
  /-- The curve constant `b` of `y² = x³ + b`. -/
  b : F
  /-- A known quadratic non-residue. -/
  nonResidue : F

/-- The three candidate abscissae (PS `potentialXs`): one of them is the abscissa
of a curve point — Shallue–van de Woestijne's theorem, which the laws take as a
hypothesis rather than prove. Division is the field's total one (`0⁻¹ = 0`),
matching the gadget's `div`. -/
def potentialXs [Field F] (params : GroupMapParams F) (t : F) : F × F × F :=
  let t2 := t * t
  let alphaInv := (t2 + params.fu) * t2
  let alpha := 1 / alphaInv
  let t4 := t2 * t2
  let x1 := params.sqrtNeg3U2MinusUOver2 - t4 * alpha * params.sqrtNeg3U2
  let x2 := -params.u - x1
  let t2PlusFu := t2 + params.fu
  let t2Inv := alpha * t2PlusFu
  let x3 := params.u - (t2PlusFu * t2PlusFu) * t2Inv * params.inv3U2
  (x1, x2, x3)

/-- The curve's ordinate square `x³ + b` (PS's local `ySquared`): the per-candidate
test value — `groupMapPure`'s branch scrutinee and the completeness law's SvdW
vocabulary. -/
def ySquared [Field F] (params : GroupMapParams F) (x : F) : F :=
  x * x * x + params.b

/-- The pure map (PS `groupMap`): the first candidate whose ordinate square has a
root under `sqrtF`, as a coordinate pair. The no-candidate branch returns `(0, 0)`
(PS throws) — unreachable when some candidate is a square and `sqrtF` is total on
squares. -/
def groupMapPure [Field F] (sqrtF : F → Option F) (params : GroupMapParams F)
    (t : F) : F × F :=
  let (x1, x2, x3) := potentialXs params t
  match sqrtF (ySquared params x1) with
  | some y => (x1, y)
  | none =>
    match sqrtF (ySquared params x2) with
    | some y => (x2, y)
    | none =>
      match sqrtF (ySquared params x3) with
      | some y => (x3, y)
      | none => (0, 0)

/-- The residuosity flag's advice: whether `sqrtF` finds a root. -/
private def isQRWit [Field F] (sqrtF : F → Option F) (x : FVar F) :
    AsProver F Bool := do
  let v ← AsProver.readCVar x
  pure (sqrtF v).isSome

/-- The root's advice: `sqrtF`'s root of the selected operand (`0` when there is
none — unreachable honestly). -/
private def sqrtWit [Field F] (sqrtF : F → Option F) (x : FVar F) :
    AsProver F F := do
  let v ← AsProver.readCVar x
  pure ((sqrtF v).getD 0)

/-- In-circuit square root with a residuosity flag (PS `sqrtFlagged`): witness the
flag, select the operand or its non-residue twist, witness a root, and pin it with
one `square` row — `y² = if isQR then x else nonResidue·x`. -/
private def sqrtFlagged [Field F] [DecidableEq F] [BasicSystem F c]
    (sqrtF : F → Option F) (nonResidue : F) (x : FVar F) :
    CircuitM F c (FVar F × BoolVar F) := do
  let isQR ← witness (val := Bool) (isQRWit sqrtF x)
  let mX := CVar.scale_ nonResidue x
  let xOrMx ← select isQR x mX
  let sqrtVal ← witness (val := F) (sqrtWit sqrtF xOrMx)
  assertSquare sqrtVal xOrMx
  pure (sqrtVal, isQR)

/-- The in-circuit BW19 map (PS `groupMapCircuit`): the candidate abscissae from
seven `mul`s and one `div`, a flagged root per candidate, at least one flag
asserted set, and the first-flagged candidate selected by mutually exclusive
boolean products. -/
def groupMapCircuit [Field F] [DecidableEq F] [BasicSystem F c]
    (sqrtF : F → Option F) (params : GroupMapParams F) (t : FVar F) :
    CircuitM F c (AffinePoint (FVar F)) := do
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

/-! ## The laws

Soundness quotes the module's own pure model: any satisfying valuation reads the
result as an on-curve pair whose abscissa is one of `potentialXs`' three
candidates. Completeness lands on `groupMapPure` — the first-flagged candidate —
under the advice coherence the honest run needs. -/

open Std.Do in
/-- `sqrtFlagged` is sound: the flag reads as a genuine bit and the returned value
squares to the flag-selected operand — `y² = if isQR then x else nonResidue·x`. -/
@[spec] private theorem sqrtFlagged_spec [Field F] [DecidableEq F] {c : Type}
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (sqrtF : F → Option F) (nonResidue : F) (x : FVar F)
    (Q : PostCond (FVar F × BoolVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F × BoolVar F) =>
        ∃ bb : Bool, (↑r.2 : CVar F).val V = bit bb ∧
          r.1.val V * r.1.val V
            = (if bb then x.val V else nonResidue * x.val V)) Q⦄
    (sqrtFlagged (c := c) sqrtF nonResidue x)
    ⦃Q⦄ := by
  simp only [sqrtFlagged]
  mvcgen [witnessBool_spec, -witness_spec]
  rename_i s hpre
  intro isQR _ hbool
  mvcgen
  intro xOrMx _ hsel
  mvcgen
  intro sqrtVal _
  mvcgen
  intro _ _ hsq
  mvcgen
  rcases hbool with h0 | h1
  · refine hpre (sqrtVal, isQR) _ ⟨false, by simpa [bit] using h0, ?_⟩
    rw [hsq, hsel false (by simpa [bit] using h0)]
    simp [selectPure, CVar.val_scale_]
  · refine hpre (sqrtVal, isQR) _ ⟨true, by simpa [bit] using h1, ?_⟩
    rw [hsq, hsel true (by simpa [bit] using h1)]
    simp [selectPure]

open Std.Do in
/-- `sqrtFlagged`'s honest run accepts on an evaluable operand when `sqrtF`'s roots
are genuine and a rootless operand's non-residue twist has a root; the flag
reads the operand's residuosity and the value reads the advice's root of the
flag-selected operand. -/
private theorem sqrtFlagged_complete_spec [Field F] [DecidableEq F] {c : Type}
    [BasicSystem F c] [Checker F c] [LawfulChecker F c]
    (sqrtF : F → Option F) (nonResidue : F) (x : FVar F)
    (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (Q : PostCond (FVar F × BoolVar F)
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (x.eval env).isOk ∧
          ∀ xv, x.eval env = .ok xv → sqrtF xv = none →
            (sqrtF (nonResidue * xv)).isSome)
        (fun env r env' => ∀ xv, x.eval env = .ok xv →
          (↑r.2 : CVar F).eval env' = .ok (bit (sqrtF xv).isSome) ∧
          r.1.eval env' = .ok
            ((sqrtF (if (sqrtF xv).isSome then xv else nonResidue * xv)).getD 0))
        Q⦄
    (sqrtFlagged (c := Prover c) sqrtF nonResidue x)
    ⦃Q⦄ := by
  simp only [sqrtFlagged]
  mvcgen
  rename_i st hpre
  obtain ⟨⟨hokx, htw⟩, hk⟩ := hpre
  obtain ⟨xv, hx⟩ := CVar.evalOk hokx
  have hw₁ : isQRWit sqrtF x st.env = .ok (sqrtF xv).isSome := by
    rw [show isQRWit sqrtF x st.env
        = (fun v => (sqrtF v).isSome) <$> CVar.eval x st.env from rfl, hx]
    rfl
  refine ⟨by rw [hw₁]; rfl, fun isQR st₁ hrd₁ hle₁ => ?_⟩
  have hb₁ : (↑isQR : CVar F).eval st₁.env = .ok (bit (sqrtF xv).isSome) := hrd₁ _ hw₁
  have hx₁ : x.eval st₁.env = .ok xv := CVar.eval_le hle₁ hx
  mvcgen
  refine ⟨⟨ReadsBit.of_bit hb₁, by rw [hx₁]; rfl,
    by rw [CVar.eval_scale_ hx₁ nonResidue]; rfl⟩, fun xOrMx st₂ hrd₂ hle₂ => ?_⟩
  have hsel : xOrMx.eval st₂.env
      = .ok (if (sqrtF xv).isSome then xv else nonResidue * xv) := by
    simpa [selectPure] using hrd₂ _ _ _ hb₁ hx₁ (CVar.eval_scale_ hx₁ nonResidue)
  have hw₂ : sqrtWit sqrtF xOrMx st₂.env
      = .ok ((sqrtF (if (sqrtF xv).isSome then xv else nonResidue * xv)).getD 0) := by
    rw [show sqrtWit sqrtF xOrMx st₂.env
        = (fun v => (sqrtF v).getD 0) <$> CVar.eval xOrMx st₂.env from rfl, hsel]
    rfl
  mvcgen
  refine ⟨by rw [hw₂]; rfl, fun sqrtVal st₃ hrd₃ hle₃ => ?_⟩
  have hy₃ : sqrtVal.eval st₃.env
      = .ok ((sqrtF (if (sqrtF xv).isSome then xv else nonResidue * xv)).getD 0) :=
    hrd₃ _ hw₂
  have hsel₃ : xOrMx.eval st₃.env
      = .ok (if (sqrtF xv).isSome then xv else nonResidue * xv) :=
    CVar.eval_le hle₃ hsel
  mvcgen
  refine ⟨⟨by rw [hy₃]; rfl, by rw [hsel₃]; rfl, fun a b ha hb => ?_⟩,
    fun r st₄ hle₄ hf => ?_⟩
  · -- the advice root really squares to the selected operand
    rw [hy₃] at ha
    rw [hsel₃] at hb
    injection ha with ha
    injection hb with hb
    subst ha hb
    rcases hcase : sqrtF xv with _ | y
    · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (htw xv hx hcase)
      simp [hz, hroot _ z hz]
    · simp [hcase, hroot _ y hcase]
  · exact hk (sqrtVal, isQR) ⟨st₄.nv, st₄.env, hf⟩
      (fun xv' hx' => by
        rw [hx] at hx'
        injection hx' with hx'
        subst hx'
        exact ⟨CVar.eval_le ((hle₂.trans hle₃).trans hle₄) hb₁,
          CVar.eval_le hle₄ hy₃⟩)
      (((hle₁.trans hle₂).trans hle₃).trans hle₄)

open Std.Do in
/-- `groupMapCircuit` is sound: any satisfying valuation reads the result as an
on-curve pair (`y² = x³ + b`) whose abscissa is one of the three `potentialXs`
candidates at the operand — the constraints force a set flag, the first-flag
selectors are mutually exclusive boolean products, and the selected branch's
`sqrtFlagged` root is the ordinate. The advice `sqrtF` is universally quantified:
soundness never consults it. -/
theorem groupMapCircuit_spec [Field F] [DecidableEq F]
    (sqrtF : F → Option F) (params : GroupMapParams F) (t : FVar F)
    (Q : PostCond (AffinePoint (FVar F)) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AffinePoint (FVar F)) =>
        (r.x.val V = (potentialXs params (t.val V)).1
          ∨ r.x.val V = (potentialXs params (t.val V)).2.1
          ∨ r.x.val V = (potentialXs params (t.val V)).2.2) ∧
        r.y.val V * r.y.val V
          = r.x.val V * r.x.val V * r.x.val V + params.b) Q⦄
    (groupMapCircuit (c := KimchiConstraint F) sqrtF params t)
    ⦃Q⦄ := by
  simp only [groupMapCircuit]
  mvcgen
  rename_i s hpre
  intro t2 _ ht2
  mvcgen
  intro alphaInv _ halphaInv
  mvcgen
  intro alpha _ halpha
  mvcgen
  intro t4 _ ht4
  mvcgen
  intro t4Alpha _ ht4Alpha
  mvcgen
  intro temp1 _ htemp1
  mvcgen
  intro t2Inv _ ht2Inv
  mvcgen
  intro t2PlusFuSq _ ht2PlusFuSq
  mvcgen
  intro temp2a _ htemp2a
  mvcgen
  intro temp2 _ htemp2
  mvcgen
  intro xSq1 _ hxSq1
  mvcgen
  intro xCu1 _ hxCu1
  mvcgen
  intro sf1 _ hsf1
  mvcgen
  intro xSq2 _ hxSq2
  mvcgen
  intro xCu2 _ hxCu2
  mvcgen
  intro sf2 _ hsf2
  mvcgen
  intro xSq3 _ hxSq3
  mvcgen
  intro xCu3 _ hxCu3
  mvcgen
  intro sf3 _ hsf3
  mvcgen
  intro _ _ hnz
  mvcgen
  intro x2First _ hx2First
  mvcgen
  intro nb2AndB3 _ hnb2AndB3
  mvcgen
  intro x3First _ hx3First
  mvcgen
  intro t3y _ ht3y
  mvcgen
  intro t2y _ ht2y
  mvcgen
  intro t1y _ ht1y
  mvcgen
  intro t3x _ ht3x
  mvcgen
  intro t2x _ ht2x
  mvcgen
  intro t1x _ ht1x
  mvcgen
  obtain ⟨bb1, hb1, hy1⟩ := hsf1
  obtain ⟨bb2, hb2, hy2⟩ := hsf2
  obtain ⟨bb3, hb3, hy3⟩ := hsf3
  -- the candidate values, from the arithmetic grants
  have hval : ∀ (a : F), (CVar.const a : CVar F).val s.V = a := fun _ => rfl
  have hx1v : (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) temp1).val s.V
      = (potentialXs params (t.val s.V)).1 := by
    simp only [potentialXs, CVar.val_sub_, hval, htemp1, ht4Alpha, ht4, halpha,
      halphaInv, ht2, CVar.val_add_]
  have hx2v : (CVar.sub_ (.const (-params.u))
        (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) temp1)).val s.V
      = (potentialXs params (t.val s.V)).2.1 := by
    simp only [potentialXs, CVar.val_sub_, hval, htemp1, ht4Alpha, ht4, halpha,
      halphaInv, ht2, CVar.val_add_]
  have hx3v : (CVar.sub_ (.const params.u) temp2).val s.V
      = (potentialXs params (t.val s.V)).2.2 := by
    simp only [potentialXs, CVar.val_sub_, hval, htemp2, htemp2a, ht2PlusFuSq,
      ht2Inv, halpha, halphaInv, ht2, CVar.val_add_]
  -- the flag bits force exactly one first-flag selector
  have hnb1 : (↑(Snarky.not sf1.2) : CVar F).val s.V = bit (!bb1) := by
    rcases bb1 <;> simp [Snarky.not, circuitVal, CVar.val, hb1, bit]
  have hnb2 : (↑(Snarky.not sf2.2) : CVar F).val s.V = bit (!bb2) := by
    rcases bb2 <;> simp [Snarky.not, circuitVal, CVar.val, hb2, bit]
  have hs2 := hx2First (!bb1) bb2 hnb1 hb2
  have hs3 := hx3First (!bb1) (!bb2 && bb3) hnb1 (hnb2AndB3 (!bb2) bb3 hnb2 hb3)
  -- select the branch: the sums collapse under the selector bits
  rcases bb1 with _ | _
  · rcases bb2 with _ | _
    · rcases bb3 with _ | _
      · -- all flags clear: the asserted flag sum is zero
        exact absurd (by simp [circuitVal, hb1, hb2, hb3, bit]) hnz
      · -- third candidate
        refine hpre _ _ (Or.inr (Or.inr ?_)) ?_
        · rw [← hx3v]
          simp [circuitVal, CVar.val, ht1x, ht2x, ht3x, hb1, hs2, hs3, bit]
        · simpa [circuitVal, CVar.val, ht1x, ht2x, ht3x, ht1y, ht2y, ht3y, hb1,
            hs2, hs3, bit, hxCu3, hxSq3] using hy3
    · -- second candidate
      refine hpre _ _ (Or.inr (Or.inl ?_)) ?_
      · rw [← hx2v]
        simp [circuitVal, CVar.val, ht1x, ht2x, ht3x, hb1, hs2, hs3, bit]
      · simpa [circuitVal, CVar.val, ht1x, ht2x, ht3x, ht1y, ht2y, ht3y, hb1,
          hs2, hs3, bit, hxCu2, hxSq2] using hy2
  · -- first candidate, whatever the later flags
    refine hpre _ _ (Or.inl ?_) ?_
    · rw [← hx1v]
      simp [circuitVal, CVar.val, ht1x, ht2x, ht3x, hb1, hs2, hs3, bit]
    · simpa [circuitVal, CVar.val, ht1x, ht2x, ht3x, ht1y, ht2y, ht3y, hb1,
        hs2, hs3, bit, hxCu1, hxSq1] using hy1

open Std.Do in
/-- `groupMapCircuit`'s honest run accepts and the result reads the pure map's point.
Hypotheses: the operand evaluates; its `alphaInv` product is nonzero (the `div`
divisor); some candidate ordinate square has a root — Shallue–van de Woestijne,
taken as a hypothesis; `sqrtF`'s roots are genuine; a rootless value's non-residue
twist has a root; and `2, 3 ≠ 0` price the flag-sum assertion. -/
theorem groupMapCircuit_complete_spec [Field F] [DecidableEq F] {c : Type}
    [BasicSystem F c] [Checker F c] [LawfulChecker F c]
    (sqrtF : F → Option F) (params : GroupMapParams F) (t : FVar F)
    (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : ∀ a, sqrtF a = none → (sqrtF (params.nonResidue * a)).isSome)
    (htwo : (2 : F) ≠ 0) (hthree : (3 : F) ≠ 0)
    (Q : PostCond (AffinePoint (FVar F))
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (t.eval env).isOk ∧
          ∀ tv, t.eval env = .ok tv →
            (tv * tv + params.fu) * (tv * tv) ≠ 0 ∧
            ((sqrtF (ySquared params (potentialXs params tv).1)).isSome ∨
              (sqrtF (ySquared params (potentialXs params tv).2.1)).isSome ∨
              (sqrtF (ySquared params (potentialXs params tv).2.2)).isSome))
        (fun env r env' => ∀ tv, t.eval env = .ok tv →
          r.x.eval env' = .ok (groupMapPure sqrtF params tv).1 ∧
          r.y.eval env' = .ok (groupMapPure sqrtF params tv).2)
        Q⦄
    (groupMapCircuit (c := Prover c) sqrtF params t)
    ⦃Q⦄ := by
  simp only [groupMapCircuit]
  mvcgen
  rename_i st hpre
  obtain ⟨⟨hokt, hcond⟩, hk⟩ := hpre
  obtain ⟨tv, ht⟩ := CVar.evalOk hokt
  obtain ⟨hne, hdisj⟩ := hcond tv ht
  simp only [potentialXs, ySquared] at hdisj
  have hcst : ∀ (a : F) (env : Assignments F),
      (CVar.const a : CVar F).eval env = .ok a := fun _ _ => rfl
  refine ⟨⟨by rw [ht]; rfl, by rw [ht]; rfl⟩, fun t2 s1 g1 l1 => ?_⟩
  have h2 := g1 tv tv ht ht
  mvcgen
  refine ⟨⟨by rw [CVar.eval_add_ h2 rfl]; rfl, by rw [h2]; rfl⟩,
    fun alphaInv s2 g2 l2 => ?_⟩
  have hAI := g2 _ _ (CVar.eval_add_ h2 rfl) h2
  mvcgen
  refine ⟨⟨rfl, by rw [hAI]; rfl, fun yv hyv => ?_⟩, fun alpha s3 g3 l3 => ?_⟩
  · rw [hAI] at hyv
    injection hyv with hyv
    exact hyv ▸ hne
  have hAL := g3 _ _ (hcst _ _) hAI
  mvcgen
  have h2c := CVar.eval_le (l2.trans l3) h2
  refine ⟨⟨by rw [h2c]; rfl, by rw [h2c]; rfl⟩, fun t4 s4 g4 l4 => ?_⟩
  have h4 := g4 _ _ h2c h2c
  mvcgen
  have hALc := CVar.eval_le l4 hAL
  refine ⟨⟨by rw [h4]; rfl, by rw [hALc]; rfl⟩, fun t4A s5 g5 l5 => ?_⟩
  have h4A := g5 _ _ h4 hALc
  mvcgen
  refine ⟨⟨by rw [h4A]; rfl, rfl⟩, fun tm1 s6 g6 l6 => ?_⟩
  have hT1 := g6 _ _ h4A rfl
  mvcgen
  have hALd := CVar.eval_le (l5.trans l6) hALc
  have h2d := CVar.eval_le (l4.trans (l5.trans l6)) h2c
  refine ⟨⟨by rw [hALd]; rfl, by rw [CVar.eval_add_ h2d rfl]; rfl⟩,
    fun t2I s7 g7 l7 => ?_⟩
  have hT2I := g7 _ _ hALd (CVar.eval_add_ h2d rfl)
  mvcgen
  have h2e := CVar.eval_le l7 h2d
  refine ⟨⟨by rw [CVar.eval_add_ h2e rfl]; rfl, by rw [CVar.eval_add_ h2e rfl]; rfl⟩,
    fun tFS s8 g8 l8 => ?_⟩
  have hFS := g8 _ _ (CVar.eval_add_ h2e rfl) (CVar.eval_add_ h2e rfl)
  mvcgen
  have hT2Ic := CVar.eval_le l8 hT2I
  refine ⟨⟨by rw [hFS]; rfl, by rw [hT2Ic]; rfl⟩, fun tm2a s9 g9 l9 => ?_⟩
  have hT2a := g9 _ _ hFS hT2Ic
  mvcgen
  refine ⟨⟨by rw [hT2a]; rfl, rfl⟩, fun tm2 s10 g10 l10 => ?_⟩
  have hT2 := g10 _ _ hT2a rfl
  mvcgen
  have hT1c := CVar.eval_le (l7.trans (l8.trans (l9.trans l10))) hT1
  have hX1 := CVar.eval_sub_ (hcst params.sqrtNeg3U2MinusUOver2 _) hT1c
  set X1 : F := params.sqrtNeg3U2MinusUOver2
    - tv * tv * (tv * tv) * (1 / ((tv * tv + params.fu) * (tv * tv)))
      * params.sqrtNeg3U2 with hX1d
  refine ⟨⟨by rw [hX1]; rfl, by rw [hX1]; rfl⟩, fun q1 s11 g11 l11 => ?_⟩
  have hQ1 := g11 _ _ hX1 hX1
  mvcgen
  have hX1c := CVar.eval_le l11 hX1
  refine ⟨⟨by rw [hQ1]; rfl, by rw [hX1c]; rfl⟩, fun cu1 s12 g12 l12 => ?_⟩
  have hC1 := g12 _ _ hQ1 hX1c
  mvcgen
  refine sqrtFlagged_complete_spec (c := c) sqrtF params.nonResidue
    (CVar.add_ cu1 (.const params.b)) hroot _ _
    ⟨⟨by rw [CVar.eval_add_ hC1 (hcst _ _)]; rfl, fun v _ hnone => htwist v hnone⟩,
      fun sf1 s13 g13 l13 => ?_⟩
  obtain ⟨y1, b1⟩ := sf1
  obtain ⟨hB1, hY1⟩ := g13 _ (CVar.eval_add_ hC1 (hcst _ _))
  mvcgen
  have hX1e := CVar.eval_le (l12.trans l13) hX1c
  have hX2 := CVar.eval_sub_ (hcst (-params.u) _) hX1e
  refine ⟨⟨by rw [hX2]; rfl, by rw [hX2]; rfl⟩, fun q2 s14 g14 l14 => ?_⟩
  have hQ2 := g14 _ _ hX2 hX2
  mvcgen
  have hX2c := CVar.eval_le l14 hX2
  refine ⟨⟨by rw [hQ2]; rfl, by rw [hX2c]; rfl⟩, fun cu2 s15 g15 l15 => ?_⟩
  have hC2 := g15 _ _ hQ2 hX2c
  mvcgen
  refine sqrtFlagged_complete_spec (c := c) sqrtF params.nonResidue
    (CVar.add_ cu2 (.const params.b)) hroot _ _
    ⟨⟨by rw [CVar.eval_add_ hC2 (hcst _ _)]; rfl, fun v _ hnone => htwist v hnone⟩,
      fun sf2 s16 g16 l16 => ?_⟩
  obtain ⟨y2, b2⟩ := sf2
  obtain ⟨hB2, hY2⟩ := g16 _ (CVar.eval_add_ hC2 (hcst _ _))
  mvcgen
  have hT2c := CVar.eval_le
    (l11.trans (l12.trans (l13.trans (l14.trans (l15.trans l16))))) hT2
  have hX3 := CVar.eval_sub_ (hcst params.u _) hT2c
  set X3 : F := params.u
    - (tv * tv + params.fu) * (tv * tv + params.fu)
      * (1 / ((tv * tv + params.fu) * (tv * tv)) * (tv * tv + params.fu))
      * params.inv3U2 with hX3d
  refine ⟨⟨by rw [hX3]; rfl, by rw [hX3]; rfl⟩, fun q3 s17 g17 l17 => ?_⟩
  have hQ3 := g17 _ _ hX3 hX3
  mvcgen
  have hX3c := CVar.eval_le l17 hX3
  refine ⟨⟨by rw [hQ3]; rfl, by rw [hX3c]; rfl⟩, fun cu3 s18 g18 l18 => ?_⟩
  have hC3 := g18 _ _ hQ3 hX3c
  mvcgen
  refine sqrtFlagged_complete_spec (c := c) sqrtF params.nonResidue
    (CVar.add_ cu3 (.const params.b)) hroot _ _
    ⟨⟨by rw [CVar.eval_add_ hC3 (hcst _ _)]; rfl, fun v _ hnone => htwist v hnone⟩,
      fun sf3 s19 g19 l19 => ?_⟩
  obtain ⟨y3, b3⟩ := sf3
  obtain ⟨hB3, hY3⟩ := g19 _ (CVar.eval_add_ hC3 (hcst _ _))
  mvcgen
  have hB1c := CVar.eval_le
    (l14.trans (l15.trans (l16.trans (l17.trans (l18.trans l19))))) hB1
  have hB2c := CVar.eval_le (l17.trans (l18.trans l19)) hB2
  have hSum := CVar.eval_add_ (CVar.eval_add_ hB1c hB2c) hB3
  refine ⟨⟨by rw [hSum]; rfl, fun vv hvv => ?_⟩, fun u20 s20 l20 => ?_⟩
  · rw [hSum] at hvv
    injection hvv with hvv
    subst hvv
    cases hb1c : (sqrtF (X1 * X1 * X1 + params.b)).isSome <;>
      cases hb2c : (sqrtF ((-params.u - X1) * (-params.u - X1) * (-params.u - X1)
        + params.b)).isSome <;>
      cases hb3c : (sqrtF (X3 * X3 * X3 + params.b)).isSome <;>
      simp [hb1c, hb2c, hb3c, bit] at hdisj ⊢ <;>
      first
      | exact one_ne_zero
      | (rw [one_add_one_eq_two]; exact htwo)
      | (rw [one_add_one_eq_two, two_add_one_eq_three]; exact hthree)
  mvcgen
  have hB1e := CVar.eval_le l20 hB1c
  have hB2e := CVar.eval_le l20 hB2c
  have hNB1 := not_eval (bb := (sqrtF (X1 * X1 * X1 + params.b)).isSome) hB1e
  refine ⟨⟨by rw [hNB1]; rfl, by rw [hB2e]; rfl⟩, fun a1 s21 g21 l21 => ?_⟩
  have hA1 := g21 _ _ hNB1 hB2e
  mvcgen
  have hB2f := CVar.eval_le l21 hB2e
  have hB3c := CVar.eval_le (l20.trans l21) hB3
  have hNB2 := not_eval (bb := (sqrtF ((-params.u - X1) * (-params.u - X1)
    * (-params.u - X1) + params.b)).isSome) hB2f
  refine ⟨⟨by rw [hNB2]; rfl, by rw [hB3c]; rfl⟩, fun a2 s22 g22 l22 => ?_⟩
  have hA2 := g22 _ _ hNB2 hB3c
  mvcgen
  have hB1f := CVar.eval_le (l21.trans l22) hB1e
  have hNB1' := not_eval (bb := (sqrtF (X1 * X1 * X1 + params.b)).isSome) hB1f
  refine ⟨⟨by rw [hNB1']; rfl, by rw [hA2]; rfl⟩, fun a3 s23 g23 l23 => ?_⟩
  have hA3 := g23 _ _ hNB1' hA2
  mvcgen
  have hY3c := CVar.eval_le (l20.trans (l21.trans (l22.trans l23))) hY3
  refine ⟨⟨by rw [hA3]; rfl, by rw [hY3c]; rfl⟩, fun m3y s24 g24 l24 => ?_⟩
  have hT3y := g24 _ _ hA3 hY3c
  mvcgen
  have hA1c := CVar.eval_le (l22.trans (l23.trans l24)) hA1
  have hY2c := CVar.eval_le (l17.trans (l18.trans (l19.trans (l20.trans
    (l21.trans (l22.trans (l23.trans l24))))))) hY2
  refine ⟨⟨by rw [hA1c]; rfl, by rw [hY2c]; rfl⟩, fun m2y s25 g25 l25 => ?_⟩
  have hT2y := g25 _ _ hA1c hY2c
  mvcgen
  have hB1g := CVar.eval_le (l23.trans (l24.trans l25)) hB1f
  have hY1c := CVar.eval_le (l14.trans (l15.trans (l16.trans (l17.trans (l18.trans
    (l19.trans (l20.trans (l21.trans (l22.trans (l23.trans
    (l24.trans l25))))))))))) hY1
  refine ⟨⟨by rw [hB1g]; rfl, by rw [hY1c]; rfl⟩, fun m1y s26 g26 l26 => ?_⟩
  have hT1y := g26 _ _ hB1g hY1c
  mvcgen
  have hA3d := CVar.eval_le (l24.trans (l25.trans l26)) hA3
  have hX3e := CVar.eval_le (l17.trans (l18.trans (l19.trans (l20.trans (l21.trans
    (l22.trans (l23.trans (l24.trans (l25.trans l26))))))))) hX3
  refine ⟨⟨by rw [hA3d]; rfl, by rw [hX3e]; rfl⟩, fun m3x s27 g27 l27 => ?_⟩
  have hT3x := g27 _ _ hA3d hX3e
  mvcgen
  have hA1d := CVar.eval_le (l25.trans (l26.trans l27)) hA1c
  have hX2e := CVar.eval_le (l14.trans (l15.trans (l16.trans (l17.trans (l18.trans
    (l19.trans (l20.trans (l21.trans (l22.trans (l23.trans (l24.trans (l25.trans
    (l26.trans l27))))))))))))) hX2
  refine ⟨⟨by rw [hA1d]; rfl, by rw [hX2e]; rfl⟩, fun m2x s28 g28 l28 => ?_⟩
  have hT2x := g28 _ _ hA1d hX2e
  mvcgen
  have hB1h := CVar.eval_le (l26.trans (l27.trans l28)) hB1g
  have hX1f := CVar.eval_le (l14.trans (l15.trans (l16.trans (l17.trans (l18.trans
    (l19.trans (l20.trans (l21.trans (l22.trans (l23.trans (l24.trans (l25.trans
    (l26.trans (l27.trans l28)))))))))))))) hX1e
  refine ⟨⟨by rw [hB1h]; rfl, by rw [hX1f]; rfl⟩, fun m1x s29 g29 l29 => ?_⟩
  have hT1x := g29 _ _ hB1h hX1f
  intro hf
  have hT2xc := CVar.eval_le l29 hT2x
  have hT3xc := CVar.eval_le (l28.trans l29) hT3x
  have hT1yc := CVar.eval_le (l27.trans (l28.trans l29)) hT1y
  have hT2yc := CVar.eval_le (l26.trans (l27.trans (l28.trans l29))) hT2y
  have hT3yc := CVar.eval_le (l25.trans (l26.trans (l27.trans (l28.trans l29)))) hT3y
  have lAll : st.env.Le s29.env :=
    l1.trans (l2.trans (l3.trans (l4.trans (l5.trans (l6.trans (l7.trans (l8.trans
      (l9.trans (l10.trans (l11.trans (l12.trans (l13.trans (l14.trans (l15.trans
      (l16.trans (l17.trans (l18.trans (l19.trans (l20.trans (l21.trans (l22.trans
      (l23.trans (l24.trans (l25.trans (l26.trans (l27.trans (l28.trans
        l29)))))))))))))))))))))))))))
  refine hk ⟨_, _⟩ ⟨s29.nv, s29.env, hf⟩ (fun tv' ht' => ?_) lAll
  rw [ht] at ht'
  injection ht' with ht'
  subst ht'
  refine ⟨?_, ?_⟩
  · rw [CVar.eval_add_ (CVar.eval_add_ hT1x hT2xc) hT3xc]
    simp only [groupMapPure, potentialXs, ySquared]
    rw [← hX1d, ← hX3d]
    rcases hc1 : sqrtF (X1 * X1 * X1 + params.b) with _ | w1 <;>
      rcases hc2 : sqrtF ((-params.u - X1) * (-params.u - X1) * (-params.u - X1)
        + params.b) with _ | w2 <;>
      rcases hc3 : sqrtF (X3 * X3 * X3 + params.b) with _ | w3 <;>
      simp [hc1, hc2, hc3, bit] at hdisj ⊢
  · rw [CVar.eval_add_ (CVar.eval_add_ hT1yc hT2yc) hT3yc]
    simp only [groupMapPure, potentialXs, ySquared]
    rw [← hX1d, ← hX3d]
    rcases hc1 : sqrtF (X1 * X1 * X1 + params.b) with _ | w1 <;>
      rcases hc2 : sqrtF ((-params.u - X1) * (-params.u - X1) * (-params.u - X1)
        + params.b) with _ | w2 <;>
      rcases hc3 : sqrtF (X3 * X3 * X3 + params.b) with _ | w3 <;>
      simp [hc1, hc2, hc3, bit] at hdisj ⊢

end Snarky.Kimchi
