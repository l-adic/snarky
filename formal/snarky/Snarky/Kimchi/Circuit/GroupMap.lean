import Snarky.DSL.Field
import Snarky.DSL.Assert
import Snarky.DSL.Boolean
import Snarky.Kimchi.Semantics
import Poseidon.GroupMap

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

The value level (`potentialXs`, `groupMapPure`) is identified with the wire verifier's
fixture-validated map: `groupMapPure_toGroup` proves it computes
`Poseidon.GroupMap.toGroup` — the `U`-base derivation the kimchi verifier runs — at any
wire `Spec`. The generic laws quote the module's own pure model; the wire section
restates them with the wire map itself as the spec.

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

open Std.Do in
/-- The flagged root's contract: the flag is a bit, and the root squares to the operand
where the flag is set, to its non-residue twist where it is clear. -/
@[spec] private theorem sqrtFlagged_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (sqrtF : F → Option F) (nonResidue : F) (x : FVar F) :
    ⦃⌜True⌝⦄
    sqrtFlagged (c := Builder V c) sqrtF nonResidue x
    ⦃⇓ r _ => ⌜∃ bb : Bool, (↑r.2 : CVar F).val V = bit bb ∧
      r.1.val V * r.1.val V = if bb then x.val V else nonResidue * x.val V⌝⦄ := by
  simp only [sqrtFlagged, select_fvar]
  mvcgen
  rename_i _ isQR _ hbool _ _ hsel _ _ _ _ _ hsq
  obtain ⟨bb, hbb⟩ := hbool
  refine ⟨bb, hbb, ?_⟩
  rw [hsq, hsel bb hbb, CVar.val_scale_]

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

open Std.Do in
/-- **Soundness.** Any satisfying valuation reads the result as an on-curve pair
(`y² = x³ + b`) whose abscissa is one of the three `potentialXs` candidates at the
operand: the constraints force a set flag, the first-flag selectors are mutually
exclusive boolean products, and the selected branch's `sqrtFlagged` root is the
ordinate. The advice is universally quantified — soundness never consults it. -/
theorem groupMapCircuit_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (sqrtF : F → Option F) (params : GroupMapParams F) (t : FVar F) :
    ⦃⌜True⌝⦄
    groupMapCircuit (c := Builder V c) sqrtF params t
    ⦃⇓ r _ => ⌜(r.x.val V = (potentialXs params (t.val V)).1 ∨
        r.x.val V = (potentialXs params (t.val V)).2.1 ∨
        r.x.val V = (potentialXs params (t.val V)).2.2) ∧
      r.y.val V * r.y.val V = ySquared params (r.x.val V)⌝⦄ := by
  simp only [groupMapCircuit]
  mvcgen
  rename_i _ t2 _ ht2 alphaInv _ halphaInv alpha _ halpha t4 _ ht4 t4Alpha _ ht4Alpha temp1 _
    htemp1 t2Inv _ ht2Inv t2PlusFuSq _ ht2PlusFuSq temp2a _ htemp2a temp2 _ htemp2 xSq1 _ hxSq1
    xCu1 _ hxCu1 sf1 _ hsf1 xSq2 _ hxSq2 xCu2 _ hxCu2 sf2 _ hsf2 xSq3 _ hxSq3 xCu3 _ hxCu3 sf3 _
    hsf3 _ _ hnz x2First _ hx2First nb2AndB3 _ hnb2AndB3 x3First _ hx3First t3y _ ht3y t2y _
    ht2y t1y _ ht1y t3x _ ht3x t2x _ ht2x t1x _ ht1x
  obtain ⟨bb1, hb1, hy1⟩ := hsf1
  obtain ⟨bb2, hb2, hy2⟩ := hsf2
  obtain ⟨bb3, hb3, hy3⟩ := hsf3
  have hval : ∀ a : F, (CVar.const a : CVar F).val V = a := fun _ => rfl
  -- the three candidates, read off the arithmetic grants
  have hx1v : ((CVar.const params.sqrtNeg3U2MinusUOver2).sub_ temp1).val V
      = (potentialXs params (t.val V)).1 := by
    simp only [potentialXs, CVar.val_sub_, CVar.val_add_, hval, htemp1, ht4Alpha, ht4,
      halpha, halphaInv, ht2]
  have hx2v : ((CVar.const (-params.u)).sub_
        ((CVar.const params.sqrtNeg3U2MinusUOver2).sub_ temp1)).val V
      = (potentialXs params (t.val V)).2.1 := by
    simp only [potentialXs, CVar.val_sub_, CVar.val_add_, hval, htemp1, ht4Alpha, ht4,
      halpha, halphaInv, ht2]
  have hx3v : ((CVar.const params.u).sub_ temp2).val V
      = (potentialXs params (t.val V)).2.2 := by
    simp only [potentialXs, CVar.val_sub_, CVar.val_add_, hval, htemp2, htemp2a,
      ht2PlusFuSq, ht2Inv, halpha, halphaInv, ht2]
  -- the flags force exactly one first-flag selector
  have hs2 := hx2First (!bb1) bb2 (not_val hb1) hb2
  have hs3 := hx3First (!bb1) (!bb2 && bb3) (not_val hb1)
    (hnb2AndB3 (!bb2) bb3 (not_val hb2) hb3)
  rcases bb1 with _ | _
  · rcases bb2 with _ | _
    · rcases bb3 with _ | _
      · -- every flag clear: the asserted flag sum is zero
        exact absurd (by simp [CVar.val_add_, hb1, hb2, hb3, bit]) hnz
      · refine ⟨Or.inr (Or.inr ?_), ?_⟩
        · rw [← hx3v]
          simp [CVar.val_add_, ht1x, ht2x, ht3x, hb1, hs2, hs3, bit]
        · simpa [CVar.val_add_, ySquared, ht1x, ht2x, ht3x, ht1y, ht2y, ht3y, hb1,
            hs2, hs3, bit, hxCu3, hxSq3] using hy3
    · refine ⟨Or.inr (Or.inl ?_), ?_⟩
      · rw [← hx2v]
        simp [CVar.val_add_, ht1x, ht2x, ht3x, hb1, hs2, hs3, bit]
      · simpa [CVar.val_add_, ySquared, ht1x, ht2x, ht3x, ht1y, ht2y, ht3y, hb1,
          hs2, hs3, bit, hxCu2, hxSq2] using hy2
  · refine ⟨Or.inl ?_, ?_⟩
    · rw [← hx1v]
      simp [CVar.val_add_, ht1x, ht2x, ht3x, hb1, hs2, hs3, bit]
    · simpa [CVar.val_add_, ySquared, ht1x, ht2x, ht3x, ht1y, ht2y, ht3y, hb1,
        hs2, hs3, bit, hxCu1, hxSq1] using hy1

/-! ## Completeness

The honest run, step by step in the DSL's reading currency: each gate's law takes its
operands' readings and gives the result's, and `CircuitType.ReadsAs.mono` carries a
reading past the gates that follow. -/

/-- The ordinate-square block's honest run: two `mul`s and a constant add. -/
private theorem ySquared_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (params : GroupMapParams F)
    (x : FVar F) (xv : F) :
    Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := F) st x xv)
      (do let xSq ← mul (c := c) x x
          let xCu ← mul xSq x
          pure (CVar.add_ xCu (CVar.const params.b)))
      (fun r st' => CircuitType.ReadsAs (val := F) st' r (ySquared params xv)) := by
  intro st hx
  obtain ⟨xSq, st₁, hrun₁, hsat₁, h₁⟩ := mul_complete (c := c) x x xv xv st ⟨hx, hx⟩
  obtain ⟨xCu, st₂, hrun₂, hsat₂, h₂⟩ :=
    mul_complete (c := c) xSq x (xv * xv) xv st₁ ⟨h₁, hx.mono hrun₁.nv_le hrun₁.le⟩
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar] at h₂ ⊢
  exact ⟨_, st₂, hrun₁.bind (hrun₂.bind rfl), fun hnv hle =>
    Sat.bind hrun₁ (hsat₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle))
      (Sat.bind hrun₂ (hsat₂ hnv hle) Sat.pure),
    CVar.Scoped.add_ h₂.1 trivial, by rw [CVar.val_add_, h₂.2]; rfl⟩

/-- **The flagged root's honest run.** With genuine roots, and a rootless operand's
non-residue twist rooted, the run accepts: the flag reads the operand's residuosity and
the value reads the advice's root of the flag-selected operand. -/
private theorem sqrtFlagged_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (sqrtF : F → Option F) (nonResidue : F)
    (x : FVar F) (xv : F) (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : sqrtF xv = none → (sqrtF (nonResidue * xv)).isSome) :
    Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := F) st x xv)
      (sqrtFlagged (c := c) sqrtF nonResidue x)
      (fun r st' => CircuitType.ReadsAs (val := Bool) st' r.2 (sqrtF xv).isSome ∧
        CircuitType.ReadsAs (val := F) st' r.1
          ((sqrtF (if (sqrtF xv).isSome then xv else nonResidue * xv)).getD 0)) := by
  intro st hx
  have hx' := hx
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar] at hx'
  obtain ⟨hscx, hvx⟩ := hx'
  -- the residuosity flag
  obtain ⟨isQR, st₁, hrun₁, hsat₁, hnv₁, hle₁, hsc₁, hrd₁⟩ :=
    witness_complete (c := c) (val := Bool) (isQRWit sqrtF x) (st := st)
      (v := (sqrtF xv).isSome)
      (by
        simp only [isQRWit, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run hscx, hvx, Except.bind]
        rfl)
  -- the flag-selected operand
  obtain ⟨xOrMx, st₂, hrun₂, hsat₂, hsel⟩ :=
    selectField_complete (c := c) isQR x (CVar.scale_ nonResidue x) (sqrtF xv).isSome
      xv (nonResidue * xv) st₁
      ⟨⟨hsc₁, hrd₁⟩, hx.mono hnv₁ hle₁,
        by
          simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]
          exact ⟨CVar.Scoped.scale_ (hscx.mono hnv₁),
            by rw [CVar.val_scale_, CVar.val_of_le hle₁ hscx, hvx]⟩⟩
  have hle₂ := hrun₂.le
  have hnv₂ := hrun₂.nv_le
  have hsel' := hsel
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar] at hsel'
  -- the advice's root really is one
  have hsome : (sqrtF (if (sqrtF xv).isSome then xv else nonResidue * xv)).isSome := by
    rcases hcase : sqrtF xv with _ | y
    · simpa [hcase] using htwist hcase
    · simp [hcase]
  have hsq : ((sqrtF (if (sqrtF xv).isSome then xv else nonResidue * xv)).getD 0)
      * ((sqrtF (if (sqrtF xv).isSome then xv else nonResidue * xv)).getD 0)
      = (if (sqrtF xv).isSome then xv else nonResidue * xv) := by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsome
    rw [hy]
    exact hroot _ y hy
  -- the root
  obtain ⟨sqrtVal, st₃, hrun₃, hsat₃, hnv₃, hle₃, hsc₃, hrd₃⟩ :=
    witness_complete (c := c) (val := F) (sqrtWit sqrtF xOrMx) (st := st₂)
      (v := (sqrtF (if (sqrtF xv).isSome then xv else nonResidue * xv)).getD 0)
      (by
        simp only [sqrtWit, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run hsel'.1, hsel'.2, Except.bind]
        rfl)
  -- the square row
  obtain ⟨u, st₄, hrun₄, hsat₄, -⟩ :=
    assertSquare_complete (c := c) sqrtVal xOrMx _ _ hsq st₃
      ⟨⟨hsc₃, hrd₃⟩, hsel.mono hnv₃ hle₃⟩
  have hle₄ := hrun₄.le
  have hnv₄ := hrun₄.nv_le
  refine ⟨(sqrtVal, isQR), st₄,
    hrun₁.bind (hrun₂.bind (hrun₃.bind (hrun₄.bind rfl))), fun hnv hle =>
      Sat.bind hrun₁ (hsat₁ ?_ ?_) (Sat.bind hrun₂ (hsat₂ ?_ ?_)
        (Sat.bind hrun₃ (hsat₃ ?_ ?_) (Sat.bind hrun₄ (hsat₄ hnv hle) Sat.pure))), ?_, ?_⟩
  · exact Nat.le_trans (Nat.le_trans hnv₂ (Nat.le_trans hnv₃ hnv₄)) hnv
  · exact ((hle₂.trans hle₃).trans hle₄).trans hle
  · exact Nat.le_trans (Nat.le_trans hnv₃ hnv₄) hnv
  · exact (hle₃.trans hle₄).trans hle
  · exact Nat.le_trans hnv₄ hnv
  · exact hle₄.trans hle
  · exact CircuitType.ReadsAs.mono (val := Bool)
      (Nat.le_trans hnv₂ (Nat.le_trans hnv₃ hnv₄)) ((hle₂.trans hle₃).trans hle₄)
      ⟨hsc₁, hrd₁⟩
  · exact CircuitType.ReadsAs.mono (val := F) hnv₄ hle₄ ⟨hsc₃, hrd₃⟩

/-- At least one flag set makes the asserted flag sum nonzero — where the characteristic
is neither `2` nor `3`, which is what prices the sums `2` and `3`. -/
private theorem flagSum [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∀ a b c : Bool, (a = true ∨ b = true ∨ c = true) →
      (bit a : F) + bit b + bit c ≠ 0 := by
  rintro a b c h
  cases a <;> cases b <;> cases c <;> simp_all [bit]
  all_goals
    first
      | (rw [show (1 : F) + 1 = 2 from by norm_num]; exact h2)
      | (rw [show (1 : F) + 1 + 1 = 3 from by norm_num]; exact h3)

/-- **Completeness.** The honest run accepts and its result reads the pure map's point.
The hypotheses: the operand reads a value whose `alphaInv` product is nonzero (the `div`
divisor); some candidate's ordinate square has a root — Shallue–van de Woestijne, taken
as a hypothesis; `sqrtF`'s roots are genuine; a rootless value's non-residue twist has a
root; and `2, 3 ≠ 0` price the flag-sum assertion. -/
theorem groupMapCircuit_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c]
    (sqrtF : F → Option F) (params : GroupMapParams F) (t : FVar F) (tv : F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hne : (tv * tv + params.fu) * (tv * tv) ≠ 0)
    (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : ∀ a, sqrtF a = none → (sqrtF (params.nonResidue * a)).isSome)
    (hsome : (sqrtF (ySquared params (potentialXs params tv).1)).isSome = true ∨
      (sqrtF (ySquared params (potentialXs params tv).2.1)).isSome = true ∨
      (sqrtF (ySquared params (potentialXs params tv).2.2)).isSome = true) :
    Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := F) st t tv)
      (groupMapCircuit (c := c) sqrtF params t)
      (fun r st' =>
        CircuitType.ReadsAs (val := F) st' r.x (groupMapPure sqrtF params tv).1 ∧
        CircuitType.ReadsAs (val := F) st' r.y (groupMapPure sqrtF params tv).2) := by
  -- readings of the pure combinations, proof-local
  have RC : ∀ (a : F) (s : ProverState F),
      CircuitType.ReadsAs (val := F) s (CVar.const a) a := fun _ _ =>
    ⟨CircuitType.scoped_fvar.mpr trivial, CircuitType.reads_fvar.mpr rfl⟩
  have RS : ∀ {s : ProverState F} {u : FVar F} {uv a : F},
      CircuitType.ReadsAs (val := F) s u uv →
      CircuitType.ReadsAs (val := F) s ((CVar.const a).sub_ u) (a - uv) := by
    intro s u uv a h
    simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar] at h ⊢
    exact ⟨CVar.Scoped.sub_ trivial h.1, by rw [CVar.val_sub_, h.2]; rfl⟩
  have RA : ∀ {s : ProverState F} {u : FVar F} {uv a : F},
      CircuitType.ReadsAs (val := F) s u uv →
      CircuitType.ReadsAs (val := F) s (u.add_ (CVar.const a)) (uv + a) := by
    intro s u uv a h
    simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar] at h ⊢
    exact ⟨CVar.Scoped.add_ h.1 trivial, by rw [CVar.val_add_, h.2]; rfl⟩
  have RB : ∀ {s : ProverState F} {u v : FVar F} {uv vv : F},
      CircuitType.ReadsAs (val := F) s u uv → CircuitType.ReadsAs (val := F) s v vv →
      CircuitType.ReadsAs (val := F) s (u.add_ v) (uv + vv) := by
    intro s u v uv vv hu hv
    simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]
      at hu hv ⊢
    exact ⟨CVar.Scoped.add_ hu.1 hv.1, by rw [CVar.val_add_, hu.2, hv.2]⟩
  have RCoe : ∀ {s : ProverState F} {b : BoolVar F} {bb : Bool},
      CircuitType.ReadsAs (val := Bool) s b bb →
      CircuitType.ReadsAs (val := F) s (↑b : CVar F) (bit bb) := fun h =>
    ⟨CircuitType.scoped_fvar.mpr (CircuitType.scoped_boolVar.mp h.1),
      CircuitType.reads_fvar.mpr (CircuitType.reads_boolVar.mp h.2)⟩
  have RNot : ∀ {s : ProverState F} {b : BoolVar F} {bb : Bool},
      CircuitType.ReadsAs (val := Bool) s b bb →
      CircuitType.ReadsAs (val := Bool) s (Snarky.not b) (!bb) := fun h =>
    ⟨CircuitType.scoped_boolVar.mpr (not_scoped (CircuitType.scoped_boolVar.mp h.1)),
      CircuitType.reads_boolVar.mpr (not_val (CircuitType.reads_boolVar.mp h.2))⟩
  simp only [groupMapCircuit]
  intro st ht
  obtain ⟨t2, st1, hrun1, hsat1, hT2⟩ :=
    mul_complete (c := c) t t tv tv
      st ⟨ht, ht⟩
  have hT2Fu := RA hT2 (a := params.fu)
  obtain ⟨alphaInv, st2, hrun2, hsat2, hAlphaInv⟩ :=
    mul_complete (c := c) (t2.add_ (CVar.const params.fu)) t2
      (tv * tv + params.fu) (tv * tv)
      st1 ⟨hT2Fu, hT2⟩
  have hT2 := hT2.mono hrun2.nv_le hrun2.le
  have hT2Fu := hT2Fu.mono hrun2.nv_le hrun2.le
  obtain ⟨alpha, st3, hrun3, hsat3, hAlpha⟩ :=
    div_complete (c := c) (CVar.const 1) alphaInv 1
      ((tv * tv + params.fu) * (tv * tv)) hne
      st2 ⟨RC 1 _, hAlphaInv⟩
  have hT2 := hT2.mono hrun3.nv_le hrun3.le
  have hT2Fu := hT2Fu.mono hrun3.nv_le hrun3.le
  obtain ⟨t4, st4, hrun4, hsat4, hT4⟩ :=
    mul_complete (c := c) t2 t2 (tv * tv) (tv * tv)
      st3 ⟨hT2, hT2⟩
  have hT2Fu := hT2Fu.mono hrun4.nv_le hrun4.le
  have hAlpha := hAlpha.mono hrun4.nv_le hrun4.le
  obtain ⟨t4Alpha, st5, hrun5, hsat5, hT4Alpha⟩ :=
    mul_complete (c := c) t4 alpha (tv * tv * (tv * tv))
      (1 / ((tv * tv + params.fu) * (tv * tv)))
      st4 ⟨hT4, hAlpha⟩
  have hT2Fu := hT2Fu.mono hrun5.nv_le hrun5.le
  have hAlpha := hAlpha.mono hrun5.nv_le hrun5.le
  obtain ⟨temp1, st6, hrun6, hsat6, hTemp1⟩ :=
    mul_complete (c := c) t4Alpha (CVar.const params.sqrtNeg3U2)
      (tv * tv * (tv * tv) * (1 / ((tv * tv + params.fu) * (tv * tv)))) params.sqrtNeg3U2
      st5 ⟨hT4Alpha, RC _ _⟩
  have hT2Fu := hT2Fu.mono hrun6.nv_le hrun6.le
  have hAlpha := hAlpha.mono hrun6.nv_le hrun6.le
  have hX1 : CircuitType.ReadsAs (val := F)
    st6 ((CVar.const params.sqrtNeg3U2MinusUOver2).sub_ temp1) (potentialXs params tv).1 := by
    simpa [potentialXs] using RS hTemp1 (a := params.sqrtNeg3U2MinusUOver2)
  have hX2 : CircuitType.ReadsAs (val := F)
    st6 ((CVar.const (-params.u)).sub_ ((CVar.const params.sqrtNeg3U2MinusUOver2).sub_ temp1))
      (potentialXs params tv).2.1 := by
    simpa [potentialXs] using RS hX1 (a := -params.u)
  obtain ⟨t2Inv, st7, hrun7, hsat7, hT2Inv⟩ :=
    mul_complete (c := c) alpha (t2.add_ (CVar.const params.fu))
      (1 / ((tv * tv + params.fu) * (tv * tv))) (tv * tv + params.fu)
      st6 ⟨hAlpha, hT2Fu⟩
  have hT2Fu := hT2Fu.mono hrun7.nv_le hrun7.le
  have hX1 := hX1.mono hrun7.nv_le hrun7.le
  have hX2 := hX2.mono hrun7.nv_le hrun7.le
  obtain ⟨t2PlusFuSq, st8, hrun8, hsat8, hT2PlusFuSq⟩ :=
    mul_complete (c := c) (t2.add_ (CVar.const params.fu))
      (t2.add_ (CVar.const params.fu)) (tv * tv + params.fu) (tv * tv + params.fu)
      st7 ⟨hT2Fu, hT2Fu⟩
  have hX1 := hX1.mono hrun8.nv_le hrun8.le
  have hX2 := hX2.mono hrun8.nv_le hrun8.le
  have hT2Inv := hT2Inv.mono hrun8.nv_le hrun8.le
  obtain ⟨temp2a, st9, hrun9, hsat9, hTemp2a⟩ :=
    mul_complete (c := c) t2PlusFuSq t2Inv ((tv * tv + params.fu) * (tv * tv + params.fu))
      ((1 / ((tv * tv + params.fu) * (tv * tv))) * (tv * tv + params.fu))
      st8 ⟨hT2PlusFuSq, hT2Inv⟩
  have hX1 := hX1.mono hrun9.nv_le hrun9.le
  have hX2 := hX2.mono hrun9.nv_le hrun9.le
  obtain ⟨temp2, st10, hrun10, hsat10, hTemp2⟩ :=
    mul_complete (c := c) temp2a (CVar.const params.inv3U2)
      (((tv * tv + params.fu) * (tv * tv + params.fu)) * ((1 / ((tv * tv + params.fu) * (tv * tv)))
        * (tv * tv + params.fu))) params.inv3U2
      st9 ⟨hTemp2a, RC _ _⟩
  have hX1 := hX1.mono hrun10.nv_le hrun10.le
  have hX2 := hX2.mono hrun10.nv_le hrun10.le
  have hX3 : CircuitType.ReadsAs (val := F) st10 ((CVar.const params.u).sub_ temp2)
    (potentialXs params tv).2.2 := by
    simpa [potentialXs] using RS hTemp2 (a := params.u)
  obtain ⟨y1Sq, st11, hrun11, hsat11, hY1Sq⟩ :=
    ySquared_complete (c := c) params ((CVar.const params.sqrtNeg3U2MinusUOver2).sub_ temp1)
      (potentialXs params tv).1
      st10 hX1
  have hX1 := hX1.mono hrun11.nv_le hrun11.le
  have hX2 := hX2.mono hrun11.nv_le hrun11.le
  have hX3 := hX3.mono hrun11.nv_le hrun11.le
  obtain ⟨sf1, st12, hrun12, hsat12, hSf1⟩ :=
    sqrtFlagged_complete (c := c) sqrtF params.nonResidue
      y1Sq (ySquared params (potentialXs params tv).1) hroot (htwist _)
      st11 hY1Sq
  have hX1 := hX1.mono hrun12.nv_le hrun12.le
  have hX2 := hX2.mono hrun12.nv_le hrun12.le
  have hX3 := hX3.mono hrun12.nv_le hrun12.le
  obtain ⟨y1, b1⟩ := sf1
  obtain ⟨hB1, hRoot1⟩ := hSf1
  obtain ⟨y2Sq, st13, hrun13, hsat13, hY2Sq⟩ :=
    ySquared_complete (c := c)
      params ((CVar.const (-params.u)).sub_ ((CVar.const params.sqrtNeg3U2MinusUOver2).sub_ temp1))
      (potentialXs params tv).2.1
      st12 hX2
  have hX1 := hX1.mono hrun13.nv_le hrun13.le
  have hX2 := hX2.mono hrun13.nv_le hrun13.le
  have hX3 := hX3.mono hrun13.nv_le hrun13.le
  have hB1 := hB1.mono hrun13.nv_le hrun13.le
  have hRoot1 := hRoot1.mono hrun13.nv_le hrun13.le
  obtain ⟨sf2, st14, hrun14, hsat14, hSf2⟩ :=
    sqrtFlagged_complete (c := c) sqrtF params.nonResidue
      y2Sq (ySquared params (potentialXs params tv).2.1) hroot (htwist _)
      st13 hY2Sq
  have hX1 := hX1.mono hrun14.nv_le hrun14.le
  have hX2 := hX2.mono hrun14.nv_le hrun14.le
  have hX3 := hX3.mono hrun14.nv_le hrun14.le
  have hB1 := hB1.mono hrun14.nv_le hrun14.le
  have hRoot1 := hRoot1.mono hrun14.nv_le hrun14.le
  obtain ⟨y2, b2⟩ := sf2
  obtain ⟨hB2, hRoot2⟩ := hSf2
  obtain ⟨y3Sq, st15, hrun15, hsat15, hY3Sq⟩ :=
    ySquared_complete (c := c) params ((CVar.const params.u).sub_ temp2)
      (potentialXs params tv).2.2
      st14 hX3
  have hX1 := hX1.mono hrun15.nv_le hrun15.le
  have hX2 := hX2.mono hrun15.nv_le hrun15.le
  have hX3 := hX3.mono hrun15.nv_le hrun15.le
  have hB1 := hB1.mono hrun15.nv_le hrun15.le
  have hRoot1 := hRoot1.mono hrun15.nv_le hrun15.le
  have hB2 := hB2.mono hrun15.nv_le hrun15.le
  have hRoot2 := hRoot2.mono hrun15.nv_le hrun15.le
  obtain ⟨sf3, st16, hrun16, hsat16, hSf3⟩ :=
    sqrtFlagged_complete (c := c) sqrtF params.nonResidue
      y3Sq (ySquared params (potentialXs params tv).2.2) hroot (htwist _)
      st15 hY3Sq
  have hX1 := hX1.mono hrun16.nv_le hrun16.le
  have hX2 := hX2.mono hrun16.nv_le hrun16.le
  have hX3 := hX3.mono hrun16.nv_le hrun16.le
  have hB1 := hB1.mono hrun16.nv_le hrun16.le
  have hRoot1 := hRoot1.mono hrun16.nv_le hrun16.le
  have hB2 := hB2.mono hrun16.nv_le hrun16.le
  have hRoot2 := hRoot2.mono hrun16.nv_le hrun16.le
  obtain ⟨y3, b3⟩ := sf3
  obtain ⟨hB3, hRoot3⟩ := hSf3
  obtain ⟨u17, st17, hrun17, hsat17, -⟩ :=
    assertNonZero_complete (c := c)
      (((↑b1 : CVar F).add_ (↑b2 : CVar F)).add_ (↑b3 : CVar F))
      (bit (sqrtF (ySquared params (potentialXs params tv).1)).isSome + bit (sqrtF (ySquared params
        (potentialXs params tv).2.1)).isSome + bit (sqrtF (ySquared params (potentialXs params
          tv).2.2)).isSome)
      (flagSum h2 h3 _ _ _ hsome) st16
      (RB (RB (RCoe hB1) (RCoe hB2)) (RCoe hB3))
  have hX1 := hX1.mono hrun17.nv_le hrun17.le
  have hX2 := hX2.mono hrun17.nv_le hrun17.le
  have hX3 := hX3.mono hrun17.nv_le hrun17.le
  have hB1 := hB1.mono hrun17.nv_le hrun17.le
  have hRoot1 := hRoot1.mono hrun17.nv_le hrun17.le
  have hB2 := hB2.mono hrun17.nv_le hrun17.le
  have hRoot2 := hRoot2.mono hrun17.nv_le hrun17.le
  have hB3 := hB3.mono hrun17.nv_le hrun17.le
  have hRoot3 := hRoot3.mono hrun17.nv_le hrun17.le
  have hNB1 := RNot hB1
  have hNB2 := RNot hB2
  obtain ⟨x2First, st18, hrun18, hsat18, hX2First⟩ :=
    and_complete (c := c) (Snarky.not b1)
      b2 (!(sqrtF (ySquared params (potentialXs params tv).1)).isSome)
      ((sqrtF (ySquared params (potentialXs params tv).2.1)).isSome)
      st17 ⟨hNB1, hB2⟩
  have hX1 := hX1.mono hrun18.nv_le hrun18.le
  have hX2 := hX2.mono hrun18.nv_le hrun18.le
  have hX3 := hX3.mono hrun18.nv_le hrun18.le
  have hB1 := hB1.mono hrun18.nv_le hrun18.le
  have hRoot1 := hRoot1.mono hrun18.nv_le hrun18.le
  have hB2 := hB2.mono hrun18.nv_le hrun18.le
  have hRoot2 := hRoot2.mono hrun18.nv_le hrun18.le
  have hB3 := hB3.mono hrun18.nv_le hrun18.le
  have hRoot3 := hRoot3.mono hrun18.nv_le hrun18.le
  have hNB1 := hNB1.mono hrun18.nv_le hrun18.le
  have hNB2 := hNB2.mono hrun18.nv_le hrun18.le
  obtain ⟨nb2AndB3, st19, hrun19, hsat19, hNB2AndB3⟩ :=
    and_complete (c := c) (Snarky.not b2)
      b3 (!(sqrtF (ySquared params (potentialXs params tv).2.1)).isSome)
      ((sqrtF (ySquared params (potentialXs params tv).2.2)).isSome)
      st18 ⟨hNB2, hB3⟩
  have hX1 := hX1.mono hrun19.nv_le hrun19.le
  have hX2 := hX2.mono hrun19.nv_le hrun19.le
  have hX3 := hX3.mono hrun19.nv_le hrun19.le
  have hB1 := hB1.mono hrun19.nv_le hrun19.le
  have hRoot1 := hRoot1.mono hrun19.nv_le hrun19.le
  have hRoot2 := hRoot2.mono hrun19.nv_le hrun19.le
  have hRoot3 := hRoot3.mono hrun19.nv_le hrun19.le
  have hNB1 := hNB1.mono hrun19.nv_le hrun19.le
  have hX2First := hX2First.mono hrun19.nv_le hrun19.le
  obtain ⟨x3First, st20, hrun20, hsat20, hX3First⟩ :=
    and_complete (c := c) (Snarky.not b1)
      nb2AndB3 (!(sqrtF (ySquared params (potentialXs params tv).1)).isSome)
      (!(sqrtF (ySquared params (potentialXs params tv).2.1)).isSome && (sqrtF (ySquared params
        (potentialXs params tv).2.2)).isSome)
      st19 ⟨hNB1, hNB2AndB3⟩
  have hX1 := hX1.mono hrun20.nv_le hrun20.le
  have hX2 := hX2.mono hrun20.nv_le hrun20.le
  have hX3 := hX3.mono hrun20.nv_le hrun20.le
  have hB1 := hB1.mono hrun20.nv_le hrun20.le
  have hRoot1 := hRoot1.mono hrun20.nv_le hrun20.le
  have hRoot2 := hRoot2.mono hrun20.nv_le hrun20.le
  have hRoot3 := hRoot3.mono hrun20.nv_le hrun20.le
  have hX2First := hX2First.mono hrun20.nv_le hrun20.le
  obtain ⟨t3y, st21, hrun21, hsat21, hT3y⟩ :=
    mul_complete (c := c) (↑x3First : CVar F) y3
      (bit (!(sqrtF (ySquared params (potentialXs params tv).1)).isSome && (!(sqrtF (ySquared params
        (potentialXs params tv).2.1)).isSome && (sqrtF (ySquared params (potentialXs params
          tv).2.2)).isSome)))
      ((sqrtF (if (sqrtF (ySquared params (potentialXs params tv).2.2)).isSome then ySquared params
        (potentialXs params tv).2.2
        else params.nonResidue * ySquared params (potentialXs params tv).2.2)).getD 0)
      st20 ⟨RCoe hX3First, hRoot3⟩
  have hX1 := hX1.mono hrun21.nv_le hrun21.le
  have hX2 := hX2.mono hrun21.nv_le hrun21.le
  have hX3 := hX3.mono hrun21.nv_le hrun21.le
  have hB1 := hB1.mono hrun21.nv_le hrun21.le
  have hRoot1 := hRoot1.mono hrun21.nv_le hrun21.le
  have hRoot2 := hRoot2.mono hrun21.nv_le hrun21.le
  have hRoot3 := hRoot3.mono hrun21.nv_le hrun21.le
  have hX2First := hX2First.mono hrun21.nv_le hrun21.le
  have hX3First := hX3First.mono hrun21.nv_le hrun21.le
  obtain ⟨t2y, st22, hrun22, hsat22, hT2y⟩ :=
    mul_complete (c := c) (↑x2First : CVar F) y2
      (bit (!(sqrtF (ySquared params (potentialXs params tv).1)).isSome && (sqrtF (ySquared params
        (potentialXs params tv).2.1)).isSome))
      ((sqrtF (if (sqrtF (ySquared params (potentialXs params tv).2.1)).isSome then ySquared params
        (potentialXs params tv).2.1
        else params.nonResidue * ySquared params (potentialXs params tv).2.1)).getD 0)
      st21 ⟨RCoe hX2First, hRoot2⟩
  have hX1 := hX1.mono hrun22.nv_le hrun22.le
  have hX2 := hX2.mono hrun22.nv_le hrun22.le
  have hX3 := hX3.mono hrun22.nv_le hrun22.le
  have hB1 := hB1.mono hrun22.nv_le hrun22.le
  have hRoot1 := hRoot1.mono hrun22.nv_le hrun22.le
  have hRoot2 := hRoot2.mono hrun22.nv_le hrun22.le
  have hRoot3 := hRoot3.mono hrun22.nv_le hrun22.le
  have hX2First := hX2First.mono hrun22.nv_le hrun22.le
  have hX3First := hX3First.mono hrun22.nv_le hrun22.le
  have hT3y := hT3y.mono hrun22.nv_le hrun22.le
  obtain ⟨t1y, st23, hrun23, hsat23, hT1y⟩ :=
    mul_complete (c := c) (↑b1 : CVar F) y1
      (bit (sqrtF (ySquared params (potentialXs params tv).1)).isSome)
      ((sqrtF (if (sqrtF (ySquared params (potentialXs params tv).1)).isSome then ySquared params
        (potentialXs params tv).1
        else params.nonResidue * ySquared params (potentialXs params tv).1)).getD 0)
      st22 ⟨RCoe hB1, hRoot1⟩
  have hX1 := hX1.mono hrun23.nv_le hrun23.le
  have hX2 := hX2.mono hrun23.nv_le hrun23.le
  have hX3 := hX3.mono hrun23.nv_le hrun23.le
  have hB1 := hB1.mono hrun23.nv_le hrun23.le
  have hRoot1 := hRoot1.mono hrun23.nv_le hrun23.le
  have hRoot2 := hRoot2.mono hrun23.nv_le hrun23.le
  have hRoot3 := hRoot3.mono hrun23.nv_le hrun23.le
  have hX2First := hX2First.mono hrun23.nv_le hrun23.le
  have hX3First := hX3First.mono hrun23.nv_le hrun23.le
  have hT3y := hT3y.mono hrun23.nv_le hrun23.le
  have hT2y := hT2y.mono hrun23.nv_le hrun23.le
  obtain ⟨t3x, st24, hrun24, hsat24, hT3x⟩ :=
    mul_complete (c := c) (↑x3First : CVar F) ((CVar.const params.u).sub_ temp2)
      (bit (!(sqrtF (ySquared params (potentialXs params tv).1)).isSome && (!(sqrtF (ySquared params
        (potentialXs params tv).2.1)).isSome && (sqrtF (ySquared params (potentialXs params
          tv).2.2)).isSome)))
      (potentialXs params tv).2.2
      st23 ⟨RCoe hX3First, hX3⟩
  have hX1 := hX1.mono hrun24.nv_le hrun24.le
  have hX2 := hX2.mono hrun24.nv_le hrun24.le
  have hX3 := hX3.mono hrun24.nv_le hrun24.le
  have hB1 := hB1.mono hrun24.nv_le hrun24.le
  have hRoot1 := hRoot1.mono hrun24.nv_le hrun24.le
  have hRoot2 := hRoot2.mono hrun24.nv_le hrun24.le
  have hRoot3 := hRoot3.mono hrun24.nv_le hrun24.le
  have hX2First := hX2First.mono hrun24.nv_le hrun24.le
  have hX3First := hX3First.mono hrun24.nv_le hrun24.le
  have hT3y := hT3y.mono hrun24.nv_le hrun24.le
  have hT2y := hT2y.mono hrun24.nv_le hrun24.le
  have hT1y := hT1y.mono hrun24.nv_le hrun24.le
  obtain ⟨t2x, st25, hrun25, hsat25, hT2x⟩ :=
    mul_complete (c := c) (↑x2First : CVar F)
      ((CVar.const (-params.u)).sub_ ((CVar.const params.sqrtNeg3U2MinusUOver2).sub_ temp1))
      (bit (!(sqrtF (ySquared params (potentialXs params tv).1)).isSome && (sqrtF (ySquared params
        (potentialXs params tv).2.1)).isSome))
      (potentialXs params tv).2.1
      st24 ⟨RCoe hX2First, hX2⟩
  have hX1 := hX1.mono hrun25.nv_le hrun25.le
  have hX2 := hX2.mono hrun25.nv_le hrun25.le
  have hX3 := hX3.mono hrun25.nv_le hrun25.le
  have hB1 := hB1.mono hrun25.nv_le hrun25.le
  have hRoot1 := hRoot1.mono hrun25.nv_le hrun25.le
  have hRoot2 := hRoot2.mono hrun25.nv_le hrun25.le
  have hRoot3 := hRoot3.mono hrun25.nv_le hrun25.le
  have hX2First := hX2First.mono hrun25.nv_le hrun25.le
  have hX3First := hX3First.mono hrun25.nv_le hrun25.le
  have hT3y := hT3y.mono hrun25.nv_le hrun25.le
  have hT2y := hT2y.mono hrun25.nv_le hrun25.le
  have hT1y := hT1y.mono hrun25.nv_le hrun25.le
  have hT3x := hT3x.mono hrun25.nv_le hrun25.le
  obtain ⟨t1x, st26, hrun26, hsat26, hT1x⟩ :=
    mul_complete (c := c) (↑b1 : CVar F) ((CVar.const params.sqrtNeg3U2MinusUOver2).sub_ temp1)
      (bit (sqrtF (ySquared params (potentialXs params tv).1)).isSome)
      (potentialXs params tv).1
      st25 ⟨RCoe hB1, hX1⟩
  have hX1 := hX1.mono hrun26.nv_le hrun26.le
  have hX2 := hX2.mono hrun26.nv_le hrun26.le
  have hX3 := hX3.mono hrun26.nv_le hrun26.le
  have hB1 := hB1.mono hrun26.nv_le hrun26.le
  have hRoot1 := hRoot1.mono hrun26.nv_le hrun26.le
  have hRoot2 := hRoot2.mono hrun26.nv_le hrun26.le
  have hRoot3 := hRoot3.mono hrun26.nv_le hrun26.le
  have hX2First := hX2First.mono hrun26.nv_le hrun26.le
  have hX3First := hX3First.mono hrun26.nv_le hrun26.le
  have hT3y := hT3y.mono hrun26.nv_le hrun26.le
  have hT2y := hT2y.mono hrun26.nv_le hrun26.le
  have hT1y := hT1y.mono hrun26.nv_le hrun26.le
  have hT3x := hT3x.mono hrun26.nv_le hrun26.le
  have hT2x := hT2x.mono hrun26.nv_le hrun26.le

  have N25 : st25.nv ≤ st26.nv := hrun26.nv_le
  have L25 : st25.env.Le st26.env := hrun26.le
  have N24 : st24.nv ≤ st26.nv := Nat.le_trans hrun25.nv_le N25
  have L24 : st24.env.Le st26.env := hrun25.le.trans L25
  have N23 : st23.nv ≤ st26.nv := Nat.le_trans hrun24.nv_le N24
  have L23 : st23.env.Le st26.env := hrun24.le.trans L24
  have N22 : st22.nv ≤ st26.nv := Nat.le_trans hrun23.nv_le N23
  have L22 : st22.env.Le st26.env := hrun23.le.trans L23
  have N21 : st21.nv ≤ st26.nv := Nat.le_trans hrun22.nv_le N22
  have L21 : st21.env.Le st26.env := hrun22.le.trans L22
  have N20 : st20.nv ≤ st26.nv := Nat.le_trans hrun21.nv_le N21
  have L20 : st20.env.Le st26.env := hrun21.le.trans L21
  have N19 : st19.nv ≤ st26.nv := Nat.le_trans hrun20.nv_le N20
  have L19 : st19.env.Le st26.env := hrun20.le.trans L20
  have N18 : st18.nv ≤ st26.nv := Nat.le_trans hrun19.nv_le N19
  have L18 : st18.env.Le st26.env := hrun19.le.trans L19
  have N17 : st17.nv ≤ st26.nv := Nat.le_trans hrun18.nv_le N18
  have L17 : st17.env.Le st26.env := hrun18.le.trans L18
  have N16 : st16.nv ≤ st26.nv := Nat.le_trans hrun17.nv_le N17
  have L16 : st16.env.Le st26.env := hrun17.le.trans L17
  have N15 : st15.nv ≤ st26.nv := Nat.le_trans hrun16.nv_le N16
  have L15 : st15.env.Le st26.env := hrun16.le.trans L16
  have N14 : st14.nv ≤ st26.nv := Nat.le_trans hrun15.nv_le N15
  have L14 : st14.env.Le st26.env := hrun15.le.trans L15
  have N13 : st13.nv ≤ st26.nv := Nat.le_trans hrun14.nv_le N14
  have L13 : st13.env.Le st26.env := hrun14.le.trans L14
  have N12 : st12.nv ≤ st26.nv := Nat.le_trans hrun13.nv_le N13
  have L12 : st12.env.Le st26.env := hrun13.le.trans L13
  have N11 : st11.nv ≤ st26.nv := Nat.le_trans hrun12.nv_le N12
  have L11 : st11.env.Le st26.env := hrun12.le.trans L12
  have N10 : st10.nv ≤ st26.nv := Nat.le_trans hrun11.nv_le N11
  have L10 : st10.env.Le st26.env := hrun11.le.trans L11
  have N9 : st9.nv ≤ st26.nv := Nat.le_trans hrun10.nv_le N10
  have L9 : st9.env.Le st26.env := hrun10.le.trans L10
  have N8 : st8.nv ≤ st26.nv := Nat.le_trans hrun9.nv_le N9
  have L8 : st8.env.Le st26.env := hrun9.le.trans L9
  have N7 : st7.nv ≤ st26.nv := Nat.le_trans hrun8.nv_le N8
  have L7 : st7.env.Le st26.env := hrun8.le.trans L8
  have N6 : st6.nv ≤ st26.nv := Nat.le_trans hrun7.nv_le N7
  have L6 : st6.env.Le st26.env := hrun7.le.trans L7
  have N5 : st5.nv ≤ st26.nv := Nat.le_trans hrun6.nv_le N6
  have L5 : st5.env.Le st26.env := hrun6.le.trans L6
  have N4 : st4.nv ≤ st26.nv := Nat.le_trans hrun5.nv_le N5
  have L4 : st4.env.Le st26.env := hrun5.le.trans L5
  have N3 : st3.nv ≤ st26.nv := Nat.le_trans hrun4.nv_le N4
  have L3 : st3.env.Le st26.env := hrun4.le.trans L4
  have N2 : st2.nv ≤ st26.nv := Nat.le_trans hrun3.nv_le N3
  have L2 : st2.env.Le st26.env := hrun3.le.trans L3
  have N1 : st1.nv ≤ st26.nv := Nat.le_trans hrun2.nv_le N2
  have L1 : st1.env.Le st26.env := hrun2.le.trans L2
  refine ⟨⟨(t1x.add_ t2x).add_ t3x, (t1y.add_ t2y).add_ t3y⟩, st26, ?_, ?_, ?_, ?_⟩
  · exact hrun1.bind (hrun2.bind (hrun3.bind (hrun4.bind (hrun5.bind (hrun6.bind
      (hrun7.bind (hrun8.bind (hrun9.bind (hrun10.bind (hrun11.bind (hrun12.bind
      (hrun13.bind (hrun14.bind (hrun15.bind (hrun16.bind (hrun17.bind (hrun18.bind
      (hrun19.bind (hrun20.bind (hrun21.bind (hrun22.bind (hrun23.bind (hrun24.bind
      (hrun25.bind (hrun26.bind rfl)))))))))))))))))))))))))
  · intro stf hnv hle
    exact
      Sat.bind hrun1 (hsat1 (Nat.le_trans N1 hnv) (L1.trans hle)) (
      Sat.bind hrun2 (hsat2 (Nat.le_trans N2 hnv) (L2.trans hle)) (
      Sat.bind hrun3 (hsat3 (Nat.le_trans N3 hnv) (L3.trans hle)) (
      Sat.bind hrun4 (hsat4 (Nat.le_trans N4 hnv) (L4.trans hle)) (
      Sat.bind hrun5 (hsat5 (Nat.le_trans N5 hnv) (L5.trans hle)) (
      Sat.bind hrun6 (hsat6 (Nat.le_trans N6 hnv) (L6.trans hle)) (
      Sat.bind hrun7 (hsat7 (Nat.le_trans N7 hnv) (L7.trans hle)) (
      Sat.bind hrun8 (hsat8 (Nat.le_trans N8 hnv) (L8.trans hle)) (
      Sat.bind hrun9 (hsat9 (Nat.le_trans N9 hnv) (L9.trans hle)) (
      Sat.bind hrun10 (hsat10 (Nat.le_trans N10 hnv) (L10.trans hle)) (
      Sat.bind hrun11 (hsat11 (Nat.le_trans N11 hnv) (L11.trans hle)) (
      Sat.bind hrun12 (hsat12 (Nat.le_trans N12 hnv) (L12.trans hle)) (
      Sat.bind hrun13 (hsat13 (Nat.le_trans N13 hnv) (L13.trans hle)) (
      Sat.bind hrun14 (hsat14 (Nat.le_trans N14 hnv) (L14.trans hle)) (
      Sat.bind hrun15 (hsat15 (Nat.le_trans N15 hnv) (L15.trans hle)) (
      Sat.bind hrun16 (hsat16 (Nat.le_trans N16 hnv) (L16.trans hle)) (
      Sat.bind hrun17 (hsat17 (Nat.le_trans N17 hnv) (L17.trans hle)) (
      Sat.bind hrun18 (hsat18 (Nat.le_trans N18 hnv) (L18.trans hle)) (
      Sat.bind hrun19 (hsat19 (Nat.le_trans N19 hnv) (L19.trans hle)) (
      Sat.bind hrun20 (hsat20 (Nat.le_trans N20 hnv) (L20.trans hle)) (
      Sat.bind hrun21 (hsat21 (Nat.le_trans N21 hnv) (L21.trans hle)) (
      Sat.bind hrun22 (hsat22 (Nat.le_trans N22 hnv) (L22.trans hle)) (
      Sat.bind hrun23 (hsat23 (Nat.le_trans N23 hnv) (L23.trans hle)) (
      Sat.bind hrun24 (hsat24 (Nat.le_trans N24 hnv) (L24.trans hle)) (
      Sat.bind hrun25 (hsat25 (Nat.le_trans N25 hnv) (L25.trans hle)) (
      Sat.bind hrun26 (hsat26 hnv hle) Sat.pure)))))))))))))))))))))))))
  · have h := RB (RB hT1x hT2x) hT3x
    rcases h1 : sqrtF (ySquared params (potentialXs params tv).1) with _ | v1
    · rcases h2' : sqrtF (ySquared params (potentialXs params tv).2.1) with _ | v2
      · rcases h3' : sqrtF (ySquared params (potentialXs params tv).2.2) with _ | v3
        · simp [h1, h2', h3'] at hsome
        · simpa [groupMapPure, h1, h2', h3', bit] using h
      · simpa [groupMapPure, h1, h2', bit] using h
    · simpa [groupMapPure, h1, bit] using h
  · have h := RB (RB hT1y hT2y) hT3y
    rcases h1 : sqrtF (ySquared params (potentialXs params tv).1) with _ | v1
    · rcases h2' : sqrtF (ySquared params (potentialXs params tv).2.1) with _ | v2
      · rcases h3' : sqrtF (ySquared params (potentialXs params tv).2.2) with _ | v3
        · simp [h1, h2', h3'] at hsome
        · simpa [groupMapPure, h1, h2', h3', bit] using h
      · simpa [groupMapPure, h1, h2', bit] using h
    · simpa [groupMapPure, h1, bit] using h

/-! ## The wire-protocol spec

`Poseidon.GroupMap.toGroup` is the map the kimchi verifier actually runs: the executable
IPA wire verifier derives the per-proof `U` base with it (`Bulletproof/Wire.lean`), and
the knowledge-soundness capstones quote it. This section takes it as the circuit's
specification, in the canonical `ZMod q` world (`Fact q.Prime`) the deployed Pasta specs
live in: `GroupMapParams.ofSpec` reads a wire `Spec` as this module's parameter record,
`groupMapPure_toGroup` identifies the module's pure model with the wire map, and the two
laws below restate soundness against the wire curve predicate (`OnCurve`) and
completeness against `toGroup` itself, the advice instantiated with the spec's own
Tonelli–Shanks root and its coherence hypotheses discharged. -/

section Wire

open CompElliptic.Fields CompElliptic.CurveForms.ShortWeierstrass

variable {q : ℕ} [Fact q.Prime]

/-- This module's parameters, read off a wire `Poseidon.GroupMap.Spec` — plus the
non-residue the in-circuit flagged-root trick needs, which the wire map has no
counterpart for (it retries candidates instead of certifying failures). -/
def GroupMapParams.ofSpec (spec : _root_.Poseidon.GroupMap.Spec q) (nonResidue : ZMod q) :
    GroupMapParams (ZMod q) where
  u := spec.u
  fu := spec.fu
  sqrtNeg3U2MinusUOver2 := spec.sqrtNegThreeUSquaredMinusUOver2
  sqrtNeg3U2 := spec.sqrtNegThreeUSquared
  inv3U2 := spec.invThreeUSquared
  b := spec.E.B
  nonResidue := nonResidue

/-- The candidate abscissae agree with the wire map's: `potentialXs` at `ofSpec` is
`Poseidon.GroupMap.potentialXs`. -/
theorem potentialXs_ofSpec (spec : _root_.Poseidon.GroupMap.Spec q)
    (nonResidue t : ZMod q) :
    potentialXs (.ofSpec spec nonResidue) t
      = _root_.Poseidon.GroupMap.potentialXs spec t := by
  have hinv : (1 : ZMod q) / ((t * t + spec.fu) * (t * t))
      = (t ^ 2 * (t ^ 2 + spec.fu))⁻¹ := by
    rw [one_div,
      show (t * t + spec.fu) * (t * t) = t ^ 2 * (t ^ 2 + spec.fu) from by ring]
  simp only [potentialXs, _root_.Poseidon.GroupMap.potentialXs, GroupMapParams.ofSpec,
    hinv, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- The candidate test values agree with the wire map's: `ySquared` at `ofSpec` is
`Poseidon.GroupMap.curveEqn`. -/
theorem ySquared_ofSpec (spec : _root_.Poseidon.GroupMap.Spec q)
    (nonResidue x : ZMod q) :
    ySquared (.ofSpec spec nonResidue) x = _root_.Poseidon.GroupMap.curveEqn spec x := by
  simp only [ySquared, _root_.Poseidon.GroupMap.curveEqn, GroupMapParams.ofSpec]
  ring

/-- **The wire identification**: at a wire `Spec`, with the spec's own Tonelli–Shanks
root as advice, the module's pure model computes the wire map's point — coordinate for
coordinate, first-flagged candidate for first-flagged candidate. -/
theorem groupMapPure_toGroup (spec : _root_.Poseidon.GroupMap.Spec q)
    (nonResidue t : ZMod q) :
    groupMapPure spec.sqrt.sqrt? (.ofSpec spec nonResidue) t
      = ((_root_.Poseidon.GroupMap.toGroup spec t).x,
          (_root_.Poseidon.GroupMap.toGroup spec t).y) := by
  have hys : ∀ x : ZMod q,
      spec.sqrt.sqrt? (ySquared (GroupMapParams.ofSpec spec nonResidue) x)
        = _root_.Poseidon.GroupMap.getY spec x := fun x => by
    rw [ySquared_ofSpec, _root_.Poseidon.GroupMap.getY]
  rcases hg : _root_.Poseidon.GroupMap.toGroup spec t with ⟨px, py, hval⟩
  simp only [_root_.Poseidon.GroupMap.toGroup] at hg
  split at hg <;> [skip; split at hg <;> [skip; split at hg]] <;>
    obtain ⟨rfl, rfl⟩ : _ ∧ _ := ⟨congrArg SWPoint.x hg, congrArg SWPoint.y hg⟩ <;>
    simp [groupMapPure, potentialXs_ofSpec, *]

/-- A rootless value's non-residue twist has a root: two non-squares multiply to a
square (`FiniteField.pow_dichotomy`), and `sqrt?` is complete on squares. The discharge
of `groupMapCircuit_complete_spec`'s twist hypothesis at a genuine Tonelli–Shanks
root. -/
private theorem sqrt?_twist {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (d : TonelliShanks F) (hchar : ringChar F ≠ 2)
    {nr : F} (hnr0 : nr ≠ 0) (hnr : ¬IsSquare nr) :
    ∀ a, d.sqrt? a = none → (d.sqrt? (nr * a)).isSome := by
  intro a hnone
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp [TonelliShanks.sqrt?] at hnone
  have hnsq : ¬IsSquare a := fun hsq => by
    obtain ⟨r, hr⟩ := d.sqrt?_isSome_of_isSquare hsq
    rw [hr] at hnone
    cases hnone
  have hsq : IsSquare (nr * a) := by
    have h1 := (FiniteField.pow_dichotomy hchar hnr0).resolve_left
      fun h => hnr ((FiniteField.isSquare_iff hchar hnr0).mpr h)
    have h2 := (FiniteField.pow_dichotomy hchar ha0).resolve_left
      fun h => hnsq ((FiniteField.isSquare_iff hchar ha0).mpr h)
    refine (FiniteField.isSquare_iff hchar (mul_ne_zero hnr0 ha0)).mpr ?_
    rw [mul_pow, h1, h2, neg_mul_neg, one_mul]
  obtain ⟨r, hr⟩ := d.sqrt?_isSome_of_isSquare hsq
  rw [hr]
  rfl

open Std.Do in
/-- **Wire-level soundness**: any satisfying valuation reads the result as a point of the
wire spec's curve — `OnCurve`, the verifier's own predicate — at one of the SvdW candidate
abscissae. The advice is universally quantified: soundness never consults it. -/
theorem groupMapCircuit_onCurve_spec {V : Valuation (ZMod q)} {c : Type}
    [BasicSystem (ZMod q) c] [ConstraintHolds (ZMod q) c] [LawfulBasicSystem (ZMod q) c]
    (spec : _root_.Poseidon.GroupMap.Spec q) (nonResidue : ZMod q)
    (sqrtF : ZMod q → Option (ZMod q)) (t : FVar (ZMod q)) :
    ⦃⌜True⌝⦄
    groupMapCircuit (c := Builder V c) sqrtF (.ofSpec spec nonResidue) t
    ⦃⇓ r _ => ⌜(r.x.val V = (potentialXs (.ofSpec spec nonResidue) (t.val V)).1 ∨
        r.x.val V = (potentialXs (.ofSpec spec nonResidue) (t.val V)).2.1 ∨
        r.x.val V = (potentialXs (.ofSpec spec nonResidue) (t.val V)).2.2) ∧
      OnCurve spec.E.A spec.E.B (r.x.val V, r.y.val V)⌝⦄ := by
  intro nv h hsat
  obtain ⟨hx, hy⟩ := groupMapCircuit_spec (c := c) (V := V) sqrtF
    (.ofSpec spec nonResidue) t nv h hsat
  refine ⟨hx, ?_⟩
  show _ ^ 2 = _ ^ 3 + spec.E.A * _ + spec.E.B
  rw [spec.hA]
  simp only [ySquared] at hy
  rw [show ((GroupMapParams.ofSpec spec nonResidue).b : ZMod q) = spec.E.B from rfl] at hy
  linear_combination hy

open WeierstrassCurve.Affine in
/-- **Wire-level completeness**: the honest run lands on the wire map itself — the result
reads `Poseidon.GroupMap.toGroup`, the map the verifier runs to derive the per-proof `U`
base. `groupMapCircuit_complete` at a wire `Spec`: the advice is the spec's own
Tonelli–Shanks root, root-genuineness is `sqrt?_mul_self`, twist-totality is `sqrt?_twist`
at a genuine non-residue, `2 ≠ 0` comes from `q ≠ 2`, and the pure model is rewritten by
`groupMapPure_toGroup`. The SvdW disjunction (as `IsSquare`) and the operand's
nondegeneracy remain, with `q ≠ 3` pricing the flag-sum assertion. -/
theorem groupMapCircuit_toGroup_complete {c : Type} [BasicSystem (ZMod q) c]
    [ConstraintHolds (ZMod q) c] [LawfulBasicSystem (ZMod q) c]
    (spec : _root_.Poseidon.GroupMap.Spec q) (nonResidue : ZMod q) (t : FVar (ZMod q))
    (tv : ZMod q) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hnr0 : nonResidue ≠ 0)
    (hnr : ¬IsSquare nonResidue)
    (hne : (tv * tv + spec.fu) * (tv * tv) ≠ 0)
    (hsq : IsSquare (ySquared (.ofSpec spec nonResidue)
          (potentialXs (.ofSpec spec nonResidue) tv).1) ∨
        IsSquare (ySquared (.ofSpec spec nonResidue)
          (potentialXs (.ofSpec spec nonResidue) tv).2.1) ∨
        IsSquare (ySquared (.ofSpec spec nonResidue)
          (potentialXs (.ofSpec spec nonResidue) tv).2.2)) :
    Complete (F := ZMod q) (c := c)
      (fun st => CircuitType.ReadsAs (val := ZMod q) st t tv)
      (groupMapCircuit (c := c) spec.sqrt.sqrt? (.ofSpec spec nonResidue) t)
      (fun r st' =>
        CircuitType.ReadsAs (val := ZMod q) st' r.x
          (_root_.Poseidon.GroupMap.toGroup spec tv).x ∧
        CircuitType.ReadsAs (val := ZMod q) st' r.y
          (_root_.Poseidon.GroupMap.toGroup spec tv).y) := by
  have hchar : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hq2
  have hthree : (3 : ZMod q) ≠ 0 := by
    intro h
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp
      ((CharP.cast_eq_zero_iff (ZMod q) q 3).mp (by exact_mod_cast h)))
  have hsome : ∀ v : ZMod q, IsSquare v → (spec.sqrt.sqrt? v).isSome = true := fun v hv => by
    obtain ⟨r, hr⟩ := spec.sqrt.sqrt?_isSome_of_isSquare hv
    rw [hr]
    rfl
  intro st ht
  obtain ⟨r, st', hrun, hsat, hx, hy⟩ :=
    groupMapCircuit_complete (c := c) spec.sqrt.sqrt? (.ofSpec spec nonResidue) t tv
      (Ring.two_ne_zero hchar) hthree hne
      (fun a y h => TonelliShanks.sqrt?_mul_self spec.sqrt h)
      (sqrt?_twist spec.sqrt hchar hnr0 hnr)
      (hsq.imp (hsome _) (Or.imp (hsome _) (hsome _))) st ht
  rw [groupMapPure_toGroup] at hx hy
  exact ⟨r, st', hrun, hsat, hx, hy⟩

end Wire

end Snarky.Kimchi
