import Snarky.DSL.Field
import Snarky.Tactic
import Snarky.DSL.Assert
import Snarky.DSL.Boolean
import Snarky.Kimchi.Semantics
import Poseidon.GroupMap

/-!
# The BW19 hash-to-curve gadget

Port of packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/GroupMap.purs (after mina's
`group_map/bw19.ml`; Wahby–Boneh 2019, https://eprint.iacr.org/2019/403): map a field
element onto a curve `y² = x³ + b`. The circuit computes three candidate abscissae; per
candidate, `sqrtFlagged` witnesses a residuosity flag and a root of either the candidate's
ordinate square or its non-residue twist. At least one flag is asserted set, and the result
is the first-flagged candidate, selected by mutually exclusive boolean products.

The pure model (`potentialXs`, `groupMapPure`) computes the wire map
`Poseidon.GroupMap.toGroup` at any wire `Spec` (`groupMapPure_toGroup`). The generic laws
are stated against the pure model; the wire section restates them against `toGroup`.

## Implementation notes

- The parameters are data (`GroupMapParams`); the deployed values live with their curves
  in the poseidon package.
- The advice is an explicit `sqrtF : F → Option F`. Soundness never consults it;
  completeness states the coherence it needs.
- The port is total: a missing root reads as `0` and the pure map falls back to `(0, 0)`,
  both unreachable for honest inputs.
-/

namespace Snarky.Kimchi

open Snarky Std.Do

variable {F c : Type}

/-- The map's parameters: the seed `u`, `f(u) = u³ + b`, the square-root and inverse
constants, the curve constant, and a known quadratic non-residue for the flagged root. -/
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

/-- The three candidate abscissae: one of them is the abscissa of a curve point
(Shallue–van de Woestijne, which the laws take as a hypothesis). Division is the field's
total one (`0⁻¹ = 0`). -/
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

/-- The ordinate square `x³ + b`, each candidate's test value. -/
def ySquared [Field F] (params : GroupMapParams F) (x : F) : F :=
  x * x * x + params.b

/-- The pure map: the first candidate whose ordinate square has a root under `sqrtF`, as a
coordinate pair; `(0, 0)` when none does, unreachable when some candidate is a square and
`sqrtF` is total on squares. -/
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

/-- In-circuit square root with a residuosity flag: witness the flag, select the operand or
its non-residue twist, witness a root, and pin it with one `square` row —
`y² = if isQR then x else nonResidue·x`. -/
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

/-- The in-circuit map: the candidate abscissae, a flagged root per candidate, at least one
flag asserted set, and the first-flagged candidate selected by boolean products. -/
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
(`y² = x³ + b`) whose abscissa is one of the three `potentialXs` candidates: a flag is
forced set, the selectors pick one branch, and that branch's root is the ordinate. The
advice is universally quantified. -/
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

open Std.Do in
/-- **Soundness, first-flagged.** The selected candidate is the first whose flag is set, and
every earlier candidate's flag is clear with its clearance certified: a root of the
non-residue twist of its ordinate square. The advice is universally quantified. -/
theorem groupMapCircuit_first_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (sqrtF : F → Option F) (params : GroupMapParams F) (t : FVar F) :
    ⦃⌜True⌝⦄
    groupMapCircuit (c := Builder V c) sqrtF params t
    ⦃⇓ r _ => ⌜(r.x.val V = (potentialXs params (t.val V)).1 ∧
        r.y.val V * r.y.val V = ySquared params (potentialXs params (t.val V)).1) ∨
      ((∃ y : F, y * y = params.nonResidue * ySquared params (potentialXs params (t.val V)).1) ∧
        r.x.val V = (potentialXs params (t.val V)).2.1 ∧
        r.y.val V * r.y.val V = ySquared params (potentialXs params (t.val V)).2.1) ∨
      ((∃ y : F, y * y = params.nonResidue * ySquared params (potentialXs params (t.val V)).1) ∧
        (∃ y : F, y * y = params.nonResidue * ySquared params (potentialXs params (t.val V)).2.1) ∧
        r.x.val V = (potentialXs params (t.val V)).2.2 ∧
        r.y.val V * r.y.val V = ySquared params (potentialXs params (t.val V)).2.2)⌝⦄ := by
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
  have hs2 := hx2First (!bb1) bb2 (not_val hb1) hb2
  have hs3 := hx3First (!bb1) (!bb2 && bb3) (not_val hb1)
    (hnb2AndB3 (!bb2) bb3 (not_val hb2) hb3)
  -- the twist certificates of clear flags
  have htw1 : bb1 = false → ∃ y : F,
      y * y = params.nonResidue * ySquared params (potentialXs params (t.val V)).1 := by
    rintro rfl
    exact ⟨sf1.1.val V, by simpa [ySquared, CVar.val_add_, hxCu1, hxSq1, hx1v] using hy1⟩
  have htw2 : bb2 = false → ∃ y : F,
      y * y = params.nonResidue * ySquared params (potentialXs params (t.val V)).2.1 := by
    rintro rfl
    exact ⟨sf2.1.val V, by simpa [ySquared, CVar.val_add_, hxCu2, hxSq2, hx2v] using hy2⟩
  rcases bb1 with _ | _
  · rcases bb2 with _ | _
    · rcases bb3 with _ | _
      · exact absurd (by simp [CVar.val_add_, hb1, hb2, hb3, bit]) hnz
      · refine Or.inr (Or.inr ⟨htw1 rfl, htw2 rfl, ?_, ?_⟩)
        · rw [← hx3v]
          simp [CVar.val_add_, ht1x, ht2x, ht3x, hb1, hs2, hs3, bit]
        · have hx : ((CVar.const params.u).sub_ temp2).val V
              = (potentialXs params (t.val V)).2.2 := hx3v
          rw [← hx]
          simpa [CVar.val_add_, ySquared, ht1x, ht2x, ht3x, ht1y, ht2y, ht3y, hb1,
            hs2, hs3, bit, hxCu3, hxSq3] using hy3
    · refine Or.inr (Or.inl ⟨htw1 rfl, ?_, ?_⟩)
      · rw [← hx2v]
        simp [CVar.val_add_, ht1x, ht2x, ht3x, hb1, hs2, hs3, bit]
      · rw [← hx2v]
        simpa [CVar.val_add_, ySquared, ht1x, ht2x, ht3x, ht1y, ht2y, ht3y, hb1,
          hs2, hs3, bit, hxCu2, hxSq2] using hy2
  · refine Or.inl ⟨?_, ?_⟩
    · rw [← hx1v]
      simp [CVar.val_add_, ht1x, ht2x, ht3x, hb1, hs2, hs3, bit]
    · rw [← hx1v]
      simpa [CVar.val_add_, ySquared, ht1x, ht2x, ht3x, ht1y, ht2y, ht3y, hb1,
        hs2, hs3, bit, hxCu1, hxSq1] using hy1

/-! ## Completeness

The honest run, step by step: each gate's completeness law takes its operands' readings
(`CircuitType.ReadsAs`) to the result's. -/

/-- The ordinate-square block's honest run: two `mul`s and a constant add. -/
@[complete_law] private theorem ySquared_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (params : GroupMapParams F)
    (x : FVar F) (xv : F) :
    Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := F) st x xv)
      (do let xSq ← mul (c := c) x x
          let xCu ← mul xSq x
          pure (CVar.add_ xCu (CVar.const params.b)))
      (fun r st' => CircuitType.ReadsAs (val := F) st' r (ySquared params xv)) := by
  complete_walk
  exact Complete.pure_of fun st h =>
    ⟨CircuitType.scoped_fvar.mpr
        (CVar.Scoped.add_ (CircuitType.scoped_fvar.mp h.2.1) trivial),
      CircuitType.reads_fvar.mpr (by
        rw [CVar.val_add_, CircuitType.reads_fvar.mp h.2.2]; rfl)⟩

/-- The flagged root's honest run. With genuine roots, and a rootless operand's
non-residue twist rooted, the run accepts: the flag reads the operand's residuosity and
the value reads the advice's root of the flag-selected operand. -/
@[complete_law] private theorem sqrtFlagged_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (sqrtF : F → Option F) (nonResidue : F)
    (x : FVar F) (xv : F) (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : sqrtF xv = none → (sqrtF (nonResidue * xv)).isSome) :
    Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := F) st x xv)
      (sqrtFlagged (c := c) sqrtF nonResidue x)
      (fun r st' => CircuitType.ReadsAs (val := Bool) st' r.2 (sqrtF xv).isSome ∧
        CircuitType.ReadsAs (val := F) st' r.1
          ((sqrtF (if (sqrtF xv).isSome then xv else nonResidue * xv)).getD 0)) := by
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
  simp only [sqrtFlagged, select_fvar]
  -- the residuosity flag
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?qrun, h⟩) (fun _ _ h => h)
      (Complete.frame CircuitType.monotone_readsAs
        (Complete.witness (isQRWit sqrtF x) ((sqrtF xv).isSome) (by simp))))
    fun isQR => ?_
  case qrun =>
    simp only [isQRWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.1),
      CircuitType.reads_fvar.mp h.2, Except.bind]
    rfl
  -- the flag-selected operand
  refine Complete.bind
    (Complete.imp
      (fun st h => ⟨⟨h.1, h.2,
        ⟨CircuitType.scoped_fvar.mpr
            (CVar.Scoped.scale_ (CircuitType.scoped_fvar.mp h.2.1)),
          CircuitType.reads_fvar.mpr (by
            rw [CVar.val_scale_, CircuitType.reads_fvar.mp h.2.2])⟩⟩, h.1⟩)
      (fun _ _ h => h)
      (Complete.frame CircuitType.monotone_readsAs
        (selectField_complete (c := c) isQR x (CVar.scale_ nonResidue x)
          (sqrtF xv).isSome xv (nonResidue * xv))))
    fun xOrMx => ?_
  -- the root
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?rrun, h⟩) (fun _ _ h => h)
      (Complete.frame (monotone_and CircuitType.monotone_readsAs CircuitType.monotone_readsAs)
        (Complete.witness (sqrtWit sqrtF xOrMx)
          ((sqrtF (if (sqrtF xv).isSome then xv else nonResidue * xv)).getD 0)
          (by simp))))
    fun sqrtVal => ?_
  case rrun =>
    simp only [sqrtWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.1.1),
      CircuitType.reads_fvar.mp h.1.2, Except.bind]
    rfl
  -- the square row
  refine Complete.bind
    (Complete.imp (fun st h => ⟨⟨h.1, h.2.1⟩, h.1, h.2.2⟩) (fun _ _ h => h)
      (Complete.frame (monotone_and CircuitType.monotone_readsAs CircuitType.monotone_readsAs)
        (assertSquare_complete (c := c) sqrtVal xOrMx _ _ hsq)))
    fun _ => Complete.pure_of fun _ h => ⟨h.2.2, h.2.1⟩

/-- At least one flag set makes the flag sum nonzero, given `2 ≠ 0` and `3 ≠ 0`. -/
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
Hypotheses: the `div` divisor `(t² + f(u))·t²` is nonzero; some candidate's ordinate
square has a root (Shallue–van de Woestijne); `sqrtF`'s roots are genuine; a rootless
value's non-residue twist has a root; and `2, 3 ≠ 0` keep the flag sum nonzero. -/
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
  -- the candidate identifications, stated before the walk so every goal it leaves has them
  have e1 : params.sqrtNeg3U2MinusUOver2 -
      tv * tv * (tv * tv) * (1 / ((tv * tv + params.fu) * (tv * tv))) * params.sqrtNeg3U2
      = (potentialXs params tv).1 := by simp [potentialXs]
  have e2 : -params.u - (potentialXs params tv).1 = (potentialXs params tv).2.1 := by
    simp [potentialXs]
  have e3 : params.u -
      (tv * tv + params.fu) * (tv * tv + params.fu) *
        (1 / ((tv * tv + params.fu) * (tv * tv)) * (tv * tv + params.fu)) * params.inv3U2
      = (potentialXs params tv).2.2 := by simp [potentialXs]
  simp only [groupMapCircuit]
  complete_walk
  refine Complete.pure_of fun st h => ⟨?_, ?_⟩
  · have hx := RB (RB h.2 h.1.2) h.1.1.2
    rw [e1, e2, e3] at hx
    rcases h1 : sqrtF (ySquared params (potentialXs params tv).1) with _ | v1
    · rcases h2' : sqrtF (ySquared params (potentialXs params tv).2.1) with _ | v2
      · rcases h3' : sqrtF (ySquared params (potentialXs params tv).2.2) with _ | v3
        · simp [h1, h2', h3'] at hsome
        · simpa [groupMapPure, h1, h2', h3', bit] using hx
      · simpa [groupMapPure, h1, h2', bit] using hx
    · simpa [groupMapPure, h1, bit] using hx
  · have hy := RB (RB h.1.1.1.2 h.1.1.1.1.2) h.1.1.1.1.1.2
    rw [e1, e2, e3] at hy
    rcases h1 : sqrtF (ySquared params (potentialXs params tv).1) with _ | v1
    · rcases h2' : sqrtF (ySquared params (potentialXs params tv).2.1) with _ | v2
      · rcases h3' : sqrtF (ySquared params (potentialXs params tv).2.2) with _ | v3
        · simp [h1, h2', h3'] at hsome
        · simpa [groupMapPure, h1, h2', h3', bit] using hy
      · simpa [groupMapPure, h1, h2', bit] using hy
    · simpa [groupMapPure, h1, bit] using hy
  · rw [e1, e2, e3]
    exact flagSum h2 h3 _ _ _ hsome
  all_goals exact htwist _

/-! ## The wire-protocol spec

`Poseidon.GroupMap.toGroup` is the wire map-to-curve: the wire verifier's `U` base is its
lower-half representative (`Bulletproof.Ipa.KimchiCurve.uBase`). This section takes it as
the circuit's specification over `ZMod q`: `GroupMapParams.ofSpec` reads a wire `Spec` as
this module's parameters, and the laws below restate soundness against the wire curve
predicate and against `toGroup` up to sign, and completeness against `toGroup` with the
spec's own Tonelli–Shanks root as advice. -/

section Wire

open CompElliptic.Fields CompElliptic.CurveForms.ShortWeierstrass

variable {q : ℕ} [Fact q.Prime]

/-- This module's parameters, read off a wire `Poseidon.GroupMap.Spec`, the non-residue
included. -/
def GroupMapParams.ofSpec (spec : _root_.Poseidon.GroupMap.Spec q) :
    GroupMapParams (ZMod q) where
  u := spec.u
  fu := spec.fu
  sqrtNeg3U2MinusUOver2 := spec.sqrtNegThreeUSquaredMinusUOver2
  sqrtNeg3U2 := spec.sqrtNegThreeUSquared
  inv3U2 := spec.invThreeUSquared
  b := spec.E.B
  nonResidue := spec.nonResidue

/-- The candidate abscissae agree with the wire map's: `potentialXs` at `ofSpec` is
`Poseidon.GroupMap.potentialXs`. -/
theorem potentialXs_ofSpec (spec : _root_.Poseidon.GroupMap.Spec q) (t : ZMod q) :
    potentialXs (.ofSpec spec) t
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
theorem ySquared_ofSpec (spec : _root_.Poseidon.GroupMap.Spec q) (x : ZMod q) :
    ySquared (.ofSpec spec) x = _root_.Poseidon.GroupMap.curveEqn spec x := by
  simp only [ySquared, _root_.Poseidon.GroupMap.curveEqn, GroupMapParams.ofSpec]
  ring

/-- **Wire identification.** At a wire `Spec`, with the spec's own Tonelli–Shanks root as
advice, the pure model computes `toGroup`'s point. -/
theorem groupMapPure_toGroup (spec : _root_.Poseidon.GroupMap.Spec q) (t : ZMod q) :
    groupMapPure spec.sqrt.sqrt? (.ofSpec spec) t
      = ((_root_.Poseidon.GroupMap.toGroup spec t).x,
          (_root_.Poseidon.GroupMap.toGroup spec t).y) := by
  have hys : ∀ x : ZMod q,
      spec.sqrt.sqrt? (ySquared (GroupMapParams.ofSpec spec) x)
        = _root_.Poseidon.GroupMap.getY spec x := fun x => by
    rw [ySquared_ofSpec, _root_.Poseidon.GroupMap.getY]
  rcases hg : _root_.Poseidon.GroupMap.toGroup spec t with ⟨px, py, hval⟩
  simp only [_root_.Poseidon.GroupMap.toGroup] at hg
  split at hg <;> [skip; split at hg <;> [skip; split at hg]] <;>
    obtain ⟨rfl, rfl⟩ : _ ∧ _ := ⟨congrArg SWPoint.x hg, congrArg SWPoint.y hg⟩ <;>
    simp [groupMapPure, potentialXs_ofSpec, *]

/-- A rootless value's non-residue twist has a root: two non-squares multiply to a
square (`FiniteField.pow_dichotomy`), and `sqrt?` is complete on squares. Discharges
`groupMapCircuit_complete`'s twist hypothesis. -/
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
/-- **Wire-level soundness.** Any satisfying valuation reads the result as a point of the
wire spec's curve (`CompElliptic.CurveForms.ShortWeierstrass.OnCurve`) at one of the
candidate abscissae. The advice is universally quantified. -/
theorem groupMapCircuit_onCurve_spec {V : Valuation (ZMod q)} {c : Type}
    [BasicSystem (ZMod q) c] [ConstraintHolds (ZMod q) c] [LawfulBasicSystem (ZMod q) c]
    (spec : _root_.Poseidon.GroupMap.Spec q)
    (sqrtF : ZMod q → Option (ZMod q)) (t : FVar (ZMod q)) :
    ⦃⌜True⌝⦄
    groupMapCircuit (c := Builder V c) sqrtF (.ofSpec spec) t
    ⦃⇓ r _ => ⌜(r.x.val V = (potentialXs (.ofSpec spec) (t.val V)).1 ∨
        r.x.val V = (potentialXs (.ofSpec spec) (t.val V)).2.1 ∨
        r.x.val V = (potentialXs (.ofSpec spec) (t.val V)).2.2) ∧
      OnCurve spec.E.A spec.E.B (r.x.val V, r.y.val V)⌝⦄ := by
  intro nv h hsat
  obtain ⟨hx, hy⟩ := groupMapCircuit_spec (c := c) (V := V) sqrtF
    (.ofSpec spec) t nv h hsat
  refine ⟨hx, ?_⟩
  show _ ^ 2 = _ ^ 3 + spec.E.A * _ + spec.E.B
  rw [spec.hA]
  simp only [ySquared] at hy
  rw [show ((GroupMapParams.ofSpec spec).b : ZMod q) = spec.E.B from rfl] at hy
  linear_combination hy

open WeierstrassCurve.Affine in
/-- **Wire-level completeness.** The honest run's result reads
`Poseidon.GroupMap.toGroup`'s point: `groupMapCircuit_complete` with the spec's own
Tonelli–Shanks root as advice, its root and twist hypotheses discharged
(`CompElliptic.Fields.TonelliShanks.sqrt?_mul_self`, `sqrt?_twist`) and `2 ≠ 0` from
`q ≠ 2`. The candidate disjunction (as `IsSquare`) and the nonzero `div` divisor remain,
with `q ≠ 3` for the flag sum. -/
theorem groupMapCircuit_toGroup_complete {c : Type} [BasicSystem (ZMod q) c]
    [ConstraintHolds (ZMod q) c] [LawfulBasicSystem (ZMod q) c]
    (spec : _root_.Poseidon.GroupMap.Spec q) (t : FVar (ZMod q))
    (tv : ZMod q) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hne : (tv * tv + spec.fu) * (tv * tv) ≠ 0)
    (hsq : IsSquare (ySquared (.ofSpec spec)
          (potentialXs (.ofSpec spec) tv).1) ∨
        IsSquare (ySquared (.ofSpec spec)
          (potentialXs (.ofSpec spec) tv).2.1) ∨
        IsSquare (ySquared (.ofSpec spec)
          (potentialXs (.ofSpec spec) tv).2.2)) :
    Complete (F := ZMod q) (c := c)
      (fun st => CircuitType.ReadsAs (val := ZMod q) st t tv)
      (groupMapCircuit (c := c) spec.sqrt.sqrt? (.ofSpec spec) t)
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
    groupMapCircuit_complete (c := c) spec.sqrt.sqrt? (.ofSpec spec) t tv
      (Ring.two_ne_zero hchar) hthree hne
      (fun a y h => TonelliShanks.sqrt?_mul_self spec.sqrt h)
      (sqrt?_twist spec.sqrt hchar
        (fun h => spec.nonResidue_spec
          (by rw [show spec.nonResidue = 0 from h]; exact ⟨0, by ring⟩))
        spec.nonResidue_spec)
      (hsq.imp (hsome _) (Or.imp (hsome _) (hsome _))) st ht
  rw [groupMapPure_toGroup] at hx hy
  exact ⟨r, st', hrun, hsat, hx, hy⟩


/-- A twist root certifies a non-square: if `y² = nr·a` with `a = s²` nonzero, then
`nr = (y/s)²`. -/
private theorem not_isSquare_of_twist {F : Type} [Field F] {nr a y : F}
    (hnr : ¬IsSquare nr) (ha : a ≠ 0) (h : y * y = nr * a) : ¬IsSquare a := by
  rintro ⟨s, rfl⟩
  have hs : s ≠ 0 := fun hs => ha (by rw [hs, mul_zero])
  refine hnr ⟨y / s, ?_⟩
  rw [div_mul_div_comm, h, mul_div_assoc, div_self (mul_ne_zero hs hs), mul_one]

/-- `getY` finds a root exactly at the squares. -/
private theorem getY_eq_none_iff (spec : _root_.Poseidon.GroupMap.Spec q) (x : ZMod q) :
    _root_.Poseidon.GroupMap.getY spec x = none
      ↔ ¬IsSquare (_root_.Poseidon.GroupMap.curveEqn spec x) := by
  constructor
  · intro hnone hsq
    obtain ⟨r, hr⟩ := spec.sqrt.sqrt?_isSome_of_isSquare hsq
    rw [_root_.Poseidon.GroupMap.getY, hr] at hnone
    cases hnone
  · intro hnsq
    rcases hy : _root_.Poseidon.GroupMap.getY spec x with _ | y
    · rfl
    · exact absurd ⟨y, (TonelliShanks.sqrt?_mul_self spec.sqrt hy).symm⟩ hnsq

open Std.Do in
/-- **Wire-level soundness, up to sign.** When no ordinate square vanishes (`hnz`), any
satisfying valuation reads the result as `toGroup`'s point up to the ordinate's sign: the
constraints pin the root's square, not its sign. The advice is universally quantified. -/
theorem groupMapCircuit_toGroup_spec {V : Valuation (ZMod q)} {c : Type}
    [BasicSystem (ZMod q) c] [ConstraintHolds (ZMod q) c] [LawfulBasicSystem (ZMod q) c]
    (spec : _root_.Poseidon.GroupMap.Spec q)
    (hnz : ∀ x : ZMod q, _root_.Poseidon.GroupMap.curveEqn spec x ≠ 0)
    (sqrtF : ZMod q → Option (ZMod q)) (t : FVar (ZMod q)) :
    ⦃⌜True⌝⦄
    groupMapCircuit (c := Builder V c) sqrtF (.ofSpec spec) t
    ⦃⇓ r _ => ⌜r.x.val V = (_root_.Poseidon.GroupMap.toGroup spec (t.val V)).x ∧
      (r.y.val V = (_root_.Poseidon.GroupMap.toGroup spec (t.val V)).y ∨
        r.y.val V = -(_root_.Poseidon.GroupMap.toGroup spec (t.val V)).y)⌝⦄ := by
  refine builder_spec_imp _ _ _
    (groupMapCircuit_first_spec (c := c) sqrtF (.ofSpec spec) t) fun r h => ?_
  simp only [potentialXs_ofSpec, ySquared_ofSpec] at h
  simp only [_root_.Poseidon.GroupMap.toGroup]
  have hnone : ∀ x : ZMod q, _root_.Poseidon.GroupMap.getY spec x = none →
      r.y.val V * r.y.val V = _root_.Poseidon.GroupMap.curveEqn spec x → False :=
    fun x hn hy => (getY_eq_none_iff spec x).mp hn ⟨_, hy.symm⟩
  have hsome : ∀ x y w : ZMod q, _root_.Poseidon.GroupMap.getY spec x = some y →
      w * w = spec.nonResidue * _root_.Poseidon.GroupMap.curveEqn spec x → False :=
    fun x y w hs hw => by
    rw [(getY_eq_none_iff spec x).mpr
      (not_isSquare_of_twist spec.nonResidue_spec (hnz x) hw)] at hs
    cases hs
  have hsign : ∀ x y : ZMod q, _root_.Poseidon.GroupMap.getY spec x = some y →
      r.y.val V * r.y.val V = _root_.Poseidon.GroupMap.curveEqn spec x →
      r.y.val V = y ∨ r.y.val V = -y := fun x y hs hy =>
    mul_self_eq_mul_self_iff.mp (hy.trans (TonelliShanks.sqrt?_mul_self spec.sqrt hs).symm)
  split
  · rename_i y hy1
    rcases h with ⟨hx, hy⟩ | ⟨⟨w, hw⟩, -, -⟩ | ⟨⟨w, hw⟩, -, -, -⟩
    · exact ⟨hx, hsign _ y hy1 hy⟩
    · exact (hsome _ y w hy1 hw).elim
    · exact (hsome _ y w hy1 hw).elim
  · rename_i hy1
    split
    · rename_i y hy2
      rcases h with ⟨-, hy⟩ | ⟨-, hx, hy⟩ | ⟨-, ⟨w, hw⟩, -, -⟩
      · exact (hnone _ hy1 hy).elim
      · exact ⟨hx, hsign _ y hy2 hy⟩
      · exact (hsome _ y w hy2 hw).elim
    · rename_i hy2
      split
      · rename_i y hy3
        rcases h with ⟨-, hy⟩ | ⟨-, -, hy⟩ | ⟨-, -, hx, hy⟩
        · exact (hnone _ hy1 hy).elim
        · exact (hnone _ hy2 hy).elim
        · exact ⟨hx, hsign _ y hy3 hy⟩
      · rename_i hy3
        rcases h with ⟨-, hy⟩ | ⟨-, -, hy⟩ | ⟨-, -, -, hy⟩
        · exact (hnone _ hy1 hy).elim
        · exact (hnone _ hy2 hy).elim
        · exact (hnone _ hy3 hy).elim
end Wire

end Snarky.Kimchi
