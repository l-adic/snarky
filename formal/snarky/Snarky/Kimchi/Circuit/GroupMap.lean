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
private def sqrtFlagged [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c]
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
def groupMapCircuit [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c]
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

The honest run at the prover's reading (`Snarky.Prover.WP`): the flagged root's advice
registered, then the map's law over its stages. -/

/-- `isQRWit` returns whether the operand's reading has a root. -/
@[spec] private def Prover.isQRWit_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (sqrtF : F → Option F) (x : FVar F) :=
  Prover.register (Prover.witness_of_run (c := c) (isQRWit sqrtF x) (fun st => x.Scoped st)
    (fun st => (sqrtF (st.read x)).isSome)
    (fun _ h => by simp [isQRWit, AsProver.readCVar_run h]) fun _ _ => by simp)

/-- `sqrtWit` returns the advice's root of the operand's reading. -/
@[spec] private def Prover.sqrtWit_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (sqrtF : F → Option F) (x : FVar F) :=
  Prover.register (Prover.witness_of_run (c := c) (sqrtWit sqrtF x) (fun st => x.Scoped st)
    (fun st => (sqrtF (st.read x)).getD 0)
    (fun _ h => by simp [sqrtWit, AsProver.readCVar_run h]) fun _ _ => by simp)

/-- The flagged root's state-relative completeness: with genuine roots, and every rootless
value's non-residue twist rooted, the flag reads the operand's residuosity and the root reads
the advice's root of the flag-selected operand. -/
private theorem Prover.sqrtFlagged_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (sqrtF : F → Option F) (nonResidue : F)
    (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : ∀ a, sqrtF a = none → (sqrtF (nonResidue * a)).isSome)
    (x : FVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ x.Scoped st₀⌝⦄
    sqrtFlagged (c := Prover c) sqrtF nonResidue x
    ⦃⇓ r s' => ⌜r.1.Scoped s' ∧ (↑r.2 : CVar F).Scoped s' ∧
      s'.read r.2 = (if (sqrtF (st₀.read x)).isSome then 1 else 0) ∧
      s'.read r.1 = (sqrtF (if (sqrtF (st₀.read x)).isSome then st₀.read x
        else nonResidue * st₀.read x)).getD 0 ∧
      st₀ ≤ s'⌝⦄ := by
  -- the advice's root squares to the selected operand
  have hsq : ∀ v : F, (sqrtF (if (sqrtF v).isSome then v else nonResidue * v)).getD 0
      * (sqrtF (if (sqrtF v).isSome then v else nonResidue * v)).getD 0
      = if (sqrtF v).isSome then v else nonResidue * v := by
    intro v
    have hsome : (sqrtF (if (sqrtF v).isSome then v else nonResidue * v)).isSome := by
      rcases hcase : sqrtF v with _ | y
      · simpa [hcase] using htwist v hcase
      · simp [hcase]
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsome
    rw [hy]
    exact hroot _ y hy
  unfold sqrtFlagged
  simp only [select_fvar]
  mvcgen
  -- the result: the select resolves through the flag's field value
  case vc5.post.success.post.success.post.success.post.success =>
    rename_i s₀ h₀ q s₁ h₁ m s₂ h₂ y s₃ h₃ u s h
    obtain ⟨rfl, hx⟩ := h₀
    obtain ⟨⟨hqsc, hqrd⟩, hle₁⟩ := Prover.Reg.iff.mp h₁
    obtain ⟨hmsc, hm, hle₂⟩ := Prover.Reg.iff.mp h₂
    obtain ⟨⟨hysc, hyrd⟩, hle₃⟩ := Prover.Reg.iff.mp h₃
    have hle := Prover.Reg.iff.mp h
    rw [CircuitType.scoped_boolVar] at hqsc
    rw [CircuitType.scoped_fvar] at hysc
    have hq : s₁.read q = if (sqrtF (s₀.read x)).isSome then 1 else 0 := by
      rw [ProverState.read, CircuitType.reads_boolVar.mp hqrd, bit]
    have hsel : s₂.read m
        = if (sqrtF (s₀.read x)).isSome then s₀.read x else nonResidue * s₀.read x := by
      rw [hm, hq, ProverState.read_of_le hle₁ hx]
      split <;> simp only [zero_ne_one, ↓reduceIte, ProverState.read, CVar.val_scale_]
      rw [CVar.val_of_le hle₁ hx]
    refine ⟨hysc.of_le hle, hqsc.of_le (hle₂.trans (hle₃.trans hle)), ?_, ?_,
      hle₁.trans (hle₂.trans (hle₃.trans hle))⟩
    · rw [ProverState.read_of_le (hle₂.trans (hle₃.trans hle)) hqsc, hq]
    · rw [ProverState.read_of_le hle hysc, ProverState.read, CircuitType.reads_fvar.mp hyrd,
        hsel]
  all_goals grind [Prover.Reg.iff, CircuitType.ReadsAs, CircuitType.scoped_fvar,
    CircuitType.reads_fvar, CircuitType.scoped_boolVar, CircuitType.reads_boolVar, bit,
    ProverState.read_of_le, CVar.Scoped.of_le, CVar.Scoped.scale_, CVar.val_scale_]

/-! ### The map, by stages

One triple over the whole run, some thirty tables, exceeds the elaboration budget; the law is
stated per stage instead, over the same program regrouped: the candidate abscissae, one
candidate's ordinate square and flagged root, and the flag-weighted selection.
`groupMapCircuit_stages` is the regrouping. -/

/-- The candidate abscissae of `groupMapCircuit`. -/
private def gmCandidates [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (params : GroupMapParams F) (t : FVar F) : CircuitM F c (FVar F × FVar F × FVar F) := do
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
  pure (x1, x2, x3)

/-- One candidate's ordinate square and its flagged root. -/
private def gmRoot [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (sqrtF : F → Option F) (params : GroupMapParams F) (x : FVar F) :
    CircuitM F c (FVar F × BoolVar F) := do
  let xSq ← mul x x
  let xCu ← mul xSq x
  sqrtFlagged sqrtF params.nonResidue (CVar.add_ xCu (.const params.b))

/-- The flag-weighted selection: at least one flag set, the first-flagged candidate's point. -/
private def gmSelect [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (x1 x2 x3 y1 y2 y3 : FVar F) (b1 b2 b3 : BoolVar F) :
    CircuitM F c (AffinePoint (FVar F)) := do
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

/-- `groupMapCircuit` is its stages in sequence. -/
private theorem groupMapCircuit_stages [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (sqrtF : F → Option F)
    (params : GroupMapParams F) (t : FVar F) :
    groupMapCircuit (c := c) sqrtF params t = (do
      let (x1, x2, x3) ← gmCandidates params t
      let (y1, b1) ← gmRoot sqrtF params x1
      let (y2, b2) ← gmRoot sqrtF params x2
      let (y3, b3) ← gmRoot sqrtF params x3
      gmSelect x1 x2 x3 y1 y2 y3 b1 b2 b3) := by
  simp only [groupMapCircuit, gmCandidates, gmRoot, gmSelect, bind_assoc, pure_bind]

/-- The candidates' state-relative completeness: with the divisor reading nonzero, the abscissae
read the pure candidates. -/
private theorem Prover.gmCandidates_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (params : GroupMapParams F) (t : FVar F)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ t.Scoped st₀ ∧
      (st₀.read t * st₀.read t + params.fu) * (st₀.read t * st₀.read t) ≠ 0⌝⦄
    gmCandidates (c := Prover c) params t
    ⦃⇓ r s' => ⌜r.1.Scoped s' ∧ r.2.1.Scoped s' ∧ r.2.2.Scoped s' ∧
      s'.read r.1 = (potentialXs params (st₀.read t)).1 ∧
      s'.read r.2.1 = (potentialXs params (st₀.read t)).2.1 ∧
      s'.read r.2.2 = (potentialXs params (st₀.read t)).2.2 ∧ st₀ ≤ s'⌝⦄ := by
  have e1 : ∀ tv : F, params.sqrtNeg3U2MinusUOver2 -
      tv * tv * (tv * tv) * (1 / ((tv * tv + params.fu) * (tv * tv))) * params.sqrtNeg3U2
      = (potentialXs params tv).1 := fun tv => by simp [potentialXs]
  have e2 : ∀ tv : F, -params.u - (potentialXs params tv).1 = (potentialXs params tv).2.1 :=
    fun tv => by simp [potentialXs]
  have e3 : ∀ tv : F, params.u -
      (tv * tv + params.fu) * (tv * tv + params.fu) *
        (1 / ((tv * tv + params.fu) * (tv * tv)) * (tv * tv + params.fu)) * params.inv3U2
      = (potentialXs params tv).2.2 := fun tv => by simp [potentialXs]
  unfold gmCandidates
  dsimp only
  mvcgen
  -- the abscissae: each cell's reading carried along the run to the exit table
  case vc11 =>
    rename_i s₀ h₀ r1 s1 h1 r2 s2 h2 r3 s3 h3 r4 s4 h4 r5 s5 h5 r6 s6 h6 r7 s7 h7 r8 s8 h8
      r9 s9 h9 r10 s10 h10
    simp only [Prover.Reg.iff] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    obtain ⟨rfl, ht, -⟩ := h₀
    obtain ⟨c1, v1, l1⟩ := h1
    obtain ⟨c2, v2, l2⟩ := h2
    obtain ⟨c3, v3, l3⟩ := h3
    obtain ⟨c4, v4, l4⟩ := h4
    obtain ⟨c5, v5, l5⟩ := h5
    obtain ⟨c6, v6, l6⟩ := h6
    obtain ⟨c7, v7, l7⟩ := h7
    obtain ⟨c8, v8, l8⟩ := h8
    obtain ⟨c9, v9, l9⟩ := h9
    obtain ⟨c10, v10, l10⟩ := h10
    set tv := s₀.read t
    have rk : ∀ {u : ProverState F} (k : F), u.read (CVar.const k) = k := fun _ => rfl
    have q1 : ∀ {u}, s1 ≤ u → u.read r1 = tv * tv := fun h => by
      rw [ProverState.read_of_le h c1, v1]
    have qf : ∀ {u}, s1 ≤ u → u.read (CVar.add_ r1 (.const params.fu)) = tv * tv + params.fu :=
      fun h => by rw [ProverState.read, CVar.val_add_, ← ProverState.read, q1 h]; rfl
    have q2 : ∀ {u}, s2 ≤ u → u.read r2 = (tv * tv + params.fu) * (tv * tv) := fun h => by
      rw [ProverState.read_of_le h c2, v2, qf le_rfl, q1 le_rfl]
    have q3 : ∀ {u}, s3 ≤ u →
        u.read r3 = 1 / ((tv * tv + params.fu) * (tv * tv)) := fun h => by
      rw [ProverState.read_of_le h c3, v3, rk, q2 le_rfl]
    have q4 : ∀ {u}, s4 ≤ u → u.read r4 = tv * tv * (tv * tv) := fun h => by
      rw [ProverState.read_of_le h c4, v4, q1 (l2.trans l3)]
    have q5 : ∀ {u}, s5 ≤ u →
        u.read r5 = tv * tv * (tv * tv) * (1 / ((tv * tv + params.fu) * (tv * tv))) :=
      fun h => by rw [ProverState.read_of_le h c5, v5, q4 le_rfl, q3 l4]
    have q6 : ∀ {u}, s6 ≤ u → u.read r6 = tv * tv * (tv * tv) *
        (1 / ((tv * tv + params.fu) * (tv * tv))) * params.sqrtNeg3U2 := fun h => by
      rw [ProverState.read_of_le h c6, v6, q5 le_rfl, rk]
    have q7 : ∀ {u}, s7 ≤ u → u.read r7 =
        1 / ((tv * tv + params.fu) * (tv * tv)) * (tv * tv + params.fu) := fun h => by
      rw [ProverState.read_of_le h c7, v7, q3 (l4.trans (l5.trans l6)),
        qf (l2.trans (l3.trans (l4.trans (l5.trans l6))))]
    have q8 : ∀ {u}, s8 ≤ u → u.read r8 = (tv * tv + params.fu) * (tv * tv + params.fu) :=
      fun h => by
        rw [ProverState.read_of_le h c8, v8,
          qf (l2.trans (l3.trans (l4.trans (l5.trans (l6.trans l7)))))]
    have q9 : ∀ {u}, s9 ≤ u → u.read r9 = (tv * tv + params.fu) * (tv * tv + params.fu) *
        (1 / ((tv * tv + params.fu) * (tv * tv)) * (tv * tv + params.fu)) := fun h => by
      rw [ProverState.read_of_le h c9, v9, q8 le_rfl, q7 l8]
    have q10 : ∀ {u}, s10 ≤ u → u.read r10 = (tv * tv + params.fu) * (tv * tv + params.fu) *
        (1 / ((tv * tv + params.fu) * (tv * tv)) * (tv * tv + params.fu)) * params.inv3U2 :=
      fun h => by rw [ProverState.read_of_le h c10, v10, q9 le_rfl, rk]
    have L6 : s6 ≤ s10 := l7.trans (l8.trans (l9.trans l10))
    have hx1 : s10.read ((CVar.const params.sqrtNeg3U2MinusUOver2).sub_ r6)
        = (potentialXs params tv).1 := by
      rw [ProverState.read, CVar.val_sub_, ← ProverState.read, ← ProverState.read, rk, q6 L6,
        e1]
    refine ⟨CVar.Scoped.sub_ trivial (c6.of_le L6),
      CVar.Scoped.sub_ trivial (CVar.Scoped.sub_ trivial (c6.of_le L6)),
      CVar.Scoped.sub_ trivial c10, hx1, ?_, ?_,
      l1.trans (l2.trans (l3.trans (l4.trans (l5.trans (l6.trans L6)))))⟩
    · rw [ProverState.read, CVar.val_sub_, ← ProverState.read, ← ProverState.read, rk, hx1, e2]
    · rw [ProverState.read, CVar.val_sub_, ← ProverState.read, ← ProverState.read, rk,
        q10 le_rfl, e3]
  all_goals (try simp only [Prover.Reg.iff] at *)
  all_goals (try grind (ematch := 40) (gen := 40) only [CVar.Scoped.of_le, CVar.Scoped.add_,
    CVar.Scoped.sub_, CVar.scoped_const])
  -- the divisor's reading, from the precondition
  all_goals grind (ematch := 40) (gen := 40) [ProverState.read_of_le, CVar.Scoped.of_le,
    CVar.Scoped.add_, CVar.scoped_const, CVar.val_add_, CVar.val]

/-- One candidate's state-relative completeness: the flag reads the residuosity of the
candidate's ordinate square, and the root the advice's root of the flag-selected value. -/
private theorem Prover.gmRoot_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (sqrtF : F → Option F)
    (params : GroupMapParams F) (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : ∀ a, sqrtF a = none → (sqrtF (params.nonResidue * a)).isSome)
    (x : FVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ x.Scoped st₀⌝⦄
    gmRoot (c := Prover c) sqrtF params x
    ⦃⇓ r s' => ⌜r.1.Scoped s' ∧ (↑r.2 : CVar F).Scoped s' ∧
      s'.read r.2 = (if (sqrtF (ySquared params (st₀.read x))).isSome then 1 else 0) ∧
      s'.read r.1 = (sqrtF (if (sqrtF (ySquared params (st₀.read x))).isSome
        then ySquared params (st₀.read x)
        else params.nonResidue * ySquared params (st₀.read x))).getD 0 ∧
      st₀ ≤ s'⌝⦄ := by
  have hsf := fun y => Prover.register
    (Prover.sqrtFlagged_spec (c := c) sqrtF params.nonResidue hroot htwist y)
  unfold gmRoot
  mvcgen [hsf]
  all_goals grind [Prover.Reg.iff, ProverState.read_of_le, CVar.Scoped.of_le,
    CVar.Scoped.add_, CVar.scoped_const, CVar.val_add_, CVar.val, ySquared]

/-- Bits with one set sum to nonzero, given `2 ≠ 0` and `3 ≠ 0`. -/
private theorem flagSum_ne_zero [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {a b c : F}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
    (hone : a = 1 ∨ b = 1 ∨ c = 1) : a + b + c ≠ 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp_all
  all_goals
    first
      | (rw [show (1 : F) + 1 = 2 from by norm_num]; exact h2)
      | (rw [show (1 : F) + 1 + 1 = 3 from by norm_num]; exact h3)

/-- The selection's state-relative completeness: on bit flags with one set, the result reads
the first-flagged candidate's coordinates. -/
private theorem Prover.gmSelect_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (x1 x2 x3 y1 y2 y3 : FVar F) (b1 b2 b3 : BoolVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ x1.Scoped st₀ ∧ x2.Scoped st₀ ∧ x3.Scoped st₀ ∧
      y1.Scoped st₀ ∧ y2.Scoped st₀ ∧ y3.Scoped st₀ ∧
      (↑b1 : CVar F).Scoped st₀ ∧ (↑b2 : CVar F).Scoped st₀ ∧ (↑b3 : CVar F).Scoped st₀ ∧
      (st₀.read b1 = 0 ∨ st₀.read b1 = 1) ∧ (st₀.read b2 = 0 ∨ st₀.read b2 = 1) ∧
      (st₀.read b3 = 0 ∨ st₀.read b3 = 1) ∧
      (st₀.read b1 = 1 ∨ st₀.read b2 = 1 ∨ st₀.read b3 = 1)⌝⦄
    gmSelect (c := Prover c) x1 x2 x3 y1 y2 y3 b1 b2 b3
    ⦃⇓ r s' => ⌜r.x.Scoped s' ∧ r.y.Scoped s' ∧
      s'.read r.x = (if st₀.read b1 = 1 then st₀.read x1
        else if st₀.read b2 = 1 then st₀.read x2 else st₀.read x3) ∧
      s'.read r.y = (if st₀.read b1 = 1 then st₀.read y1
        else if st₀.read b2 = 1 then st₀.read y2 else st₀.read y3) ∧
      st₀ ≤ s'⌝⦄ := by
  have hsum := fun (a b c : F) => @flagSum_ne_zero F _ h2 h3 a b c
  unfold gmSelect
  dsimp only
  mvcgen
  -- the sums: each product carried to the exit table, then the flags case by case
  case vc11 =>
    rename_i s₀ h₀ _ s9 k9 n1 s8 k8 n2 s7 k7 n3 s6 k6 p5 s5 k5 p4 s4 k4 p3 s3 k3 p2 s2 k2
      p1 s1 k1 p0 s k0
    simp only [Prover.Reg.iff] at k9 k8 k7 k6 k5 k4 k3 k2 k1 k0
    obtain ⟨rfl, hx1, hx2, hx3, hy1, hy2, hy3, hb1, hb2, hb3, bb1, bb2, bb3, hone⟩ := h₀
    obtain ⟨c8, v8, l8⟩ := k8
    obtain ⟨c7, v7, l7⟩ := k7
    obtain ⟨c6, v6, l6⟩ := k6
    obtain ⟨c5, v5, l5⟩ := k5
    obtain ⟨c4, v4, l4⟩ := k4
    obtain ⟨c3, v3, l3⟩ := k3
    obtain ⟨c2, v2, l2⟩ := k2
    obtain ⟨c1, v1, l1⟩ := k1
    obtain ⟨c0, v0, l0⟩ := k0
    have ra : ∀ (u : ProverState F) (a b : CVar F),
        u.read (CVar.add_ a b) = u.read a + u.read b := fun _ _ _ => CVar.val_add_ ..
    have rn : ∀ (u : ProverState F) (b : BoolVar F), u.read (Snarky.not b) = 1 - u.read b :=
      fun _ _ => by
        simp only [ProverState.read, Snarky.not, BoolVar.coe_unchecked, CVar.val_sub_, CVar.val]
    have L8 : s₀ ≤ s8 := k9.trans l8
    have L6 : s₀ ≤ s6 := L8.trans (l7.trans l6)
    have L4 : s₀ ≤ s4 := L6.trans (l5.trans l4)
    have L1 : s₀ ≤ s1 := L4.trans (l3.trans (l2.trans l1))
    have q8 : ∀ {u}, s8 ≤ u →
        u.read n1 = if 1 - s₀.read b1 = 1 ∧ s₀.read b2 = 1 then 1 else 0 := fun h => by
      rw [ProverState.read_of_le h c8, v8, rn, ProverState.read_of_le k9 hb1,
        ProverState.read_of_le k9 hb2]
    have q6 : ∀ {u}, s6 ≤ u → u.read n3 = if 1 - s₀.read b1 = 1 ∧
        (if 1 - s₀.read b2 = 1 ∧ s₀.read b3 = 1 then (1 : F) else 0) = 1 then 1 else 0 :=
      fun h => by
        rw [ProverState.read_of_le h c6, v6, rn, ProverState.read_of_le (L8.trans l7) hb1,
          ProverState.read_of_le le_rfl c7, v7, rn, ProverState.read_of_le L8 hb2,
          ProverState.read_of_le L8 hb3]
    have sel : ∀ X1 X2 X3 : F, s₀.read b1 * X1 +
        (if 1 - s₀.read b1 = 1 ∧ s₀.read b2 = 1 then 1 else 0) * X2 +
        (if 1 - s₀.read b1 = 1 ∧
          (if 1 - s₀.read b2 = 1 ∧ s₀.read b3 = 1 then (1 : F) else 0) = 1 then 1 else 0) * X3
        = if s₀.read b1 = 1 then X1 else if s₀.read b2 = 1 then X2 else X3 := by
      intro X1 X2 X3
      rcases bb1 with e1 | e1 <;> rcases bb2 with e2 | e2 <;> rcases bb3 with e3 | e3 <;>
        simp [e1, e2, e3] at hone ⊢
    refine ⟨CVar.Scoped.add_ (CVar.Scoped.add_ c0 (c1.of_le l0)) (c2.of_le (l1.trans l0)),
      CVar.Scoped.add_ (CVar.Scoped.add_ (c3.of_le (l2.trans (l1.trans l0)))
        (c4.of_le (l3.trans (l2.trans (l1.trans l0)))))
        (c5.of_le (l4.trans (l3.trans (l2.trans (l1.trans l0))))), ?_, ?_, L1.trans l0⟩
    · rw [ra, ra, v0, ProverState.read_of_le l0 c1, v1, ProverState.read_of_le (l1.trans l0) c2,
        v2, ProverState.read_of_le L1 hb1, ProverState.read_of_le L1 hx1,
        q8 (l7.trans (l6.trans (l5.trans (l4.trans (l3.trans l2))))),
        ProverState.read_of_le (L4.trans (l3.trans l2)) hx2, q6 (l5.trans (l4.trans l3)),
        ProverState.read_of_le (L4.trans l3) hx3, sel]
    · rw [ra, ra, ProverState.read_of_le (l2.trans (l1.trans l0)) c3, v3,
        ProverState.read_of_le (l3.trans (l2.trans (l1.trans l0))) c4, v4,
        ProverState.read_of_le (l4.trans (l3.trans (l2.trans (l1.trans l0)))) c5, v5,
        ProverState.read_of_le L4 hb1, ProverState.read_of_le L4 hy1,
        q8 (l7.trans (l6.trans l5)), ProverState.read_of_le (L6.trans l5) hy2, q6 le_rfl,
        ProverState.read_of_le L6 hy3, sel]
  all_goals (try simp only [Prover.Reg.iff] at *)
  all_goals (try grind (ematch := 40) (gen := 40) only [CVar.Scoped.of_le, CVar.Scoped.add_,
    CVar.Scoped.sub_, CVar.scoped_const, Snarky.not_scoped])
  -- the flag sum and the conjunctions' bits, from the precondition
  all_goals grind (ematch := 40) (gen := 40) [ProverState.read_of_le, CVar.Scoped.of_le,
    CVar.Scoped.add_, CVar.Scoped.sub_, CVar.scoped_const, CVar.val_add_, CVar.val_sub_,
    CVar.val, Snarky.not, BoolVar.coe_unchecked, Snarky.not_scoped]

/-- **Completeness.** The honest run's result reads the pure map's point. Conditions: the
`div` divisor `(t² + f(u))·t²` is nonzero and some candidate's ordinate square has a root
(Shallue–van de Woestijne); hypotheses: `sqrtF`'s roots are genuine, a rootless value's
non-residue twist has a root, and `2, 3 ≠ 0` keep the flag sum nonzero. -/
theorem Prover.groupMapCircuit_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (sqrtF : F → Option F)
    (params : GroupMapParams F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : ∀ a, sqrtF a = none → (sqrtF (params.nonResidue * a)).isSome)
    (t : FVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ t.Scoped st₀ ∧
      (st₀.read t * st₀.read t + params.fu) * (st₀.read t * st₀.read t) ≠ 0 ∧
      ((sqrtF (ySquared params (potentialXs params (st₀.read t)).1)).isSome ∨
        (sqrtF (ySquared params (potentialXs params (st₀.read t)).2.1)).isSome ∨
        (sqrtF (ySquared params (potentialXs params (st₀.read t)).2.2)).isSome)⌝⦄
    groupMapCircuit (c := Prover c) sqrtF params t
    ⦃⇓ r s' => ⌜r.x.Scoped s' ∧ r.y.Scoped s' ∧
      s'.read r.x = (groupMapPure sqrtF params (st₀.read t)).1 ∧
      s'.read r.y = (groupMapPure sqrtF params (st₀.read t)).2 ∧ st₀ ≤ s'⌝⦄ := by
  have hc := Prover.register (Prover.gmCandidates_spec (c := c) params t)
  have hr := fun x => Prover.register (Prover.gmRoot_spec (c := c) sqrtF params hroot htwist x)
  have hs := fun x1 x2 x3 y1 y2 y3 b1 b2 b3 => Prover.register
    (Prover.gmSelect_spec (c := c) h2 h3 x1 x2 x3 y1 y2 y3 b1 b2 b3)
  rw [groupMapCircuit_stages]
  mvcgen [hc, hr, hs]
  -- the selection's condition and the map's post: the candidates' and the roots' readings,
  -- carried to the selection's entry table
  case' vc6 => rename_i rs ss; intro ks
  case' vc5 | vc6 =>
    rename_i s₀ h₀ rc sc kc r1 s1 k1 r2 s2 k2 r3 s3 k3
    obtain ⟨rfl, -, -, hsome⟩ := h₀
    obtain ⟨cx1, cx2, cx3, vx1, vx2, vx3, lc⟩ := Prover.Reg.iff.mp kc
    obtain ⟨cy1, cb1, vb1, vy1, l1⟩ := Prover.Reg.iff.mp k1
    obtain ⟨cy2, cb2, vb2, vy2, l2⟩ := Prover.Reg.iff.mp k2
    obtain ⟨cy3, cb3, vb3, vy3, l3⟩ := Prover.Reg.iff.mp k3
    have L : sc ≤ s3 := l1.trans (l2.trans l3)
    rw [vx1] at vb1 vy1
    rw [ProverState.read_of_le l1 cx2, vx2] at vb2 vy2
    rw [ProverState.read_of_le (l1.trans l2) cx3, vx3] at vb3 vy3
    rw [← ProverState.read_of_le (l2.trans l3) cb1] at vb1
    rw [← ProverState.read_of_le (l2.trans l3) cy1] at vy1
    rw [← ProverState.read_of_le l3 cb2] at vb2
    rw [← ProverState.read_of_le l3 cy2] at vy2
    rw [← ProverState.read_of_le L cx1] at vx1
    rw [← ProverState.read_of_le L cx2] at vx2
    rw [← ProverState.read_of_le L cx3] at vx3
  case vc5 =>
    refine ⟨trivial, cx1.of_le L, cx2.of_le L, cx3.of_le L, cy1.of_le (l2.trans l3),
      cy2.of_le l3, cy3, cb1.of_le (l2.trans l3), cb2.of_le l3, cb3, ?_, ?_, ?_, ?_⟩
    · rw [vb1]; split <;> simp
    · rw [vb2]; split <;> simp
    · rw [vb3]; split <;> simp
    · rw [vb1, vb2, vb3]
      rcases hsome with h | h | h <;> simp [h]
  case vc6 =>
    obtain ⟨csx, csy, vsx, vsy, ls⟩ := Prover.Reg.iff.mp ks
    rw [vb1, vb2, vx1, vx2, vx3] at vsx
    rw [vb1, vb2, vy1, vy2, vy3] at vsy
    refine ⟨csx, csy, vsx.trans ?_, vsy.trans ?_, lc.trans (L.trans ls)⟩
    all_goals
      rcases e1 : sqrtF (ySquared params (potentialXs params (s₀.read t)).1) with _ | v1
      · rcases e2 : sqrtF (ySquared params (potentialXs params (s₀.read t)).2.1) with _ | v2
        · rcases e3 : sqrtF (ySquared params (potentialXs params (s₀.read t)).2.2) with _ | v3
          · simp [e1, e2, e3] at hsome
          · simp [groupMapPure, e1, e2, e3]
        · simp [groupMapPure, e1, e2]
      · simp [groupMapPure, e1]
  all_goals (try simp only [Prover.Reg.iff] at *)
  all_goals grind (ematch := 40) (gen := 40) only [CVar.Scoped.of_le]

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
`Prover.groupMapCircuit_spec`'s twist hypothesis. -/
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

/-- **Wire-level completeness.** The honest run's result reads
`Poseidon.GroupMap.toGroup`'s point: `Prover.groupMapCircuit_spec` with the spec's own
Tonelli–Shanks root as advice, its root and twist hypotheses discharged
(`CompElliptic.Fields.TonelliShanks.sqrt?_mul_self`, `sqrt?_twist`), `2 ≠ 0` from `q ≠ 2`
and `3 ≠ 0` from `q ≠ 3`. The nonzero `div` divisor and the candidate disjunction (as
`IsSquare`) remain conditions. -/
theorem Prover.groupMapCircuit_toGroup_spec {c : Type} [BasicSystem (ZMod q) c]
    [ConstraintHolds (ZMod q) c] [LawfulBasicSystem (ZMod q) c]
    (spec : _root_.Poseidon.GroupMap.Spec q) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (t : FVar (ZMod q)) (st₀ : ProverState (ZMod q)) :
    ⦃fun s => ⌜s = st₀ ∧ t.Scoped st₀ ∧
      (st₀.read t * st₀.read t + spec.fu) * (st₀.read t * st₀.read t) ≠ 0 ∧
      (IsSquare (ySquared (.ofSpec spec) (potentialXs (.ofSpec spec) (st₀.read t)).1) ∨
        IsSquare (ySquared (.ofSpec spec) (potentialXs (.ofSpec spec) (st₀.read t)).2.1) ∨
        IsSquare (ySquared (.ofSpec spec) (potentialXs (.ofSpec spec) (st₀.read t)).2.2))⌝⦄
    groupMapCircuit (c := Prover c) spec.sqrt.sqrt? (.ofSpec spec) t
    ⦃⇓ r s' => ⌜r.x.Scoped s' ∧ r.y.Scoped s' ∧
      s'.read r.x = (_root_.Poseidon.GroupMap.toGroup spec (st₀.read t)).x ∧
      s'.read r.y = (_root_.Poseidon.GroupMap.toGroup spec (st₀.read t)).y ∧ st₀ ≤ s'⌝⦄ := by
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
  have hgm := Prover.register (Prover.groupMapCircuit_spec (c := c) spec.sqrt.sqrt?
    (.ofSpec spec) (Ring.two_ne_zero hchar) hthree
    (fun _ _ h => TonelliShanks.sqrt?_mul_self spec.sqrt h)
    (sqrt?_twist spec.sqrt hchar
      (fun h => spec.nonResidue_spec
        (by rw [show spec.nonResidue = 0 from h]; exact ⟨0, by ring⟩))
      spec.nonResidue_spec) t)
  mvcgen [hgm]
  case vc1 =>
    rename_i _ h
    obtain ⟨rfl, ht, hne, hsq⟩ := h
    exact ⟨trivial, ht, hne, hsq.imp (hsome _) (Or.imp (hsome _) (hsome _))⟩
  case vc2 =>
    rename_i _ h _ _
    obtain ⟨rfl, -⟩ := h
    intro hr
    simpa only [groupMapPure_toGroup] using Prover.Reg.iff.mp hr

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
