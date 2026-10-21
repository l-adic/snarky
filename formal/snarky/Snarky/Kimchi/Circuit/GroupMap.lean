import Snarky.DSL.Field
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

open Snarky

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

open Std.WP in
/-- The flagged root's contract: the flag is a bit, and the root squares to the operand
where the flag is set, to its non-residue twist where it is clear. -/
@[spec] private theorem sqrtFlagged_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (sqrtF : F → Option F) (nonResidue : F) (x : FVar F) :
    ⦃fun _ => True⦄
    sqrtFlagged (c := Builder V c) sqrtF nonResidue x
    ⦃fun r _ => ∃ bb : Bool, (↑r.2 : CVar F).val V = bit bb ∧
      r.1.val V * r.1.val V = if bb then x.val V else nonResidue * x.val V⦄ := by
  simp only [sqrtFlagged, select_fvar]
  vcgen
  rename_i hbool _ hsel _ _ _ _ hsq
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

open Std.WP in
/-- **Soundness.** Any satisfying valuation reads the result as an on-curve pair
(`y² = x³ + b`) whose abscissa is one of the three `potentialXs` candidates: a flag is
forced set, the selectors pick one branch, and that branch's root is the ordinate. The
advice is universally quantified. -/
theorem groupMapCircuit_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (sqrtF : F → Option F) (params : GroupMapParams F) (t : FVar F) :
    ⦃fun _ => True⦄
    groupMapCircuit (c := Builder V c) sqrtF params t
    ⦃fun r _ => (r.x.val V = (potentialXs params (t.val V)).1 ∨
        r.x.val V = (potentialXs params (t.val V)).2.1 ∨
        r.x.val V = (potentialXs params (t.val V)).2.2) ∧
      r.y.val V * r.y.val V = ySquared params (r.x.val V)⦄ := by
  simp only [groupMapCircuit]
  vcgen
  rename_i ht2 _ halphaInv _ halpha _ ht4 _ ht4Alpha _ htemp1 _ ht2Inv _ ht2PlusFuSq _ htemp2a _
    htemp2 _ _ hxSq1 _ _ hxCu1 _ _ _ hsf1 _ _ hxSq2 _ _ hxCu2 _ _ _ hsf2 _ hxSq3 _ hxCu3 _ _ _ hsf3
    _ _ hnz _ hx2First _ hnb2AndB3 _ hx3First _ ht3y _ ht2y _ ht1y _ ht3x _ ht2x _ ht1x
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

open Std.WP in
/-- **Soundness, first-flagged.** The selected candidate is the first whose flag is set, and
every earlier candidate's flag is clear with its clearance certified: a root of the
non-residue twist of its ordinate square. The advice is universally quantified. -/
theorem groupMapCircuit_first_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (sqrtF : F → Option F) (params : GroupMapParams F) (t : FVar F) :
    ⦃fun _ => True⦄
    groupMapCircuit (c := Builder V c) sqrtF params t
    ⦃fun r _ => (r.x.val V = (potentialXs params (t.val V)).1 ∧
        r.y.val V * r.y.val V = ySquared params (potentialXs params (t.val V)).1) ∨
      ((∃ y : F, y * y = params.nonResidue * ySquared params (potentialXs params (t.val V)).1) ∧
        r.x.val V = (potentialXs params (t.val V)).2.1 ∧
        r.y.val V * r.y.val V = ySquared params (potentialXs params (t.val V)).2.1) ∨
      ((∃ y : F, y * y = params.nonResidue * ySquared params (potentialXs params (t.val V)).1) ∧
        (∃ y : F, y * y = params.nonResidue * ySquared params (potentialXs params (t.val V)).2.1) ∧
        r.x.val V = (potentialXs params (t.val V)).2.2 ∧
        r.y.val V * r.y.val V = ySquared params (potentialXs params (t.val V)).2.2)⦄ := by
  simp only [groupMapCircuit]
  vcgen
  rename_i ht2 _ halphaInv _ halpha _ ht4 _ ht4Alpha _ htemp1 _ ht2Inv _ ht2PlusFuSq _ htemp2a _
    htemp2 _ _ hxSq1 _ _ hxCu1 y1 _ _ hsf1 _ _ hxSq2 _ _ hxCu2 y2 _ _ hsf2 _ hxSq3 _ hxCu3 _ _ _
    hsf3 _ _ hnz _ hx2First _ hnb2AndB3 _ hx3First _ ht3y _ ht2y _ ht1y _ ht3x _ ht2x _ ht1x
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
    exact ⟨y1.val V, by simpa [ySquared, CVar.val_add_, hxCu1, hxSq1, hx1v] using hy1⟩
  have htw2 : bb2 = false → ∃ y : F,
      y * y = params.nonResidue * ySquared params (potentialXs params (t.val V)).2.1 := by
    rintro rfl
    exact ⟨y2.val V, by simpa [ySquared, CVar.val_add_, hxCu2, hxSq2, hx2v] using hy2⟩
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

The honest run at the prover's reading (`Snarky.Prover.VCGen`): the flagged root's law, then the
map's law over its stages. -/

section ProverReading

open Snarky.Prover Std.WP

/-! The advices' runs: each returns its value wherever its operand is in scope. -/

/-- `isQRWit` returns whether `sqrtF` finds a root of the operand's reading. -/
private theorem Prover.isQRWit_run [Field F] {sqrtF : F → Option F} {x : FVar F}
    {s : ProverState F} (hx : x.Scoped s) :
    (isQRWit sqrtF x).run s.env = .ok (sqrtF (x.val s.env.get)).isSome := by
  simp [isQRWit, AsProver.readCVar_run hx]

/-- `sqrtWit` returns `sqrtF`'s root of the operand's reading, `0` when there is none. -/
private theorem Prover.sqrtWit_run [Field F] {sqrtF : F → Option F} {x : FVar F}
    {s : ProverState F} (hx : x.Scoped s) :
    (sqrtWit sqrtF x).run s.env = .ok ((sqrtF (x.val s.env.get)).getD 0) := by
  simp [sqrtWit, AsProver.readCVar_run hx]

/-- The flagged root's value: `sqrtF`'s root of the operand where it finds one, of the operand's
non-residue twist where it does not. -/
private def flaggedRoot [Mul F] [Zero F] (sqrtF : F → Option F) (nonResidue a : F) : F :=
  (sqrtF (if (sqrtF a).isSome then a else nonResidue * a)).getD 0

/-- The flagged root's completeness: with genuine roots, and every rootless value's non-residue
twist rooted, the root reads `flaggedRoot` and the flag reads whether `sqrtF` finds a root. -/
private theorem Prover.sqrtFlagged_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (sqrtF : F → Option F) (nonResidue : F)
    (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : ∀ a, sqrtF a = none → (sqrtF (nonResidue * a)).isSome)
    (x : FVar F) (a : F) :
    ⦃Reads x a⦄ sqrtFlagged (c := Prover c) sqrtF nonResidue x
    ⦃fun r ↦ Reads r (flaggedRoot sqrtF nonResidue a, (sqrtF a).isSome)⦄ := by
  -- the advice's root squares to the selected operand
  have hsq : flaggedRoot sqrtF nonResidue a * flaggedRoot sqrtF nonResidue a
      = if (sqrtF a).isSome then a else nonResidue * a := by
    have hsome : (sqrtF (if (sqrtF a).isSome then a else nonResidue * a)).isSome := by
      rcases hcase : sqrtF a with _ | y
      · simpa [hcase] using htwist a hcase
      · simp [hcase]
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsome
    rw [flaggedRoot, hy]
    exact hroot _ y hy
  have hq := fun x' : FVar F ↦
    Spec.witness (c := c) (isQRWit sqrtF x') (sqrtF a).isSome valid_bool
  have hs := fun (b' : BoolVar F) (m : FVar F) ↦
    Prover.selectField_spec (c := c) b' x m (sqrtF a).isSome a (nonResidue * a)
  have hw := fun x' : FVar F ↦
    Spec.witness (c := c) (sqrtWit sqrtF x') (flaggedRoot sqrtF nonResidue a) valid_fvar
  have ha := fun y m : FVar F ↦
    hsq ▸ Prover.assertSquare_spec (c := c) y m (flaggedRoot sqrtF nonResidue a)
  unfold sqrtFlagged
  simp only [select_fvar]
  vcgen [hq, hs, hw, ha]
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, Reads.boolVar_apply, Reads.prod_apply,
      Prover.isQRWit_run, Prover.sqrtWit_run, flaggedRoot])

/-! ### The map, by stages

The law is stated per stage, over the same program regrouped, each stage's result read in closed
form of its operands' values: the candidate abscissae, one candidate's ordinate square and flagged
root, and the flag-weighted selection. `groupMapCircuit_stages` is the regrouping; the candidates
are split once more after their `α` stage (`gmCandidates_stages`), where the products that follow
would otherwise share one contract pattern. -/

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

/-! #### The candidates -/

/-- `gmCandidates` is its `α` stage followed by the two abscissa terms. -/
private theorem gmCandidates_stages [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (params : GroupMapParams F) (t : FVar F) :
    gmCandidates (c := c) params t = (do
      let (t2, alpha) ← (do
        let t2 ← mul t t
        let alphaInv ← mul (CVar.add_ t2 (.const params.fu)) t2
        let alpha ← div (.const 1) alphaInv
        pure (t2, alpha) : CircuitM F c (FVar F × FVar F))
      let t4 ← mul t2 t2
      let t4Alpha ← mul t4 alpha
      let temp1 ← mul t4Alpha (.const params.sqrtNeg3U2)
      let t2Inv ← mul alpha (CVar.add_ t2 (.const params.fu))
      let t2PlusFuSq ← mul (CVar.add_ t2 (.const params.fu)) (CVar.add_ t2 (.const params.fu))
      let temp2a ← mul t2PlusFuSq t2Inv
      let temp2 ← mul temp2a (.const params.inv3U2)
      pure (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) temp1,
        CVar.sub_ (.const (-params.u)) (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) temp1),
        CVar.sub_ (.const params.u) temp2)) := by
  simp only [gmCandidates, bind_assoc, pure_bind]

/-- The candidates' completeness: with the divisor's reading nonzero, the abscissae read the pure
candidates. -/
private theorem Prover.gmCandidates_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (params : GroupMapParams F) (t : FVar F)
    (v : F) (hne : (v * v + params.fu) * (v * v) ≠ 0) :
    ⦃Reads t v⦄ gmCandidates (c := Prover c) params t
    ⦃fun r ↦ Reads r (potentialXs params v)⦄ := by
  rw [gmCandidates_stages]
  -- the `α` stage: the square and the inverse
  refine Triple.bind _ _ (fun r : FVar F × FVar F ↦
    Reads r (v * v, 1 / ((v * v + params.fu) * (v * v)))) ?_ ?_
  · have h1 := Prover.mul_spec (c := c) t t v v
    have h2 := fun t2 : FVar F ↦
      Prover.mul_spec (c := c) (CVar.add_ t2 (.const params.fu)) t2 (v * v + params.fu) (v * v)
    have h3 := fun y : FVar F ↦
      Prover.div_spec (c := c) (.const 1) y 1 ((v * v + params.fu) * (v * v)) hne
    vcgen [h1, h2, h3]
    all_goals prover_assert with
      (intros; simp_all [Reads.fvar_apply, Reads.prod_apply, CVar.val])
  -- the abscissa terms at the stage's readings
  · rintro ⟨t2, alpha⟩
    dsimp only
    have h4 := Prover.mul_spec (c := c) t2 t2 (v * v) (v * v)
    have h5 := fun t4 : FVar F ↦
      Prover.mul_spec (c := c) t4 alpha (v * v * (v * v)) (1 / ((v * v + params.fu) * (v * v)))
    have h6 := fun r : FVar F ↦ Prover.mul_spec (c := c) r (.const params.sqrtNeg3U2)
      (v * v * (v * v) * (1 / ((v * v + params.fu) * (v * v)))) params.sqrtNeg3U2
    have h7 := Prover.mul_spec (c := c) alpha (CVar.add_ t2 (.const params.fu))
      (1 / ((v * v + params.fu) * (v * v))) (v * v + params.fu)
    have h8 := Prover.mul_spec (c := c) (CVar.add_ t2 (.const params.fu))
      (CVar.add_ t2 (.const params.fu)) (v * v + params.fu) (v * v + params.fu)
    have h10 := fun r : FVar F ↦ Prover.mul_spec (c := c) r (.const params.inv3U2)
      ((v * v + params.fu) * (v * v + params.fu) *
        (1 / ((v * v + params.fu) * (v * v)) * (v * v + params.fu))) params.inv3U2
    -- the remaining product's law stays in the context: listed, it would be taken for every
    -- product
    have h9 := fun x y : FVar F ↦ Prover.mul_spec (c := c) x y
      ((v * v + params.fu) * (v * v + params.fu))
      (1 / ((v * v + params.fu) * (v * v)) * (v * v + params.fu))
    vcgen [h4, h5, h6, h7, h8, h10]
    all_goals prover_assert with
      (intros; simp_all [Reads.fvar_apply, Reads.prod_apply, CVar.val, potentialXs])


/-! #### One root -/

/-- One candidate's completeness: the flag reads whether `sqrtF` finds a root of the candidate's
ordinate square, and the root reads that square's `flaggedRoot`. -/
private theorem Prover.gmRoot_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (sqrtF : F → Option F)
    (params : GroupMapParams F) (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : ∀ a, sqrtF a = none → (sqrtF (params.nonResidue * a)).isSome)
    (x : FVar F) (a : F) :
    ⦃Reads x a⦄ gmRoot (c := Prover c) sqrtF params x
    ⦃fun r ↦ Reads r (flaggedRoot sqrtF params.nonResidue (ySquared params a),
      (sqrtF (ySquared params a)).isSome)⦄ := by
  have h1 := Prover.mul_spec (c := c) x x a a
  -- the cube's law is left in the context: listed, it would also be taken for the square
  have h2 := fun y : FVar F ↦ Prover.mul_spec (c := c) y x (a * a) a
  have hsf := fun y : FVar F ↦
    Prover.sqrtFlagged_spec (c := c) sqrtF params.nonResidue hroot htwist y (ySquared params a)
  unfold gmRoot
  vcgen [h1, hsf]
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, ySquared])

/-! #### The selection -/

/-- Bits with one set sum to nonzero, given `2 ≠ 0` and `3 ≠ 0`. -/
private theorem flagSum_ne_zero [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {b1 b2 b3 : Bool} (hone : b1 = true ∨ b2 = true ∨ b3 = true) :
    (bit b1 + bit b2 + bit b3 : F) ≠ 0 := by
  have h3' : (1 : F) + 1 + 1 ≠ 0 := by rwa [show (1 : F) + 1 + 1 = 3 by norm_num]
  rcases b1 <;> rcases b2 <;> rcases b3 <;>
    simp_all [bit, one_add_one_eq_two]

/-- The selection's completeness: on bits with one set, the result reads the first-flagged
candidate's coordinates. -/
private theorem Prover.gmSelect_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (x1 x2 x3 y1 y2 y3 : FVar F) (b1 b2 b3 : BoolVar F) (a1 a2 a3 w1 w2 w3 : F)
    (bb1 bb2 bb3 : Bool) (hone : bb1 = true ∨ bb2 = true ∨ bb3 = true) :
    ⦃Reads x1 a1 ⊓ Reads x2 a2 ⊓ Reads x3 a3 ⊓ Reads y1 w1 ⊓ Reads y2 w2 ⊓ Reads y3 w3 ⊓
      Reads b1 bb1 ⊓ Reads b2 bb2 ⊓ Reads b3 bb3⦄
    gmSelect (c := Prover c) x1 x2 x3 y1 y2 y3 b1 b2 b3
    ⦃fun r ↦ Reads r.x (if bb1 then a1 else if bb2 then a2 else a3) ⊓
      Reads r.y (if bb1 then w1 else if bb2 then w2 else w3)⦄ := by
  have hn := Prover.assertNonZero_spec (c := c) (CVar.add_ (CVar.add_ (↑b1) (↑b2)) (↑b3))
    (bit bb1 + bit bb2 + bit bb3) (flagSum_ne_zero h2 h3 hone)
  have ha1 := Prover.and_spec (c := c) (Snarky.not b1) b2 (!bb1) bb2
  have ha2 := Prover.and_spec (c := c) (Snarky.not b2) b3 (!bb2) bb3
  have hy3 := fun s : BoolVar F ↦
    Prover.mul_spec (c := c) (↑s) y3 (bit (!bb1 && (!bb2 && bb3))) w3
  have hy2 := fun s : BoolVar F ↦ Prover.mul_spec (c := c) (↑s) y2 (bit (!bb1 && bb2)) w2
  have hy1 := Prover.mul_spec (c := c) (↑b1) y1 (bit bb1) w1
  have hx3 := fun s : BoolVar F ↦
    Prover.mul_spec (c := c) (↑s) x3 (bit (!bb1 && (!bb2 && bb3))) a3
  have hx2 := fun s : BoolVar F ↦ Prover.mul_spec (c := c) (↑s) x2 (bit (!bb1 && bb2)) a2
  have hx1 := Prover.mul_spec (c := c) (↑b1) x1 (bit bb1) a1
  -- the third conjunction's law stays in the context: listed, it would also be taken for the
  -- first
  have ha3 := fun r : BoolVar F ↦
    Prover.and_spec (c := c) (Snarky.not b1) r (!bb1) (!bb2 && bb3)
  unfold gmSelect
  dsimp only
  vcgen [hn, ha1, ha2, hy3, hy2, hy1, hx3, hx2, hx1]
  all_goals prover_assert with
    (intros; first
      | (simp_all [Reads.fvar_apply, Reads.boolVar_apply]; done)
      | (simp_all [Reads.fvar_apply, Reads.boolVar_apply, Snarky.not, CVar.val_sub_, CVar.val,
          bit]; (try (split_ifs <;> simp_all))))


/-! #### The map -/

/-- **Completeness.** The honest run's result reads the pure map's point at the input's value
`v`. Hypotheses: the `div` divisor `(v² + f(u))·v²` is nonzero, some candidate's ordinate square
has a root (Shallue–van de Woestijne), `sqrtF`'s roots are genuine, a rootless value's
non-residue twist has a root, and `2, 3 ≠ 0` keep the flag sum nonzero. -/
theorem Prover.groupMapCircuit_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (sqrtF : F → Option F)
    (params : GroupMapParams F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : ∀ a, sqrtF a = none → (sqrtF (params.nonResidue * a)).isSome)
    (t : FVar F) (v : F) (hne : (v * v + params.fu) * (v * v) ≠ 0)
    (hsome : (sqrtF (ySquared params (potentialXs params v).1)).isSome ∨
      (sqrtF (ySquared params (potentialXs params v).2.1)).isSome ∨
      (sqrtF (ySquared params (potentialXs params v).2.2)).isSome) :
    ⦃Reads t v⦄ groupMapCircuit (c := Prover c) sqrtF params t
    ⦃fun r ↦ Reads r.x (groupMapPure sqrtF params v).1 ⊓
      Reads r.y (groupMapPure sqrtF params v).2⦄ := by
  rw [groupMapCircuit_stages]
  refine Triple.bind _ _ _ (Prover.gmCandidates_spec (c := c) params t v hne) fun xs ↦ ?_
  obtain ⟨x1, x2, x3⟩ := xs
  -- the candidates as named values; the pure map is the first-flagged one's flagged root
  obtain ⟨⟨X1, X2, X3⟩, hX⟩ : ∃ X, potentialXs params v = X := ⟨_, rfl⟩
  rw [hX] at hsome ⊢
  dsimp only at hsome ⊢
  have hpure : groupMapPure sqrtF params v =
      (if (sqrtF (ySquared params X1)).isSome then X1
        else if (sqrtF (ySquared params X2)).isSome then X2 else X3,
       if (sqrtF (ySquared params X1)).isSome then flaggedRoot sqrtF params.nonResidue
          (ySquared params X1)
        else if (sqrtF (ySquared params X2)).isSome then flaggedRoot sqrtF params.nonResidue
          (ySquared params X2)
        else flaggedRoot sqrtF params.nonResidue (ySquared params X3)) := by
    simp only [groupMapPure, hX, flaggedRoot]
    rcases e1 : sqrtF (ySquared params X1) with _ | w1
    · rcases e2 : sqrtF (ySquared params X2) with _ | w2
      · rcases e3 : sqrtF (ySquared params X3) with _ | w3
        · simp [e1, e2, e3] at hsome
        · simp [e3]
      · simp [e2]
    · simp [e1]
  rw [hpure]
  have hr1 := Prover.gmRoot_spec (c := c) sqrtF params hroot htwist x1 X1
  have hr2 := Prover.gmRoot_spec (c := c) sqrtF params hroot htwist x2 X2
  have hr3 := Prover.gmRoot_spec (c := c) sqrtF params hroot htwist x3 X3
  have hs := fun (y1 y2 y3 : FVar F) (b1 b2 b3 : BoolVar F) ↦
    Prover.gmSelect_spec (c := c) h2 h3 x1 x2 x3 y1 y2 y3 b1 b2 b3 X1 X2 X3
      (flaggedRoot sqrtF params.nonResidue (ySquared params X1))
      (flaggedRoot sqrtF params.nonResidue (ySquared params X2))
      (flaggedRoot sqrtF params.nonResidue (ySquared params X3)) _ _ _ hsome
  vcgen [hr1, hr2, hr3, hs]
  all_goals prover_assert with (intros; simp_all [Reads.prod_apply])

end ProverReading

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

open Std.WP in
/-- **Wire-level soundness.** Any satisfying valuation reads the result as a point of the
wire spec's curve (`CompElliptic.CurveForms.ShortWeierstrass.OnCurve`) at one of the
candidate abscissae. The advice is universally quantified. -/
theorem groupMapCircuit_onCurve_spec {V : Valuation (ZMod q)} {c : Type}
    [BasicSystem (ZMod q) c] [ConstraintHolds (ZMod q) c] [LawfulBasicSystem (ZMod q) c]
    (spec : _root_.Poseidon.GroupMap.Spec q)
    (sqrtF : ZMod q → Option (ZMod q)) (t : FVar (ZMod q)) :
    ⦃fun _ => True⦄
    groupMapCircuit (c := Builder V c) sqrtF (.ofSpec spec) t
    ⦃fun r _ => (r.x.val V = (potentialXs (.ofSpec spec) (t.val V)).1 ∨
        r.x.val V = (potentialXs (.ofSpec spec) (t.val V)).2.1 ∨
        r.x.val V = (potentialXs (.ofSpec spec) (t.val V)).2.2) ∧
      OnCurve spec.E.A spec.E.B (r.x.val V, r.y.val V)⦄ := by
  constructor
  intro nv h hsat
  obtain ⟨hx, hy⟩ := (groupMapCircuit_spec (c := c) (V := V) sqrtF
    (.ofSpec spec) t).le_wp nv h hsat
  refine ⟨hx, ?_⟩
  show _ ^ 2 = _ ^ 3 + spec.E.A * _ + spec.E.B
  rw [spec.hA]
  simp only [ySquared] at hy
  rw [show ((GroupMapParams.ofSpec spec).b : ZMod q) = spec.E.B from rfl] at hy
  linear_combination hy

open Snarky.Prover Std.WP in
/-- **Wire-level completeness.** The honest run's result reads
`Poseidon.GroupMap.toGroup`'s point: `Prover.groupMapCircuit_spec` with the spec's own
Tonelli–Shanks root as advice, its root and twist hypotheses discharged
(`CompElliptic.Fields.TonelliShanks.sqrt?_mul_self`, `sqrt?_twist`), `2 ≠ 0` from `q ≠ 2`
and `3 ≠ 0` from `q ≠ 3`. The nonzero `div` divisor and the candidate disjunction (as
`IsSquare`) remain hypotheses. -/
theorem Prover.groupMapCircuit_toGroup_spec {c : Type} [BasicSystem (ZMod q) c]
    [ConstraintHolds (ZMod q) c] [LawfulBasicSystem (ZMod q) c]
    (spec : _root_.Poseidon.GroupMap.Spec q) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (t : FVar (ZMod q)) (v : ZMod q) (hne : (v * v + spec.fu) * (v * v) ≠ 0)
    (hsq : IsSquare (ySquared (.ofSpec spec) (potentialXs (.ofSpec spec) v).1) ∨
      IsSquare (ySquared (.ofSpec spec) (potentialXs (.ofSpec spec) v).2.1) ∨
      IsSquare (ySquared (.ofSpec spec) (potentialXs (.ofSpec spec) v).2.2)) :
    ⦃Reads t v⦄ groupMapCircuit (c := Prover c) spec.sqrt.sqrt? (.ofSpec spec) t
    ⦃fun r ↦ Reads r.x (_root_.Poseidon.GroupMap.toGroup spec v).x ⊓
      Reads r.y (_root_.Poseidon.GroupMap.toGroup spec v).y⦄ := by
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
  have hgm := Prover.groupMapCircuit_spec (c := c) spec.sqrt.sqrt? (.ofSpec spec)
    (Ring.two_ne_zero hchar) hthree (fun _ _ h => TonelliShanks.sqrt?_mul_self spec.sqrt h)
    (sqrt?_twist spec.sqrt hchar
      (fun h => spec.nonResidue_spec
        (by rw [show spec.nonResidue = 0 from h]; exact ⟨0, by ring⟩))
      spec.nonResidue_spec) t v hne
    (hsq.imp (hsome _) (Or.imp (hsome _) (hsome _)))
  rwa [groupMapPure_toGroup] at hgm

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

open Std.WP in
/-- **Wire-level soundness, up to sign.** When no ordinate square vanishes (`hnz`), any
satisfying valuation reads the result as `toGroup`'s point up to the ordinate's sign: the
constraints pin the root's square, not its sign. The advice is universally quantified. -/
theorem groupMapCircuit_toGroup_spec {V : Valuation (ZMod q)} {c : Type}
    [BasicSystem (ZMod q) c] [ConstraintHolds (ZMod q) c] [LawfulBasicSystem (ZMod q) c]
    (spec : _root_.Poseidon.GroupMap.Spec q)
    (hnz : ∀ x : ZMod q, _root_.Poseidon.GroupMap.curveEqn spec x ≠ 0)
    (sqrtF : ZMod q → Option (ZMod q)) (t : FVar (ZMod q)) :
    ⦃fun _ => True⦄
    groupMapCircuit (c := Builder V c) sqrtF (.ofSpec spec) t
    ⦃fun r _ => r.x.val V = (_root_.Poseidon.GroupMap.toGroup spec (t.val V)).x ∧
      (r.y.val V = (_root_.Poseidon.GroupMap.toGroup spec (t.val V)).y ∨
        r.y.val V = -(_root_.Poseidon.GroupMap.toGroup spec (t.val V)).y)⦄ := by
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
