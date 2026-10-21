import Snarky.DSL.Utils
import Snarky.Kimchi.Semantics
import Kimchi.Gate.Semantics.AddComplete

/-!
# The complete-addition gadget

Transcribes packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/AddComplete.purs. `addFast`
seals the two operand points, witnesses the gate's auxiliary columns and the sum, and emits
one `addComplete` constraint; `Finiteness` picks whether the infinity flag is the constant
`0` or witnessed.

The point bundle's `CircuitType`/`CheckedType` instances live here, beside their first
consumer: the encoding is `[x, y]`, with no check. The gadget definitions are polymorphic
over the carrier through `KimchiSystem`, so one definition serves the soundness reading at
`KimchiConstraint` and the completeness reading at its prover tag.

## Main results

* `addFast_spec`: any satisfying valuation reads the output as the group sum, through the
  verified gate's `Kimchi.Gate.AddComplete.sound`.
* `Prover.addFast_spec`: at the prover's reading, operands reading on-curve values with a
  finite sum give an output point reading the sum's coordinates and an infinity flag reading
  `false`. Its advice fills the gate's canonical row, `Kimchi.Gate.AddComplete.build`.
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- Point bundles encode coordinatewise, `[x, y]`. -/
instance : CircuitType F (AffinePoint F) (AffinePoint (FVar F)) where
  size := 2
  valueToFields p := #v[p.x, p.y]
  fieldsToValue fs := ⟨fs[0], fs[1]⟩
  varToFields p := #v[p.x, p.y]
  fieldsToVar fs := ⟨fs[0], fs[1]⟩
  value_roundTrip _ := rfl
  var_roundTrip cvs := by
    ext i hi
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl

/-- A point's coordinates carry no check of their own. -/
instance [Field F] [BasicSystem F c] [ConstraintHolds F c] :
    CheckedType F c (AffinePoint F) (AffinePoint (FVar F)) where
  check _ := pure PUnit.unit
  post _ _ := True
  check_sound _ _ _ _ := trivial

open Std.WP in
/-- A point's check emits nothing, so it keeps the point's reading. -/
instance instCheckSpecAffinePoint [Field F] [BasicSystem F c] [ConstraintHolds F c] :
    Prover.CheckSpec F c (AffinePoint F) (AffinePoint (FVar F)) where
  check r v _ := by
    show ⦃Prover.Reads r v⦄ (pure PUnit.unit : CircuitM F (Prover c) PUnit)
      ⦃fun _ ↦ Prover.Reads r v⦄
    vcgen

/-- A point's coordinates carry no admissibility condition: what a witness of a point owes
`CheckedType.Valid`, discharged by `simp`. -/
@[simp] private theorem valid_affinePoint [Field F] [BasicSystem F c] [ConstraintHolds F c]
    {p : AffinePoint F} :
    CheckedType.Valid (F := F) (c := c) (var := AffinePoint (FVar F)) p := fun _ _ _ => trivial

/-- A point bundle is in scope when its coordinates are. -/
@[simp] theorem scoped_affinePoint {st : ProverState F} {p : AffinePoint (FVar F)} :
    CircuitType.Scoped (val := AffinePoint F) st p ↔ p.x.Scoped st ∧ p.y.Scoped st := by
  show (∀ cv ∈ [p.x, p.y], cv.Scoped st) ↔ _
  simp

/-- A point bundle reads coordinatewise. -/
@[simp] theorem reads_affinePoint [Add F] [Mul F] [Zero F] {V : Valuation F}
    {p : AffinePoint (FVar F)} {a : AffinePoint F} :
    CircuitType.Reads V p a ↔ p.x.val V = a.x ∧ p.y.val V = a.y := by
  constructor
  · intro h
    exact ⟨congrArg (fun v : Vector F 2 => v[0]) h, congrArg (fun v : Vector F 2 => v[1]) h⟩
  · rintro ⟨hx, hy⟩
    show (#v[p.x.val V, p.y.val V] : Vector F 2) = #v[a.x, a.y]
    rw [hx, hy]

/-- Seal a point coordinatewise, `y` before `x`: the order is part of the emitted rows. -/
def sealPoint [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (p : AffinePoint (FVar F)) : CircuitM F c (AffinePoint (FVar F)) := do
  let y ← sealVar p.y
  let x ← sealVar p.x
  pure ⟨x, y⟩

/-- The finiteness mode: `checkFinite` pins the infinity flag to the constant `0` with no
witness; `dontCheckFinite` witnesses it. -/
inductive Finiteness where
  /-- The sum is asserted finite: `inf` is the constant zero. -/
  | checkFinite
  /-- The sum may be the point at infinity: `inf` is witnessed. -/
  | dontCheckFinite
  deriving DecidableEq

/-- The gate's three auxiliary scalar columns, witnessed together: one advice computation
from the same four operand readings. -/
private structure AddAux (a : Type) where
  /-- The value pinning the infinity flag. -/
  infZ : a
  /-- The inverse pinning `sameX`. -/
  x21Inv : a
  /-- The addition slope. -/
  s : a

/-- The auxiliary columns as a triple, in allocation order (not the gate's column order). -/
private def AddAux.equiv (a : Type) : AddAux a ≃ a × a × a where
  toFun c := (c.infZ, c.x21Inv, c.s)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance instCircuitTypeAddAux : CircuitType F (AddAux F) (AddAux (FVar F)) :=
  CircuitType.ofEquiv (AddAux.equiv F) (AddAux.equiv (FVar F))

private instance instCheckedTypeAddAux [Field F] [BasicSystem F c] [ConstraintHolds F c] :
    CheckedType F c (AddAux F) (AddAux (FVar F)) :=
  CheckedType.ofEquiv (AddAux.equiv F) (AddAux.equiv (FVar F))

/-- An auxiliary bundle is in scope when its three columns are. -/
@[simp] private theorem scoped_addAux {st : ProverState F} {a : AddAux (FVar F)} :
    CircuitType.Scoped (val := AddAux F) st a ↔
      a.infZ.Scoped st ∧ a.x21Inv.Scoped st ∧ a.s.Scoped st := by
  show (∀ cv ∈ [a.infZ, a.x21Inv, a.s], cv.Scoped st) ↔ _
  simp

/-- An auxiliary bundle reads columnwise. -/
@[simp] private theorem reads_addAux [Add F] [Mul F] [Zero F] {V : Valuation F}
    {a : AddAux (FVar F)} {v : AddAux F} :
    CircuitType.Reads V a v ↔
      a.infZ.val V = v.infZ ∧ a.x21Inv.val V = v.x21Inv ∧ a.s.val V = v.s := by
  constructor
  · intro h
    exact ⟨congrArg (fun w : Vector F 3 => w[0]) h, congrArg (fun w : Vector F 3 => w[1]) h,
      congrArg (fun w : Vector F 3 => w[2]) h⟩
  · rintro ⟨h1, h2, h3⟩
    show (#v[a.infZ.val V, a.x21Inv.val V, a.s.val V] : Vector F 3)
      = #v[v.infZ, v.x21Inv, v.s]
    rw [h1, h2, h3]

/-- `addFast`'s result: the output point and the (mode-dependent) infinity flag. -/
structure AddResult (F : Type) where
  /-- The output sum. -/
  p : AffinePoint (FVar F)
  /-- The infinity flag: constant `false` under `checkFinite`, else witnessed. -/
  isInfinity : BoolVar F

/-- Complete addition under a finiteness mode: seal both points, witness `sameX`, the
mode-dependent `inf`, `infZ`, `x21Inv`, the slope and the output point in that order, and
emit one `addComplete` constraint. -/
def addFast [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [KimchiSystem F c]
    (finiteness : Finiteness) (p1' p2' : AffinePoint (FVar F)) :
    CircuitM F c (AddResult F) := do
  let p1 ← sealPoint p1'
  let p2 ← sealPoint p2'
  let sameXU ← witness (val := UnChecked Bool) (sameXAdvice p1 p2)
  let sameX := sameXU.val
  let inf ← infColumn finiteness p1 p2 sameX
  let aux ← witness (val := AddAux F) (auxAdvice p1 p2 sameX)
  let p3 ← witness (val := AffinePoint F) (sumAdvice p1 p2 aux.s)
  addConstraint (KimchiSystem.addComplete
    { p1 := p1, p2 := p2, p3 := p3, inf := inf.toCVar,
      sameX := sameX.toCVar, s := aux.s, infZ := aux.infZ, x21Inv := aux.x21Inv })
  pure ⟨p3, inf⟩
where
  /-- The infinity column: the constant `false` under `checkFinite`, otherwise witnessed.
  A named circuit, so the gadget's body stays a chain of binds. -/
  infColumn (finiteness : Finiteness) (p1 p2 : AffinePoint (FVar F)) (sameX : BoolVar F) :
      CircuitM F c (BoolVar F) :=
    match finiteness with
    | .checkFinite => pure false_
    | .dontCheckFinite => do
      let r ← witness (val := UnChecked Bool) (infAdvice p1 p2 sameX)
      pure r.val
  /-- Whether the operand x-coordinates coincide. -/
  sameXAdvice (p1 p2 : AffinePoint (FVar F)) : AsProver F (UnChecked Bool) := do
    let x1 ← AsProver.readCVar p1.x
    let x2 ← AsProver.readCVar p2.x
    pure ⟨decide (x1 = x2)⟩
  /-- The infinity flag: same x-coordinates, different y-coordinates. -/
  infAdvice (p1 p2 : AffinePoint (FVar F)) (sameX : BoolVar F) :
      AsProver F (UnChecked Bool) := do
    let sx ← readVar (val := Bool) sameX
    let y1 ← AsProver.readCVar p1.y
    let y2 ← AsProver.readCVar p2.y
    pure ⟨sx && !(decide (y1 = y2))⟩
  /-- The three auxiliary columns from one reading of the operands: the value pinning the
  infinity flag, the inverse pinning `sameX`, and the slope (tangent on equal
  x-coordinates, secant otherwise). -/
  auxAdvice (p1 p2 : AffinePoint (FVar F)) (sameX : BoolVar F) : AsProver F (AddAux F) := do
    let sx ← readVar (val := Bool) sameX
    let x1 ← AsProver.readCVar p1.x
    let y1 ← AsProver.readCVar p1.y
    let x2 ← AsProver.readCVar p2.x
    let y2 ← AsProver.readCVar p2.y
    pure ⟨if y1 = y2 then 0 else if sx then (y2 - y1)⁻¹ else 0,
          if sx then 0 else (x2 - x1)⁻¹,
          if sx then 3 * x1 * x1 / (2 * y1) else (y2 - y1) / (x2 - x1)⟩
  /-- The sum from the slope: `x₃ = s² − (x₁ + x₂)`, `y₃ = s·(x₁ − x₃) − y₁`. -/
  sumAdvice (p1 p2 : AffinePoint (FVar F)) (s : FVar F) : AsProver F (AffinePoint F) := do
    let sv ← AsProver.readCVar s
    let x1 ← AsProver.readCVar p1.x
    let x2 ← AsProver.readCVar p2.x
    let y1 ← AsProver.readCVar p1.y
    let x3 := sv * sv - (x1 + x2)
    pure ⟨x3, sv * (x1 - x3) - y1⟩

/-! ## Soundness -/

open Std.WP in
/-- Sealing a point preserves both coordinates' readings — `sealVar_spec` at each. -/
@[spec] theorem sealPoint_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (q : AffinePoint (FVar F)) :
    ⦃fun _ => True⦄
    sealPoint (c := Builder V c) q
    ⦃fun r _ => r.x.val V = q.x.val V ∧ r.y.val V = q.y.val V⦄ := by
  simp only [sealPoint]
  vcgen
  exact ⟨‹_›, ‹_›⟩

open WeierstrassCurve.Affine in
/-- A circuit point reads, under `V`, as the curve point `P`: its coordinates are a
nonsingular pair naming `P`. -/
def OnCurveAt [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) (V : Valuation F)
    (p : AffinePoint (FVar F)) (P : W.Point) : Prop :=
  Kimchi.Gate.AddComplete.IsPoint W (p.x.val V) (p.y.val V) P

open WeierstrassCurve.Affine in
/-- Cells reading as a nonsingular pair `(x, y)` read as that curve point, so a consumer
never names `Point.some` at the cells' own coordinates. -/
theorem OnCurveAt.of_reads [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    {V : Valuation F} {p : AffinePoint (FVar F)} {x y : F}
    (hx : p.x.val V = x) (hy : p.y.val V = y) (h : W.Nonsingular x y) :
    OnCurveAt W V p (Point.some x y h) := by
  subst hx; subst hy; exact ⟨h, rfl⟩

open WeierstrassCurve.Affine in
/-- Two curve reads whose coordinates agree name the same point: the elimination for
`assertEqual` rows pinning two results together. -/
theorem OnCurveAt.eq [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    {V : Valuation F} {p q : AffinePoint (FVar F)} {P Q : W.Point}
    (h : OnCurveAt W V p P) (h' : OnCurveAt W V q Q)
    (hx : p.x.val V = q.x.val V) (hy : p.y.val V = q.y.val V) : P = Q := by
  obtain ⟨n, rfl⟩ := h
  obtain ⟨n', rfl⟩ := h'
  exact Kimchi.Gate.AddComplete.some_congr W n n' hx hy

open WeierstrassCurve.Affine in
/-- Negating the `y` cell with `CVar.negate_` reads as the negated curve point, since
`negY x y = −y` when `a₁ = a₃ = 0`. -/
theorem OnCurveAt.neg [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    (ha : W.a₁ = 0 ∧ W.a₃ = 0) {V : Valuation F} {p : AffinePoint (FVar F)} {P : W.Point}
    (h : OnCurveAt W V p P) :
    OnCurveAt W V ⟨p.x, CVar.negate_ p.y⟩ (-P) := by
  obtain ⟨hns, rfl⟩ := h
  have hneg : W.negY (p.x.val V) (p.y.val V) = -(p.y.val V) := by
    simp [WeierstrassCurve.Affine.negY, ha.1, ha.2]
  refine ⟨?_, ?_⟩
  · show W.Nonsingular (p.x.val V) ((CVar.negate_ p.y).val V)
    rw [CVar.val_negate_, ← hneg]
    exact (nonsingular_neg ..).mpr hns
  · rw [Point.neg_some]
    simp only [Point.some.injEq]
    exact ⟨trivial, by rw [CVar.val_negate_]; exact hneg⟩

open WeierstrassCurve.Affine in
/-- On a short curve a point with `y = 0` is 2-torsion. The gate's slope divides by `2y₁`;
the laws below take that side condition as `P + P ≠ 0`, so no caller handles a
coordinate. -/
private theorem two_torsion_of_y_eq_zero [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    {V : Valuation F} {p : AffinePoint (FVar F)} {P : W.Point}
    (h : OnCurveAt W V p P) (hy : p.y.val V = 0) : P + P = 0 := by
  obtain ⟨n, rfl⟩ := h
  rw [add_eq_zero_iff_eq_neg, Point.neg_some]
  congr 1
  rw [WeierstrassCurve.Affine.negY, ha.1, ha.2.2.1, hy]
  ring

open Std.WP in
/-- Under `checkFinite` the infinity column reads `0`, which rules out the infinite branch;
a witnessed flag is pinned only by the gate's row. -/
@[spec] private theorem infColumn_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (fin : Finiteness)
    (p1 p2 : AffinePoint (FVar F)) (sameX : BoolVar F) :
    ⦃fun _ => True⦄
    addFast.infColumn (c := Builder V c) fin p1 p2 sameX
    ⦃fun (b : BoolVar F) _ => fin = .checkFinite → (↑b : CVar F).val V = 0⦄ := by
  cases fin <;> simp only [addFast.infColumn] <;> vcgen
  · simp [false_, CVar.val]
  · simp_all

open Std.WP WeierstrassCurve.Affine in
/-- **`addFast`'s soundness.** Any valuation satisfying the emitted row reads the result
as the group sum, for operands with `P + P ≠ 0`: either the flag is `1` and `P + Q = 0`,
or the flag is `0` and the output point reads as `P + Q`. Under `checkFinite` the flag
reads `0`. `Kimchi.Gate.AddComplete.sound` does the work; the seals preserve the
operands' readings. -/
@[spec] theorem addFast_spec {V : Valuation F} [Field F] [DecidableEq F]
    (fin : Finiteness) (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0) (htwo : (2 : F) ≠ 0)
    (p1' p2' : AffinePoint (FVar F)) :
    ⦃fun _ => True⦄
    addFast (c := Builder V (KimchiConstraint F)) fin p1' p2'
    ⦃fun (r : AddResult F) _ => (fin = .checkFinite → (↑r.isInfinity : CVar F).val V = 0) ∧
        ∀ P Q : W.Point, OnCurveAt W V p1' P → OnCurveAt W V p2' Q → P + P ≠ 0 →
          ((↑r.isInfinity : CVar F).val V = 1 ∧ P + Q = 0) ∨
            ((↑r.isInfinity : CVar F).val V = 0 ∧ OnCurveAt W V r.p (P + Q))⦄ := by
  simp only [addFast]
  vcgen
  rename_i hs1 _ hs2 _ _ _ hinf _ _ _ _ hgate
  refine ⟨hinf, ?_⟩
  intro P Q hP hQ hPP
  have hy1ne : p1'.y.val V ≠ 0 := fun hy => hPP (two_torsion_of_y_eq_zero ha hP hy)
  simp only [OnCurveAt, ← hs1.1, ← hs1.2, ← hs2.1, ← hs2.2] at hP hQ
  rw [← hs1.2] at hy1ne
  obtain ⟨h1, rfl⟩ := hP
  obtain ⟨h2, rfl⟩ := hQ
  rcases Kimchi.Gate.AddComplete.sound W ha _ h1 h2 hgate hy1ne htwo with
    ⟨hinf, hsum⟩ | ⟨hinf, h3, hsum⟩
  · exact Or.inl ⟨hinf, hsum⟩
  · exact Or.inr ⟨hinf, h3, hsum⟩

/-! ## Completeness

The honest run at the prover's reading (`Snarky.Prover.VCGen`): the operands' readings in, the
result's reading out, the values as parameters. Each advice's value is a named function of the
operand values, and the emitted row reads as the gate's canonical row,
`Kimchi.Gate.AddComplete.build`, at them. -/

section ProverReading

open Snarky.Prover Std.WP WeierstrassCurve.Affine

/-- A point bundle reads a value when its coordinates are in scope and read the value's. -/
theorem Prover.reads_affinePoint_apply [Field F] (p : AffinePoint (FVar F))
    (pv : AffinePoint F) (s : ProverState F) :
    Reads p pv s ↔ p.x.Scoped s ∧ p.y.Scoped s ∧ p.x.val s.env.get = pv.x ∧
      p.y.val s.env.get = pv.y := by
  change CircuitType.ReadsAs s p pv ↔ _
  simp only [CircuitType.ReadsAs, scoped_affinePoint, reads_affinePoint, and_assoc]

/-- An auxiliary bundle reads a value when its columns are in scope and read the value's. -/
private theorem Prover.reads_addAux_apply [Field F] (a : AddAux (FVar F)) (v : AddAux F)
    (s : ProverState F) :
    Reads a v s ↔ a.infZ.Scoped s ∧ a.x21Inv.Scoped s ∧ a.s.Scoped s ∧
      a.infZ.val s.env.get = v.infZ ∧ a.x21Inv.val s.env.get = v.x21Inv ∧
        a.s.val s.env.get = v.s := by
  change CircuitType.ReadsAs s a v ↔ _
  simp only [CircuitType.ReadsAs, scoped_addAux, reads_addAux, and_assoc]

/-- An unchecked bundle reads an unchecked value when its payload reads the value's payload. -/
private theorem Prover.reads_unchecked_apply [Field F] {val var : Type} [CircuitType F val var]
    (u : UnChecked var) (v : UnChecked val) (s : ProverState F) :
    Reads u v s ↔ Reads u.val v.val s := Iff.rfl

/-- A bit bundle's decoded value, as a test of its cell's reading. -/
private theorem Prover.readVal_boolVar [Field F] [DecidableEq F] (V : Valuation F)
    (b : BoolVar F) :
    CircuitType.readVal (val := Bool) V b = decide ((↑b : CVar F).val V ≠ 0) := rfl

/-- Sealing a point: the result reads the operand's value. -/
theorem Prover.sealPoint_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (p : AffinePoint (FVar F))
    (pv : AffinePoint F) :
    ⦃Reads p pv⦄ sealPoint (c := Prover c) p ⦃fun r ↦ Reads r pv⦄ := by
  have hy := Prover.sealVar_spec (c := c) p.y pv.y
  have hx := Prover.sealVar_spec (c := c) p.x pv.x
  unfold sealPoint
  vcgen [hy, hx]
  all_goals prover_assert with
    (intros; simp_all [Prover.reads_affinePoint_apply, Reads.fvar_apply])

/-- The same-x flag from the operands' x-coordinates. -/
private def addFast.sameXVal [DecidableEq F] (x1 x2 : F) : UnChecked Bool := ⟨decide (x1 = x2)⟩

/-- The infinity flag from the same-x flag and the y-coordinates. -/
private def addFast.infVal [DecidableEq F] (sx : Bool) (y1 y2 : F) : UnChecked Bool :=
  ⟨sx && !decide (y1 = y2)⟩

/-- The infinity column's reading under a mode. -/
private def addFast.infFlag [DecidableEq F] (fin : Finiteness) (sx : Bool) (y1 y2 : F) : Bool :=
  if fin = .checkFinite then false else sx && !decide (y1 = y2)

/-- The three auxiliary columns from the same-x flag and the operands. -/
private def addFast.auxVal [Field F] [DecidableEq F] (sx : Bool) (x1 y1 x2 y2 : F) : AddAux F :=
  ⟨if y1 = y2 then 0 else if sx then (y2 - y1)⁻¹ else 0,
    if sx then 0 else (x2 - x1)⁻¹,
    if sx then 3 * x1 * x1 / (2 * y1) else (y2 - y1) / (x2 - x1)⟩

/-- The sum from the slope. -/
private def addFast.sumVal [Field F] (sv x1 x2 y1 : F) : AffinePoint F :=
  ⟨sv * sv - (x1 + x2), sv * (x1 - (sv * sv - (x1 + x2))) - y1⟩

/-- `addFast.sameXAdvice` returns the same-x flag. -/
private theorem addFast.sameXAdvice_run [Field F] [DecidableEq F] {s : ProverState F}
    {q1 q2 : AffinePoint (FVar F)} (h1 : q1.x.Scoped s) (h2 : q2.x.Scoped s) :
    (addFast.sameXAdvice q1 q2).run s.env =
      .ok (addFast.sameXVal (q1.x.val s.env.get) (q2.x.val s.env.get)) := by
  simp [addFast.sameXAdvice, addFast.sameXVal, AsProver.readCVar_run h1, AsProver.readCVar_run h2]

/-- `addFast.infAdvice` returns the infinity flag. -/
private theorem addFast.infAdvice_run [Field F] [DecidableEq F] {s : ProverState F}
    {q1 q2 : AffinePoint (FVar F)} {sameX : BoolVar F} (hs : (↑sameX : CVar F).Scoped s)
    (h1 : q1.y.Scoped s) (h2 : q2.y.Scoped s) :
    (addFast.infAdvice q1 q2 sameX).run s.env =
      .ok (addFast.infVal (CircuitType.readVal (val := Bool) s.env.get sameX)
        (q1.y.val s.env.get) (q2.y.val s.env.get)) := by
  simp [addFast.infAdvice, addFast.infVal, readVar_run (CircuitType.scoped_boolVar.mpr hs),
    AsProver.readCVar_run h1, AsProver.readCVar_run h2]

/-- `addFast.auxAdvice` returns the auxiliary columns. -/
private theorem addFast.auxAdvice_run [Field F] [DecidableEq F] {s : ProverState F}
    {q1 q2 : AffinePoint (FVar F)} {sameX : BoolVar F} (hs : (↑sameX : CVar F).Scoped s)
    (h1x : q1.x.Scoped s) (h1y : q1.y.Scoped s) (h2x : q2.x.Scoped s) (h2y : q2.y.Scoped s) :
    (addFast.auxAdvice q1 q2 sameX).run s.env =
      .ok (addFast.auxVal (CircuitType.readVal (val := Bool) s.env.get sameX)
        (q1.x.val s.env.get) (q1.y.val s.env.get) (q2.x.val s.env.get) (q2.y.val s.env.get)) := by
  simp [addFast.auxAdvice, addFast.auxVal, readVar_run (CircuitType.scoped_boolVar.mpr hs),
    AsProver.readCVar_run h1x, AsProver.readCVar_run h1y, AsProver.readCVar_run h2x,
    AsProver.readCVar_run h2y]

/-- `addFast.sumAdvice` returns the sum from the slope. -/
private theorem addFast.sumAdvice_run [Field F] [DecidableEq F] {s : ProverState F}
    {q1 q2 : AffinePoint (FVar F)} {sl : FVar F} (hsl : sl.Scoped s) (h1x : q1.x.Scoped s)
    (h2x : q2.x.Scoped s) (h1y : q1.y.Scoped s) :
    (addFast.sumAdvice q1 q2 sl).run s.env =
      .ok (addFast.sumVal (sl.val s.env.get) (q1.x.val s.env.get) (q2.x.val s.env.get)
        (q1.y.val s.env.get)) := by
  simp [addFast.sumAdvice, addFast.sumVal, AsProver.readCVar_run hsl, AsProver.readCVar_run h1x,
    AsProver.readCVar_run h2x, AsProver.readCVar_run h1y]

/-- The infinity column reads `addFast.infFlag`: under `checkFinite` the constant `false`,
otherwise the witnessed flag. -/
private theorem Prover.infColumn_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (fin : Finiteness)
    (q1 q2 : AffinePoint (FVar F)) (sameX : BoolVar F) (sx : Bool) (y1 y2 : F) :
    ⦃Reads sameX sx ⊓ Reads q1.y y1 ⊓ Reads q2.y y2⦄
    addFast.infColumn (c := Prover c) fin q1 q2 sameX
    ⦃fun r ↦ Reads r (addFast.infFlag fin sx y1 y2)⦄ := by
  cases fin with
  | checkFinite =>
    simp only [addFast.infColumn]
    vcgen
    all_goals prover_assert with
      (intros; simp [Reads.boolVar_apply, addFast.infFlag, false_, bit])
  | dontCheckFinite =>
    have hw := Spec.witness (c := c) (addFast.infAdvice q1 q2 sameX) (addFast.infVal sx y1 y2)
      valid_unchecked
    simp only [addFast.infColumn]
    vcgen [hw]
    all_goals prover_assert with
      (intros; simp_all [Reads.boolVar_apply, Reads.fvar_apply, Prover.reads_unchecked_apply,
        Prover.readVal_boolVar, addFast.infAdvice_run, addFast.infVal, addFast.infFlag, bit])

/-- At a state where the sealed operands read on-curve values `pv`, `qv` naming `P`, `Q`, and
the witnessed bundles read the advice values, the emitted row reads as
`Kimchi.Gate.AddComplete.build` at the operand values, which
`Kimchi.Gate.AddComplete.complete_build` satisfies. -/
private theorem Prover.addFast_row_checked [Field F] [DecidableEq F] (fin : Finiteness)
    {W : WeierstrassCurve.Affine F} (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (htwo : (2 : F) ≠ 0) {pv qv : AffinePoint F} {P Q : W.Point}
    (hP : Kimchi.Gate.AddComplete.IsPoint W pv.x pv.y P)
    (hQ : Kimchi.Gate.AddComplete.IsPoint W qv.x qv.y Q) (hy1 : pv.y ≠ 0)
    (hfin : fin = .checkFinite → P + Q ≠ 0) {s : ProverState F}
    {q1 q2 p3 : AffinePoint (FVar F)} {sxU : UnChecked (BoolVar F)} {inf : BoolVar F}
    {aux : AddAux (FVar F)} (h1 : Reads q1 pv s) (h2 : Reads q2 qv s)
    (h3 : Reads sxU (addFast.sameXVal pv.x qv.x) s)
    (h4 : Reads inf (addFast.infFlag fin (decide (pv.x = qv.x)) pv.y qv.y) s)
    (h5 : Reads aux (addFast.auxVal (decide (pv.x = qv.x)) pv.x pv.y qv.x qv.y) s)
    (h6 : Reads p3 (addFast.sumVal (addFast.auxVal (decide (pv.x = qv.x)) pv.x pv.y qv.x qv.y).s
      pv.x qv.x pv.y) s) :
    Checked (F := F) (KimchiConstraint.addComplete
      { p1 := q1, p2 := q2, p3 := p3, inf := (↑inf : CVar F), sameX := (↑sxU.val : CVar F),
        s := aux.s, infZ := aux.infZ, x21Inv := aux.x21Inv }) s := by
  rw [Prover.reads_affinePoint_apply] at h1 h2 h6
  rw [Prover.reads_unchecked_apply, Reads.boolVar_apply] at h3
  rw [Reads.boolVar_apply] at h4
  rw [Prover.reads_addAux_apply] at h5
  obtain ⟨q1x, q1y, e1x, e1y⟩ := h1
  obtain ⟨q2x, q2y, e2x, e2y⟩ := h2
  obtain ⟨p3x, p3y, e3x, e3y⟩ := h6
  obtain ⟨sxs, esx⟩ := h3
  obtain ⟨infs, einf⟩ := h4
  obtain ⟨ai, ax, as, eai, eax, eas⟩ := h5
  rw [Checked.apply]
  refine ⟨?_, ?_⟩
  · show Kimchi.Gate.AddComplete.Holds (AddComplete.read s.env.get _)
    have hread : AddComplete.read s.env.get
        { p1 := q1, p2 := q2, p3 := p3, inf := (↑inf : CVar F), sameX := (↑sxU.val : CVar F),
          s := aux.s, infZ := aux.infZ, x21Inv := aux.x21Inv }
        = Kimchi.Gate.AddComplete.build (decide (fin = .checkFinite)) pv.x pv.y qv.x qv.y := by
      simp only [AddComplete.read, Kimchi.Gate.AddComplete.build, e1x, e1y, e2x, e2y, e3x, e3y,
        esx, einf, eai, eax, eas, addFast.sameXVal, addFast.infFlag, addFast.auxVal,
        addFast.sumVal]
      cases fin <;> simp [bit]
    rw [hread]
    obtain ⟨n1, rfl⟩ := hP
    obtain ⟨n2, rfl⟩ := hQ
    refine Kimchi.Gate.AddComplete.complete_build W ha n1.1 n2.1 hy1 htwo ?_
    rintro hf ⟨hx, hy⟩
    refine hfin (by simpa using hf) ?_
    rw [add_eq_zero_iff_eq_neg, Point.neg_some]
    congr 1
  · intro y hy
    change y ∈ (AddComplete.operands _).toList at hy
    simp only [AddComplete.operands, Vector.toList_mk, List.mem_cons, List.mem_nil_iff,
      or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      assumption

/-- For on-curve values `pv`, `qv` naming `P`, `Q` with `pv.y ≠ 0`, and `rv` naming the finite
sum `P + Q`, the sum advice's value is `rv` and the infinity column reads `false`: the gate's
soundness at `Kimchi.Gate.AddComplete.build`'s row. -/
private theorem addFast_sum_values [Field F] [DecidableEq F] (fin : Finiteness)
    {W : WeierstrassCurve.Affine F} (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (htwo : (2 : F) ≠ 0) {pv qv rv : AffinePoint F} {P Q : W.Point}
    (hP : Kimchi.Gate.AddComplete.IsPoint W pv.x pv.y P)
    (hQ : Kimchi.Gate.AddComplete.IsPoint W qv.x qv.y Q) (hy1 : pv.y ≠ 0)
    (hPQ : Kimchi.Gate.AddComplete.IsPoint W rv.x rv.y (P + Q)) :
    addFast.sumVal (addFast.auxVal (decide (pv.x = qv.x)) pv.x pv.y qv.x qv.y).s pv.x qv.x pv.y
      = rv ∧ addFast.infFlag fin (decide (pv.x = qv.x)) pv.y qv.y = false := by
  have hPQ0 : P + Q ≠ 0 := by
    obtain ⟨h, heq⟩ := hPQ
    rw [heq]
    exact Point.some_ne_zero h
  obtain ⟨n1, rfl⟩ := hP
  obtain ⟨n2, rfl⟩ := hQ
  have hw : Kimchi.Gate.AddComplete.Holds
      (Kimchi.Gate.AddComplete.build (decide (fin = .checkFinite)) pv.x pv.y qv.x qv.y) := by
    refine Kimchi.Gate.AddComplete.complete_build W ha n1.1 n2.1 hy1 htwo ?_
    rintro - ⟨hx, hy⟩
    refine hPQ0 ?_
    rw [add_eq_zero_iff_eq_neg, Point.neg_some]
    congr 1
  rcases Kimchi.Gate.AddComplete.sound W ha _ n1 n2 hw hy1 htwo with
    ⟨-, hzero⟩ | ⟨hinf, h3, hsum⟩
  · exact absurd hzero hPQ0
  · obtain ⟨hx, hy⟩ := Kimchi.Gate.AddComplete.IsPoint.coords_eq ⟨h3, hsum⟩ hPQ
    refine ⟨?_, ?_⟩
    · obtain ⟨rx, ry⟩ := rv
      simp only [Kimchi.Gate.AddComplete.build] at hx hy
      simp only [addFast.sumVal, addFast.auxVal, decide_eq_true_eq, ← hx, ← hy]
    · cases fin <;> simp_all [Kimchi.Gate.AddComplete.build, addFast.infFlag]

/-- **`addFast`'s completeness.** For operands reading on-curve values `pv`, `qv` that name
`P`, `Q` with `P + P ≠ 0`, and `rv` naming the finite sum `P + Q`, the output point reads `rv`
and the infinity flag reads `false`. -/
theorem Prover.addFast_spec [Field F] [DecidableEq F] (fin : Finiteness)
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (htwo : (2 : F) ≠ 0) (p1' p2' : AffinePoint (FVar F)) (pv qv rv : AffinePoint F)
    (P Q : W.Point) (hP : Kimchi.Gate.AddComplete.IsPoint W pv.x pv.y P)
    (hQ : Kimchi.Gate.AddComplete.IsPoint W qv.x qv.y Q) (hPP : P + P ≠ 0)
    (hPQ : Kimchi.Gate.AddComplete.IsPoint W rv.x rv.y (P + Q)) :
    ⦃Reads p1' pv ⊓ Reads p2' qv⦄
    addFast (c := Prover (KimchiConstraint F)) fin p1' p2'
    ⦃fun r ↦ Reads r.p rv ⊓ Reads r.isInfinity false⦄ := by
  -- `two_torsion_of_y_eq_zero` at constant cells reading `pv`
  have hy1 : pv.y ≠ 0 := fun hy ↦
    hPP (two_torsion_of_y_eq_zero ha (V := fun _ ↦ 0) (p := ⟨.const pv.x, .const pv.y⟩) hP hy)
  have hPQ0 : P + Q ≠ 0 := by
    obtain ⟨h, heq⟩ := hPQ
    rw [heq]
    exact Point.some_ne_zero h
  obtain ⟨hsumv, hflag⟩ := addFast_sum_values fin ha htwo hP hQ hy1 hPQ
  have h1 := Prover.sealPoint_spec (c := KimchiConstraint F) p1' pv
  have h2 := Prover.sealPoint_spec (c := KimchiConstraint F) p2' qv
  have hsx := fun q1 q2 : AffinePoint (FVar F) ↦ Spec.witness (c := KimchiConstraint F)
    (addFast.sameXAdvice q1 q2) (addFast.sameXVal pv.x qv.x) valid_unchecked
  have hinf := fun (q1 q2 : AffinePoint (FVar F)) (b : BoolVar F) ↦
    Prover.infColumn_spec (c := KimchiConstraint F) fin q1 q2 b (decide (pv.x = qv.x)) pv.y qv.y
  have haux := fun (q1 q2 : AffinePoint (FVar F)) (b : BoolVar F) ↦
    Spec.witness (c := KimchiConstraint F) (addFast.auxAdvice q1 q2 b)
      (addFast.auxVal (decide (pv.x = qv.x)) pv.x pv.y qv.x qv.y) (by simp)
  have hsum := fun (q1 q2 : AffinePoint (FVar F)) (sl : FVar F) ↦
    Spec.witness (c := KimchiConstraint F) (addFast.sumAdvice q1 q2 sl)
      (addFast.sumVal (addFast.auxVal (decide (pv.x = qv.x)) pv.x pv.y qv.x qv.y).s pv.x qv.x
        pv.y) valid_affinePoint
  unfold addFast
  vcgen [h1, h2, hsx, hinf, haux, hsum]
  -- the call contracts are spent; `simp_all` would rewrite with them
  all_goals clear hPQ hPP
  all_goals prover_assert with
    (intros; first
      | (simp_all +zetaDelta [Prover.reads_affinePoint_apply, Prover.reads_addAux_apply,
          Prover.reads_unchecked_apply, Reads.fvar_apply, Reads.boolVar_apply,
          Prover.readVal_boolVar, addFast.sameXAdvice_run, addFast.auxAdvice_run,
          addFast.sumAdvice_run, addFast.sameXVal, bit]; done)
      | exact Prover.addFast_row_checked fin ha htwo hP hQ hy1 (fun _ ↦ hPQ0) ‹_› ‹_› ‹_› ‹_›
          ‹_› ‹_›)

end ProverReading

attribute [irreducible] sealPoint addFast addFast.infColumn

end Snarky.Kimchi
