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
* `Prover.addFast_spec`: at the prover's reading, the honest run accepts on-curve operands
  and reads the finite sum: the operands' curve points at the entry state, the sum's at the
  exit. Its advice fills the gate's canonical row, `Kimchi.Gate.AddComplete.build`.
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

instance instWPCheckedTypeAffinePoint [Field F] [BasicSystem F c] [ConstraintHolds F c] :
    WPCheckedType F c (AffinePoint F) (AffinePoint (FVar F)) :=
  ⟨fun _ _ _ _ _ => le_rfl⟩

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

open Std.Do in
/-- Sealing a point preserves both coordinates' readings — `sealVar_spec` at each. -/
@[spec] theorem sealPoint_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (q : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄
    sealPoint (c := Builder V c) q
    ⦃⇓ r _ => ⌜r.x.val V = q.x.val V ∧ r.y.val V = q.y.val V⌝⦄ := by
  simp only [sealPoint]
  mvcgen

open WeierstrassCurve.Affine in
/-- A circuit point reads, under `V`, as the curve point `P`: its coordinates are a
nonsingular pair naming `P`. -/
def OnCurveAt [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) (V : Valuation F)
    (p : AffinePoint (FVar F)) (P : W.Point) : Prop :=
  Kimchi.Gate.AddComplete.IsPoint W (p.x.val V) (p.y.val V) P

open WeierstrassCurve.Affine in
/-- `OnCurveAt` at the table's valuation, with the point in scope, so the same curve point
is read at every later table (`monotone_onCurveAs`). -/
def OnCurveAs [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) (st : ProverState F)
    (p : AffinePoint (FVar F)) (P : W.Point) : Prop :=
  CircuitType.Scoped (val := AffinePoint F) st p ∧ OnCurveAt W st.env.get p P

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

/-- A curve read survives the table's growth, with the same curve point. -/
theorem monotone_onCurveAs [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    {p : AffinePoint (FVar F)} {P : W.Point} :
    Monotone fun st : ProverState F => OnCurveAs W st p P := by
  rintro st st' hle ⟨hsc, hon⟩
  refine ⟨hsc.mono (ProverState.nv_le_of_le hle), ?_⟩
  rw [scoped_affinePoint] at hsc
  rwa [OnCurveAt, CVar.val_of_le hle hsc.1, CVar.val_of_le hle hsc.2]

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

open Std.Do in
/-- Under `checkFinite` the infinity column reads `0`, which rules out the infinite branch;
a witnessed flag is pinned only by the gate's row. -/
@[spec] private theorem infColumn_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (fin : Finiteness)
    (p1 p2 : AffinePoint (FVar F)) (sameX : BoolVar F) :
    ⦃⌜True⌝⦄
    addFast.infColumn (c := Builder V c) fin p1 p2 sameX
    ⦃⇓ b _ => ⌜fin = .checkFinite → (↑b : CVar F).val V = 0⌝⦄ := by
  cases fin <;> simp only [addFast.infColumn] <;> mvcgen
  · simp [false_, CVar.val]
  · simp

open Std.Do WeierstrassCurve.Affine in
/-- **`addFast`'s soundness.** Any valuation satisfying the emitted row reads the result
as the group sum, for operands with `P + P ≠ 0`: either the flag is `1` and `P + Q = 0`,
or the flag is `0` and the output point reads as `P + Q`. Under `checkFinite` the flag
reads `0`. `Kimchi.Gate.AddComplete.sound` does the work; the seals preserve the
operands' readings. -/
@[spec] theorem addFast_spec {V : Valuation F} [Field F] [DecidableEq F]
    (fin : Finiteness) (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0) (htwo : (2 : F) ≠ 0)
    (p1' p2' : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄
    addFast (c := Builder V (KimchiConstraint F)) fin p1' p2'
    ⦃⇓ r _ => ⌜(fin = .checkFinite → (↑r.isInfinity : CVar F).val V = 0) ∧
        ∀ P Q : W.Point, OnCurveAt W V p1' P → OnCurveAt W V p2' Q → P + P ≠ 0 →
          ((↑r.isInfinity : CVar F).val V = 1 ∧ P + Q = 0) ∨
            ((↑r.isInfinity : CVar F).val V = 0 ∧ OnCurveAt W V r.p (P + Q))⌝⦄ := by
  simp only [addFast]
  mvcgen
  rename_i _ q1 _ hs1 q2 _ hs2 _ _ _ inf _ hinf aux _ _ p3 _ _ _ _ hgate
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

The honest run at the prover's reading (`Snarky.Prover.WP`): the seal and the infinity column
registered, each advice's witness registered at a named value of the entry readings, and
`addFast`'s law cited by hand at its curve. The named values keep the gate's case structure
out of the transport: a bundle moves to a later state as one fact, and the row equation
unfolds the values at one state. -/

section ProverReading

open Std.Do WeierstrassCurve.Affine

/-- Sealing a point: the result reads the operand's entry readings. -/
private theorem Prover.sealPoint_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c]
    [LawfulBasicSystem F c] (p : AffinePoint (FVar F)) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ p.x.Scoped st₀ ∧ p.y.Scoped st₀⌝⦄
    sealPoint (c := Prover c) p
    ⦃⇓ r s' => ⌜CircuitType.ReadsAs (val := AffinePoint F) s' r ⟨st₀.read p.x, st₀.read p.y⟩ ∧
      st₀ ≤ s'⌝⦄ := by
  unfold sealPoint
  mvcgen
  all_goals grind [Prover.Reg.iff, CircuitType.ReadsAs, scoped_affinePoint, reads_affinePoint,
    ProverState.read_of_le, CVar.Scoped.of_le]

/-- Registered. -/
@[spec] private def Prover.sealPoint_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (p : AffinePoint (FVar F)) :=
  Prover.register (Prover.sealPoint_spec (c := c) p)

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

private theorem addFast.sameXAdvice_run [Field F] [DecidableEq F] {s : ProverState F}
    {q1 q2 : AffinePoint (FVar F)} (h1 : q1.x.Scoped s) (h2 : q2.x.Scoped s) :
    (addFast.sameXAdvice q1 q2).run s.env =
      .ok (addFast.sameXVal (q1.x.val s.env.get) (q2.x.val s.env.get)) := by
  simp [addFast.sameXAdvice, addFast.sameXVal, AsProver.readCVar_run h1, AsProver.readCVar_run h2]

private theorem addFast.infAdvice_run [Field F] [DecidableEq F] {s : ProverState F}
    {q1 q2 : AffinePoint (FVar F)} {sameX : BoolVar F} (hs : (↑sameX : CVar F).Scoped s)
    (h1 : q1.y.Scoped s) (h2 : q2.y.Scoped s) :
    (addFast.infAdvice q1 q2 sameX).run s.env =
      .ok (addFast.infVal (CircuitType.readVal (val := Bool) s.env.get sameX)
        (q1.y.val s.env.get) (q2.y.val s.env.get)) := by
  simp [addFast.infAdvice, addFast.infVal, readVar_run (CircuitType.scoped_boolVar.mpr hs),
    AsProver.readCVar_run h1, AsProver.readCVar_run h2]

private theorem addFast.auxAdvice_run [Field F] [DecidableEq F] {s : ProverState F}
    {q1 q2 : AffinePoint (FVar F)} {sameX : BoolVar F} (hs : (↑sameX : CVar F).Scoped s)
    (h1x : q1.x.Scoped s) (h1y : q1.y.Scoped s) (h2x : q2.x.Scoped s) (h2y : q2.y.Scoped s) :
    (addFast.auxAdvice q1 q2 sameX).run s.env =
      .ok (addFast.auxVal (CircuitType.readVal (val := Bool) s.env.get sameX)
        (q1.x.val s.env.get) (q1.y.val s.env.get) (q2.x.val s.env.get) (q2.y.val s.env.get)) := by
  simp [addFast.auxAdvice, addFast.auxVal, readVar_run (CircuitType.scoped_boolVar.mpr hs),
    AsProver.readCVar_run h1x, AsProver.readCVar_run h1y, AsProver.readCVar_run h2x,
    AsProver.readCVar_run h2y]

private theorem addFast.sumAdvice_run [Field F] [DecidableEq F] {s : ProverState F}
    {q1 q2 : AffinePoint (FVar F)} {sl : FVar F} (hsl : sl.Scoped s) (h1x : q1.x.Scoped s)
    (h2x : q2.x.Scoped s) (h1y : q1.y.Scoped s) :
    (addFast.sumAdvice q1 q2 sl).run s.env =
      .ok (addFast.sumVal (sl.val s.env.get) (q1.x.val s.env.get) (q2.x.val s.env.get)
        (q1.y.val s.env.get)) := by
  simp [addFast.sumAdvice, addFast.sumVal, AsProver.readCVar_run hsl, AsProver.readCVar_run h1x,
    AsProver.readCVar_run h2x, AsProver.readCVar_run h1y]

/-- `addFast.sameXAdvice` returns the same-x flag. -/
@[spec] private def Prover.addFast_sameXAdvice_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (q1 q2 : AffinePoint (FVar F)) :=
  Prover.register (Prover.witness_of_run (c := c) (addFast.sameXAdvice q1 q2)
    (fun st => q1.x.Scoped st ∧ q2.x.Scoped st)
    (fun st => addFast.sameXVal (st.read q1.x) (st.read q2.x))
    (fun _ h => addFast.sameXAdvice_run h.1 h.2) fun _ _ => by simp)

/-- `addFast.infAdvice` returns the infinity flag. -/
@[spec] private def Prover.addFast_infAdvice_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (q1 q2 : AffinePoint (FVar F)) (sameX : BoolVar F) :=
  Prover.register (Prover.witness_of_run (c := c) (addFast.infAdvice q1 q2 sameX)
    (fun st => (↑sameX : CVar F).Scoped st ∧ q1.y.Scoped st ∧ q2.y.Scoped st)
    (fun st => addFast.infVal (CircuitType.readVal (val := Bool) st.env.get sameX) (st.read q1.y)
      (st.read q2.y))
    (fun _ h => addFast.infAdvice_run h.1 h.2.1 h.2.2) fun _ _ => by simp)

/-- `addFast.auxAdvice` returns the auxiliary columns. -/
@[spec] private def Prover.addFast_auxAdvice_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (q1 q2 : AffinePoint (FVar F)) (sameX : BoolVar F) :=
  Prover.register (Prover.witness_of_run (c := c) (addFast.auxAdvice q1 q2 sameX)
    (fun st => (↑sameX : CVar F).Scoped st ∧ q1.x.Scoped st ∧ q1.y.Scoped st ∧
      q2.x.Scoped st ∧ q2.y.Scoped st)
    (fun st => addFast.auxVal (CircuitType.readVal (val := Bool) st.env.get sameX) (st.read q1.x)
      (st.read q1.y) (st.read q2.x) (st.read q2.y))
    (fun _ h => addFast.auxAdvice_run h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    fun _ _ => by simp)

/-- `addFast.sumAdvice` returns the sum. -/
@[spec] private def Prover.addFast_sumAdvice_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (q1 q2 : AffinePoint (FVar F)) (sl : FVar F) :=
  Prover.register (Prover.witness_of_run (c := c) (addFast.sumAdvice q1 q2 sl)
    (fun st => sl.Scoped st ∧ q1.x.Scoped st ∧ q2.x.Scoped st ∧ q1.y.Scoped st)
    (fun st => addFast.sumVal (st.read sl) (st.read q1.x) (st.read q2.x) (st.read q1.y))
    (fun _ h => addFast.sumAdvice_run h.1 h.2.1 h.2.2.1 h.2.2.2) fun _ _ => by simp)

/-- The infinity column: under `checkFinite` the constant `false`, otherwise the witnessed flag;
the reading named by `addFast.infFlag`. -/
private theorem Prover.infColumn_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c]
    [LawfulBasicSystem F c] (fin : Finiteness) (q1 q2 : AffinePoint (FVar F))
    (sameX : BoolVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ (↑sameX : CVar F).Scoped st₀ ∧ q1.y.Scoped st₀ ∧ q2.y.Scoped st₀⌝⦄
    addFast.infColumn (c := Prover c) fin q1 q2 sameX
    ⦃⇓ r s' => ⌜CircuitType.ReadsAs (val := Bool) s' r
      (addFast.infFlag fin (CircuitType.readVal (val := Bool) st₀.env.get sameX) (st₀.read q1.y)
        (st₀.read q2.y)) ∧ st₀ ≤ s'⌝⦄ := by
  cases fin with
  | checkFinite =>
    simp only [addFast.infColumn]
    mvcgen
    rename_i s h
    obtain ⟨rfl, -⟩ := h
    exact ⟨⟨by simp, by simp [addFast.infFlag, bit]⟩, le_rfl⟩
  | dontCheckFinite =>
    simp only [addFast.infColumn]
    mvcgen
    all_goals grind [Prover.Reg.iff, CircuitType.ReadsAs, CircuitType.scoped_unchecked',
      CircuitType.reads_unchecked', addFast.infVal, addFast.infFlag, CVar.Scoped.of_le]

/-- Registered. -/
@[spec] private def Prover.infColumn_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (fin : Finiteness)
    (q1 q2 : AffinePoint (FVar F)) (sameX : BoolVar F) :=
  Prover.register (Prover.infColumn_spec (c := c) fin q1 q2 sameX)

/-- The row of a complete addition, read at its emission state, is the gate's canonical row at
the entry readings: the six bundles are moved to that state once, their cells read off, and the
named values unfolded there. -/
private theorem addFast_row_read [Field F] [DecidableEq F] (fin : Finiteness)
    {st₀ s₅ s₄ s₃ s₂ s₁ s : ProverState F} {p1' p2' q1 q2 p3 : AffinePoint (FVar F)}
    {sxU : UnChecked (BoolVar F)} {inf : BoolVar F} {aux : AddAux (FVar F)}
    (h1 : CircuitType.ReadsAs (val := AffinePoint F) s₅ q1 ⟨st₀.read p1'.x, st₀.read p1'.y⟩)
    (h2 : CircuitType.ReadsAs (val := AffinePoint F) s₄ q2 ⟨s₅.read p2'.x, s₅.read p2'.y⟩)
    (hp2 : CircuitType.Scoped (val := AffinePoint F) st₀ p2') (hle1 : st₀ ≤ s₅) (hle2 : s₅ ≤ s₄)
    (h3 : CircuitType.ReadsAs (val := UnChecked Bool) s₃ sxU
      (addFast.sameXVal (s₄.read q1.x) (s₄.read q2.x))) (hle3 : s₄ ≤ s₃)
    (h4 : CircuitType.ReadsAs (val := Bool) s₂ inf
      (addFast.infFlag fin (CircuitType.readVal (val := Bool) s₃.env.get sxU.val)
        (s₃.read q1.y) (s₃.read q2.y))) (hle4 : s₃ ≤ s₂)
    (h5 : CircuitType.ReadsAs (val := AddAux F) s₁ aux
      (addFast.auxVal (CircuitType.readVal (val := Bool) s₂.env.get sxU.val) (s₂.read q1.x)
        (s₂.read q1.y) (s₂.read q2.x) (s₂.read q2.y))) (hle5 : s₂ ≤ s₁)
    (h6 : CircuitType.ReadsAs (val := AffinePoint F) s p3
      (addFast.sumVal (s₁.read aux.s) (s₁.read q1.x) (s₁.read q2.x) (s₁.read q1.y)))
    (hle6 : s₁ ≤ s) :
    AddComplete.read (F := F) s.env.get
      { p1 := q1, p2 := q2, p3 := p3, inf := (↑inf : CVar F), sameX := (↑sxU.val : CVar F),
        s := aux.s, infZ := aux.infZ, x21Inv := aux.x21Inv }
      = Kimchi.Gate.AddComplete.build (decide (fin = .checkFinite)) (p1'.x.val st₀.env.get)
          (p1'.y.val st₀.env.get) (p2'.x.val st₀.env.get) (p2'.y.val st₀.env.get) := by
  -- the bundles at the emission state, and the bundles each later advice read
  have b1 := h1.of_le (hle2.trans (hle3.trans (hle4.trans (hle5.trans hle6))))
  have b2 := h2.of_le (hle3.trans (hle4.trans (hle5.trans hle6)))
  have b3 := h3.of_le (hle4.trans (hle5.trans hle6))
  have b4 := h4.of_le (hle5.trans hle6)
  have b5 := h5.of_le hle6
  have h1₄ := h1.of_le hle2
  have h1₃ := h1.of_le (hle2.trans hle3)
  have h2₃ := h2.of_le hle3
  have h1₂ := h1.of_le (hle2.trans (hle3.trans hle4))
  have h2₂ := h2.of_le (hle3.trans hle4)
  have h3₂ := h3.of_le hle4
  have h1₁ := h1.of_le (hle2.trans (hle3.trans (hle4.trans hle5)))
  have h2₁ := h2.of_le (hle3.trans (hle4.trans hle5))
  -- cells, from the bundles, and the second seal's reading carried to the entry
  have hp2x : p2'.x.val s₅.env.get = p2'.x.val st₀.env.get :=
    CVar.val_of_le hle1 (scoped_affinePoint.mp hp2).1
  have hp2y : p2'.y.val s₅.env.get = p2'.y.val st₀.env.get :=
    CVar.val_of_le hle1 (scoped_affinePoint.mp hp2).2
  have hsx₃ := (CircuitType.reads_iff.mp (CircuitType.reads_unchecked'.mp h3.2)).2
  have hsx₂ := (CircuitType.reads_iff.mp (CircuitType.reads_unchecked'.mp h3₂.2)).2
  simp only [AddComplete.read, Kimchi.Gate.AddComplete.build, ProverState.read] at *
  simp only [(reads_affinePoint.mp b1.2).1, (reads_affinePoint.mp b1.2).2,
    (reads_affinePoint.mp b2.2).1, (reads_affinePoint.mp b2.2).2,
    CircuitType.reads_boolVar.mp (CircuitType.reads_unchecked'.mp b3.2),
    CircuitType.reads_boolVar.mp b4.2, (reads_addAux.mp b5.2).1, (reads_addAux.mp b5.2).2.1,
    (reads_addAux.mp b5.2).2.2, (reads_affinePoint.mp h6.2).1, (reads_affinePoint.mp h6.2).2,
    (reads_addAux.mp h5.2).2.2, (reads_affinePoint.mp h1₄.2).1, (reads_affinePoint.mp h2.2).1,
    (reads_affinePoint.mp h1₃.2).2, (reads_affinePoint.mp h2₃.2).2,
    (reads_affinePoint.mp h1₂.2).1, (reads_affinePoint.mp h1₂.2).2,
    (reads_affinePoint.mp h2₂.2).1, (reads_affinePoint.mp h2₂.2).2,
    (reads_affinePoint.mp h1₁.2).1, (reads_affinePoint.mp h1₁.2).2,
    (reads_affinePoint.mp h2₁.2).1, hsx₃, hsx₂, hp2x, hp2y, addFast.sameXVal, addFast.infFlag,
    addFast.auxVal, addFast.sumVal]
  cases fin <;> simp [bit]

/-- **`addFast`'s state-relative completeness.** For on-curve operands with `P + P ≠ 0` (and,
under `checkFinite`, `P + Q ≠ 0`), the run succeeds, the result is in scope, and a finite sum
reads as `P + Q`. The curve and its points are not determined by the program, so the law is
cited by hand at its instance rather than registered. -/
theorem Prover.addFast_spec [Field F] [DecidableEq F] (fin : Finiteness)
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (htwo : (2 : F) ≠ 0) (p1' p2' : AffinePoint (FVar F)) (P Q : W.Point)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ OnCurveAs W st₀ p1' P ∧ OnCurveAs W st₀ p2' Q ∧ P + P ≠ 0 ∧
      (fin = .checkFinite → P + Q ≠ 0)⌝⦄
    addFast (c := Prover (KimchiConstraint F)) fin p1' p2'
    ⦃⇓ r s' => ⌜CircuitType.Scoped (val := AffinePoint F) s' r.p ∧
      (↑r.isInfinity : CVar F).Scoped s' ∧ (P + Q ≠ 0 → OnCurveAs W s' r.p (P + Q)) ∧
      st₀ ≤ s'⌝⦄ := by
  unfold addFast
  mvcgen
  all_goals (try grind [Prover.Reg.iff, CircuitType.ReadsAs, CircuitType.scoped_fvar,
    CircuitType.scoped_unchecked', CircuitType.scoped_boolVar, scoped_affinePoint,
    scoped_addAux, CVar.Scoped.of_le, OnCurveAs])
  -- the row: it reads as the gate's canonical one
  · rename_i s₆ h₀ q1 s₅ h1 q2 s₄ h2 sxU sameX s₃ h3 inf s₂ h4 aux s₁ h5 p3 s h6
    simp only [Prover.Reg.iff] at h1 h2 h3 h4 h5 h6
    obtain ⟨rfl, ⟨hsc1, hP⟩, ⟨hsc2, hQ⟩, hPP, hfinP⟩ := h₀
    refine ⟨trivial, ?_, ?_⟩
    -- the row's cells: the sealed points', the flags', the auxiliaries' and the sum's
    on_goal 2 =>
      obtain ⟨hq1, l1⟩ := h1
      obtain ⟨hq2, l2⟩ := h2
      obtain ⟨hsx, l3⟩ := h3
      obtain ⟨hinf, l4⟩ := h4
      obtain ⟨haux, l5⟩ := h5
      obtain ⟨hp3, l6⟩ := h6
      obtain ⟨q1x, q1y⟩ := scoped_affinePoint.mp hq1.1
      obtain ⟨q2x, q2y⟩ := scoped_affinePoint.mp hq2.1
      obtain ⟨p3x, p3y⟩ := scoped_affinePoint.mp hp3.1
      obtain ⟨ai, ax, as⟩ := scoped_addAux.mp haux.1
      have hinf' := CircuitType.scoped_boolVar.mp hinf.1
      have hsx' := CircuitType.scoped_boolVar.mp (CircuitType.scoped_unchecked'.mp hsx.1)
      intro y hy
      change y ∈ (AddComplete.operands _).toList at hy
      simp only [AddComplete.operands, Vector.toList_mk, List.mem_cons, List.mem_nil_iff,
        or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact q1x.of_le (by le_chain)
      · exact q1y.of_le (by le_chain)
      · exact q2x.of_le (by le_chain)
      · exact q2y.of_le (by le_chain)
      · exact p3x
      · exact p3y
      · exact hinf'.of_le (by le_chain)
      · exact hsx'.of_le (by le_chain)
      · exact as.of_le (by le_chain)
      · exact ai.of_le (by le_chain)
      · exact ax.of_le (by le_chain)
    show Kimchi.Gate.AddComplete.Holds (AddComplete.read s.env.get _)
    rw [addFast_row_read fin h1.1 h2.1 hsc2 h1.2 h2.2 h3.1 h3.2 h4.1 h4.2 h5.1 h5.2 h6.1 h6.2]
    have hy1ne : p1'.y.val s₆.env.get ≠ 0 := fun hy => hPP (two_torsion_of_y_eq_zero ha hP hy)
    obtain ⟨n1, rfl⟩ := hP
    obtain ⟨n2, rfl⟩ := hQ
    refine Kimchi.Gate.AddComplete.complete_build W ha n1.1 n2.1 hy1ne htwo ?_
    rintro hf ⟨hx, hy⟩
    refine hfinP (by simpa using hf) ?_
    rw [add_eq_zero_iff_eq_neg, Point.neg_some]
    congr 1
  -- the final post: the sum from the row, by the gate's soundness
  · rename_i s₇ h₀ q1 s₆ h1 q2 s₅ h2 sxU sameX s₄ h3 inf s₃ h4 aux s₂ h5 p3 s₁ h6 u s h7
    simp only [Prover.Reg.iff] at h1 h2 h3 h4 h5 h6
    obtain ⟨rfl, hgate⟩ := h7
    obtain ⟨rfl, ⟨hsc1, hP⟩, ⟨hsc2, hQ⟩, hPP, hfinP⟩ := h₀
    refine ⟨by grind [CircuitType.ReadsAs, CVar.Scoped.of_le],
      by grind [CircuitType.ReadsAs, CircuitType.scoped_boolVar, CVar.Scoped.of_le],
      fun hPQ => ?_, by grind⟩
    have hread := addFast_row_read fin h1.1 h2.1 hsc2 h1.2 h2.2 h3.1 h3.2 h4.1 h4.2 h5.1 h5.2
      h6.1 h6.2
    have hy1ne : p1'.y.val s₇.env.get ≠ 0 := fun hy => hPP (two_torsion_of_y_eq_zero ha hP hy)
    obtain ⟨n1, rfl⟩ := hP
    obtain ⟨n2, rfl⟩ := hQ
    have hgate' : Kimchi.Gate.AddComplete.Holds (AddComplete.read s.env.get _) := hgate
    rw [hread] at hgate'
    rcases Kimchi.Gate.AddComplete.sound W ha _ n1 n2 hgate' hy1ne htwo with
      ⟨-, hzero⟩ | ⟨-, h3, hsum⟩
    · exact absurd hzero hPQ
    · refine ⟨by grind [CircuitType.ReadsAs, CVar.Scoped.of_le], ?_⟩
      show Kimchi.Gate.AddComplete.IsPoint W (p3.x.val s.env.get) (p3.y.val s.env.get) _
      rw [show p3.x.val s.env.get = _ from congrArg Kimchi.Gate.AddComplete.Witness.x3 hread,
        show p3.y.val s.env.get = _ from congrArg Kimchi.Gate.AddComplete.Witness.y3 hread]
      exact ⟨h3, hsum⟩

end ProverReading

attribute [irreducible] sealPoint addFast addFast.infColumn

end Snarky.Kimchi
