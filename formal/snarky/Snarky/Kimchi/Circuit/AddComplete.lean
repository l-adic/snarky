import Snarky.DSL.Utils
import Snarky.Tactic
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
* `addFast_complete`: the honest run accepts on-curve operands and reads the finite sum;
  its advice fills the gate's canonical row, `Kimchi.Gate.AddComplete.build`.
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
instance [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] :
    CheckedType F c (AffinePoint F) (AffinePoint (FVar F)) where
  check _ := pure PUnit.unit
  post _ _ := True
  check_sound _ _ _ _ := trivial
  check_complete _ _ _ := Complete.pure

/-- A point's coordinates carry no admissibility condition. -/
@[simp] theorem valid_affinePoint [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
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
def sealPoint [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
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
structure AddAux (a : Type) where
  /-- The value pinning the infinity flag. -/
  infZ : a
  /-- The inverse pinning `sameX`. -/
  x21Inv : a
  /-- The addition slope. -/
  s : a

/-- The auxiliary columns as a triple, in allocation order (not the gate's column order). -/
def AddAux.equiv (a : Type) : AddAux a ≃ a × a × a where
  toFun c := (c.infZ, c.x21Inv, c.s)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instCircuitTypeAddAux : CircuitType F (AddAux F) (AddAux (FVar F)) :=
  CircuitType.ofEquiv (AddAux.equiv F) (AddAux.equiv (FVar F))

instance instCheckedTypeAddAux [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] :
    CheckedType F c (AddAux F) (AddAux (FVar F)) :=
  CheckedType.ofEquiv (AddAux.equiv F) (AddAux.equiv (FVar F))

/-- An auxiliary bundle is in scope when its three columns are. -/
@[simp] theorem scoped_addAux {st : ProverState F} {a : AddAux (FVar F)} :
    CircuitType.Scoped (val := AddAux F) st a ↔
      a.infZ.Scoped st ∧ a.x21Inv.Scoped st ∧ a.s.Scoped st := by
  show (∀ cv ∈ [a.infZ, a.x21Inv, a.s], cv.Scoped st) ↔ _
  simp

/-- An auxiliary bundle reads columnwise. -/
@[simp] theorem reads_addAux [Add F] [Mul F] [Zero F] {V : Valuation F}
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
def addFast [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c]
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
is read at every later table (`OnCurveAs.mono`). -/
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
theorem OnCurveAs.mono [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    {st st' : ProverState F} {p : AffinePoint (FVar F)} {P : W.Point}
    (hnv : st.nv ≤ st'.nv) (hle : st.env.Le st'.env) (h : OnCurveAs W st p P) :
    OnCurveAs W st' p P := by
  obtain ⟨hsc, n, rfl⟩ := h
  rw [scoped_affinePoint] at hsc
  refine ⟨scoped_affinePoint.mpr ⟨hsc.1.mono hnv, hsc.2.mono hnv⟩, ?_, ?_⟩
  · rw [CVar.val_of_le hle hsc.1, CVar.val_of_le hle hsc.2]
    exact n
  · congr 1
    · rw [CVar.val_of_le hle hsc.1]
    · rw [CVar.val_of_le hle hsc.2]

open WeierstrassCurve.Affine in
/-- On a short curve a point with `y = 0` is 2-torsion. The gate's slope divides by `2y₁`;
the laws below take that side condition as `P + P ≠ 0`, so no caller handles a
coordinate. -/
theorem two_torsion_of_y_eq_zero [Field F] [DecidableEq F]
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
@[spec] theorem infColumn_spec {V : Valuation F} [Field F] [DecidableEq F]
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

/-! ## Completeness -/

/-- `OnCurveAs.mono` in `Mono` form, for a context that carries points. -/
@[complete_mono] theorem Mono.onCurveAs [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    {p : AffinePoint (FVar F)} {P : W.Point} :
    Snarky.Mono (F := F) fun st => OnCurveAs W st p P :=
  fun _ _ hnv hle h => OnCurveAs.mono hnv hle h

/-- Sealing a point: the run succeeds, its rows hold at every extension of the final
table, and the sealed point is scoped and reads as the operand. -/
@[complete_law] theorem sealPoint_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (p : AffinePoint (FVar F))
    (P : AffinePoint F) :
    Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := AffinePoint F) st p P)
      (sealPoint (c := c) p)
      (fun r st' => CircuitType.ReadsAs (val := AffinePoint F) st' r P) := by
  have hx : ∀ {st : ProverState F},
      CircuitType.ReadsAs (val := AffinePoint F) st p P →
        CircuitType.ReadsAs (val := F) st p.x P.x := fun h =>
    ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp h.1).1,
      CircuitType.reads_fvar.mpr (reads_affinePoint.mp h.2).1⟩
  have hy : ∀ {st : ProverState F},
      CircuitType.ReadsAs (val := AffinePoint F) st p P →
        CircuitType.ReadsAs (val := F) st p.y P.y := fun h =>
    ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp h.1).2,
      CircuitType.reads_fvar.mpr (reads_affinePoint.mp h.2).2⟩
  simp only [sealPoint]
  complete_walk
  exact Complete.pure_of fun st h =>
    ⟨scoped_affinePoint.mpr ⟨CircuitType.scoped_fvar.mp h.2.1,
        CircuitType.scoped_fvar.mp h.1.2.1⟩,
      reads_affinePoint.mpr ⟨CircuitType.reads_fvar.mp h.2.2,
        CircuitType.reads_fvar.mp h.1.2.2⟩⟩

/-- The infinity column's completeness law: the result reads `false` under `checkFinite`
(nothing emitted) and the honest flag otherwise, so the row obligation downstream treats
both modes as one reading. -/
@[complete_law] theorem infColumn_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (fin : Finiteness)
    (q1 q2 : AffinePoint (FVar F)) (sameX : BoolVar F) (b : Bool) (y1 y2 : F) :
    Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := Bool) st sameX b ∧
        CircuitType.ReadsAs (val := F) st q1.y y1 ∧
        CircuitType.ReadsAs (val := F) st q2.y y2)
      (addFast.infColumn (c := c) fin q1 q2 sameX)
      (fun r st' => CircuitType.ReadsAs (val := Bool) st' r
        (if fin = .checkFinite then false else (b && !decide (y1 = y2)))) := by
  cases fin with
  | checkFinite =>
    simp only [addFast.infColumn]
    exact Complete.pure_of fun st _ =>
      ⟨CircuitType.scoped_boolVar.mpr (by simp),
        CircuitType.reads_boolVar.mpr (by simp [bit])⟩
  | dontCheckFinite =>
    simp only [addFast.infColumn]
    refine Complete.bind
      (Complete.imp (fun st h => ?_) (fun _ _ h => h)
        (Complete.witness (addFast.infAdvice q1 q2 sameX)
          (⟨b && !decide (y1 = y2)⟩ : UnChecked Bool) (by simp)))
      fun r => Complete.pure_of fun st h =>
        ⟨CircuitType.scoped_unchecked.mp h.1,
          by simpa using CircuitType.reads_unchecked.mp h.2⟩
    simp [addFast.infAdvice, readVar_run h.1.1, (CircuitType.reads_iff.mp h.1.2).2,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.1.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.2.1),
      CircuitType.reads_fvar.mp h.2.1.2, CircuitType.reads_fvar.mp h.2.2.2]

open WeierstrassCurve.Affine in
/-- **`addFast`'s completeness.** For on-curve operands with `P + P ≠ 0` (and, under
`checkFinite`, `P + Q ≠ 0`), the run succeeds, its row holds at every extension of the
final table, the result is scoped, and a finite sum is read as `P + Q` (`addFast_spec` at
the honest table). The emitted row reads as `Kimchi.Gate.AddComplete.build`'s canonical
row, which `Kimchi.Gate.AddComplete.complete_build` satisfies. -/
@[complete_law]
theorem addFast_complete [Field F] [DecidableEq F] (fin : Finiteness)
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (htwo : (2 : F) ≠ 0) (p1' p2' : AffinePoint (FVar F)) (P Q : W.Point) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => OnCurveAs W st p1' P ∧ OnCurveAs W st p2' Q ∧
        P + P ≠ 0 ∧ (fin = .checkFinite → P + Q ≠ 0))
      (addFast (c := KimchiConstraint F) fin p1' p2')
      (fun r st' => CircuitType.Scoped (val := AffinePoint F) st' r.p ∧
        (↑r.isInfinity : CVar F).Scoped st' ∧
        (P + Q ≠ 0 → OnCurveAs W st' r.p (P + Q))) := by
  -- a bundle read, projected to a coordinate
  have hax : ∀ {st : ProverState F} {q : AffinePoint (FVar F)} {v : AffinePoint F},
      CircuitType.ReadsAs (val := AffinePoint F) st q v →
        CircuitType.ReadsAs (val := F) st q.x v.x := fun h =>
    ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp h.1).1,
      CircuitType.reads_fvar.mpr (reads_affinePoint.mp h.2).1⟩
  have hay : ∀ {st : ProverState F} {q : AffinePoint (FVar F)} {v : AffinePoint F},
      CircuitType.ReadsAs (val := AffinePoint F) st q v →
        CircuitType.ReadsAs (val := F) st q.y v.y := fun h =>
    ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp h.1).2,
      CircuitType.reads_fvar.mpr (reads_affinePoint.mp h.2).2⟩
  have hub : ∀ {st : ProverState F} {u : UnChecked (BoolVar F)} {bv : Bool},
      CircuitType.ReadsAs (val := UnChecked Bool) st u ⟨bv⟩ →
        CircuitType.ReadsAs (val := Bool) st u.val bv := fun h =>
    ⟨CircuitType.scoped_unchecked.mp h.1, CircuitType.reads_unchecked.mp h.2⟩
  have hbase : Complete (F := F) (c := KimchiConstraint F)
      (fun st => OnCurveAs W st p1' P ∧ OnCurveAs W st p2' Q ∧
        P + P ≠ 0 ∧ (fin = .checkFinite → P + Q ≠ 0))
      (addFast (c := KimchiConstraint F) fin p1' p2')
      (fun r st' => CircuitType.Scoped (val := AffinePoint F) st' r.p ∧
        (↑r.isInfinity : CVar F).Scoped st') := by
    -- the operands' coordinates live only in the state; `instantiate` names them, and
    -- the index carries the curve-level facts the final row owes `complete_build`
    refine Complete.instantiate
      (ι := {v : F × F × F × F // W.Equation v.1 v.2.1 ∧ W.Equation v.2.2.1 v.2.2.2 ∧
        v.2.1 ≠ 0 ∧
        (fin = .checkFinite → ¬(v.1 = v.2.2.1 ∧ v.2.1 = W.negY v.2.2.1 v.2.2.2))})
      (P := fun i st =>
        CircuitType.ReadsAs (val := AffinePoint F) st p1' ⟨i.1.1, i.1.2.1⟩ ∧
        CircuitType.ReadsAs (val := AffinePoint F) st p2' ⟨i.1.2.2.1, i.1.2.2.2⟩)
      (fun st h => ?_) fun i => ?_
    · obtain ⟨⟨hs1, hP⟩, ⟨hs2, n2, rfl⟩, hPP, hfinP⟩ := h
      have hy1ne : p1'.y.val st.env.get ≠ 0 :=
        fun hy => hPP (two_torsion_of_y_eq_zero ha hP hy)
      obtain ⟨n1, rfl⟩ := hP
      refine ⟨⟨(p1'.x.val st.env.get, p1'.y.val st.env.get,
          p2'.x.val st.env.get, p2'.y.val st.env.get), n1.left, n2.left, hy1ne, ?_⟩,
        ⟨hs1, reads_affinePoint.mpr ⟨rfl, rfl⟩⟩, hs2, reads_affinePoint.mpr ⟨rfl, rfl⟩⟩
      rintro hf ⟨hx, hy⟩
      refine hfinP hf ?_
      rw [add_eq_zero_iff_eq_neg, Point.neg_some]
      congr 1
    obtain ⟨⟨x1, y1, x2, y2⟩, hon1, hon2, hy1ne, hfin⟩ := i
    obtain ⟨sv, hsv⟩ : ∃ v, (if x1 = x2 then 3 * x1 * x1 / (2 * y1)
        else (y2 - y1) / (x2 - x1)) = v := ⟨_, rfl⟩
    simp only [addFast]
    complete_walk
    refine Complete.seq (by complete_mono_tac)
      (Complete.imp
        (fun st h => by
          simp [addFast.sameXAdvice,
            AsProver.readCVar_run (CircuitType.scoped_fvar.mp (hax h.1.2).1),
            AsProver.readCVar_run (CircuitType.scoped_fvar.mp (hax h.2).1),
            CircuitType.reads_fvar.mp (hax h.1.2).2,
            CircuitType.reads_fvar.mp (hax h.2).2])
        (fun _ _ h => h)
        (Complete.witness (addFast.sameXAdvice p1 p2)
          (⟨decide (x1 = x2)⟩ : UnChecked Bool) (by simp)))
      fun sameXU => ?_
    complete_walk
    refine Complete.seq (by complete_mono_tac)
      (Complete.imp
        (fun st h => by
          rw [← hsv]
          by_cases hyy : y1 = y2 <;> by_cases hxx : x1 = x2 <;>
            simp [addFast.auxAdvice, readVar_run (hub h.1.2).1,
              (CircuitType.reads_iff.mp (hub h.1.2).2).2,
              AsProver.readCVar_run (CircuitType.scoped_fvar.mp (hax h.1.1.1.2).1),
              AsProver.readCVar_run (CircuitType.scoped_fvar.mp (hay h.1.1.1.2).1),
              AsProver.readCVar_run (CircuitType.scoped_fvar.mp (hax h.1.1.2).1),
              AsProver.readCVar_run (CircuitType.scoped_fvar.mp (hay h.1.1.2).1),
              CircuitType.reads_fvar.mp (hax h.1.1.1.2).2,
              CircuitType.reads_fvar.mp (hay h.1.1.1.2).2,
              CircuitType.reads_fvar.mp (hax h.1.1.2).2,
              CircuitType.reads_fvar.mp (hay h.1.1.2).2, hyy, hxx])
        (fun _ _ h => h)
        (Complete.witness (addFast.auxAdvice p1 p2 sameXU.val)
          (⟨if y1 = y2 then 0 else if x1 = x2 then (y2 - y1)⁻¹ else 0,
            if x1 = x2 then 0 else (x2 - x1)⁻¹, sv⟩ : AddAux F) (by simp)))
      fun aux => ?_
    refine Complete.seq (by complete_mono_tac)
      (Complete.imp
        (fun st h => by
          simp [addFast.sumAdvice,
            AsProver.readCVar_run (scoped_addAux.mp h.2.1).2.2,
            AsProver.readCVar_run (CircuitType.scoped_fvar.mp (hax h.1.1.1.1.2).1),
            AsProver.readCVar_run (CircuitType.scoped_fvar.mp (hax h.1.1.1.2).1),
            AsProver.readCVar_run (CircuitType.scoped_fvar.mp (hay h.1.1.1.1.2).1),
            (reads_addAux.mp h.2.2).2.2,
            CircuitType.reads_fvar.mp (hax h.1.1.1.1.2).2,
            CircuitType.reads_fvar.mp (hax h.1.1.1.2).2,
            CircuitType.reads_fvar.mp (hay h.1.1.1.1.2).2])
        (fun _ _ h => h)
        (Complete.witness (addFast.sumAdvice p1 p2 aux.s)
          (⟨sv * sv - (x1 + x2),
            sv * (x1 - (sv * sv - (x1 + x2))) - y1⟩ : AffinePoint F)
          (by simp)))
      fun p3 => ?_
    refine Complete.bind (Complete.addConstraint ?row) fun _ =>
      Complete.pure_of fun _ h => ⟨h.2.1, CircuitType.scoped_boolVar.mp h.1.1.2.1⟩
    case row =>
      rintro st ⟨⟨⟨⟨⟨⟨-, hq1⟩, hq2⟩, hsxU⟩, hinf⟩, haux⟩, hp3⟩ stf hle
      have hsx := hub hsxU
      -- the emitted row reads as the gate's canonical one
      show Kimchi.Gate.AddComplete.Holds (AddComplete.read stf.env.get _)
      have r1x : p1.x.val stf.env.get = x1 := by
        rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp (hax hq1).1),
          CircuitType.reads_fvar.mp (hax hq1).2]
      have r1y : p1.y.val stf.env.get = y1 := by
        rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp (hay hq1).1),
          CircuitType.reads_fvar.mp (hay hq1).2]
      have r2x : p2.x.val stf.env.get = x2 := by
        rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp (hax hq2).1),
          CircuitType.reads_fvar.mp (hax hq2).2]
      have r2y : p2.y.val stf.env.get = y2 := by
        rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp (hay hq2).1),
          CircuitType.reads_fvar.mp (hay hq2).2]
      have rsx : (↑sameXU.val : CVar F).val stf.env.get = bit (decide (x1 = x2)) := by
        rw [CVar.val_of_le hle (CircuitType.scoped_boolVar.mp hsx.1),
          CircuitType.reads_boolVar.mp hsx.2]
      have rinf : (↑inf : CVar F).val stf.env.get
          = bit (if fin = .checkFinite then false
                 else (decide (x1 = x2) && !decide (y1 = y2))) := by
        rw [CVar.val_of_le hle (CircuitType.scoped_boolVar.mp hinf.1),
          CircuitType.reads_boolVar.mp hinf.2]
      have rz : aux.infZ.val stf.env.get
          = (if y1 = y2 then 0 else if x1 = x2 then (y2 - y1)⁻¹ else 0) := by
        rw [CVar.val_of_le hle (scoped_addAux.mp haux.1).1, (reads_addAux.mp haux.2).1]
      have rv : aux.x21Inv.val stf.env.get = (if x1 = x2 then 0 else (x2 - x1)⁻¹) := by
        rw [CVar.val_of_le hle (scoped_addAux.mp haux.1).2.1,
          (reads_addAux.mp haux.2).2.1]
      have rl : aux.s.val stf.env.get = sv := by
        rw [CVar.val_of_le hle (scoped_addAux.mp haux.1).2.2,
          (reads_addAux.mp haux.2).2.2]
      have r3x : p3.x.val stf.env.get = sv * sv - (x1 + x2) := by
        rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp (hax hp3).1),
          CircuitType.reads_fvar.mp (hax hp3).2]
      have r3y : p3.y.val stf.env.get = sv * (x1 - (sv * sv - (x1 + x2))) - y1 := by
        rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp (hay hp3).1),
          CircuitType.reads_fvar.mp (hay hp3).2]
      have hread : AddComplete.read (F := F) stf.env.get
          { p1 := p1, p2 := p2, p3 := p3, inf := (↑inf : CVar F),
            sameX := (↑sameXU.val : CVar F), s := aux.s, infZ := aux.infZ,
            x21Inv := aux.x21Inv }
          = Kimchi.Gate.AddComplete.build (decide (fin = .checkFinite)) x1 y1 x2 y2 := by
        simp only [AddComplete.read, Kimchi.Gate.AddComplete.build, r1x, r1y, r2x, r2y,
          rsx, rinf, rz, rv, rl, r3x, r3y, ← hsv]
        cases fin <;> simp [bit]
      rw [hread]
      exact Kimchi.Gate.AddComplete.complete_build W ha hon1 hon2 hy1ne htwo
        (fun h => hfin (of_decide_eq_true h))
  refine Complete.imp (fun st h => ⟨h, h.1, h.2.1, h.2.2.1⟩) (fun r st' h => ?_)
    (Complete.post (fun V => addFast_spec (V := V) fin W ha htwo p1' p2')
      (Complete.frame
        (Mono.and Mono.onCurveAs (Mono.and Mono.onCurveAs fun _ _ _ _ h => h)) hbase))
  obtain ⟨⟨⟨hscP, hscI⟩, hp1, hp2, hPP⟩, hspec⟩ := h
  refine ⟨hscP, hscI, fun hPQ => ?_⟩
  rcases hspec.2 P Q hp1.2 hp2.2 hPP with ⟨-, hzero⟩ | ⟨-, hon⟩
  · exact absurd hzero hPQ
  · exact ⟨hscP, hon⟩

attribute [irreducible] sealPoint addFast addFast.infColumn

end Snarky.Kimchi
