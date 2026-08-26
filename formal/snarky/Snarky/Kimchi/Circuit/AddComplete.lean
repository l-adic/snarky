import Snarky.DSL.Utils
import Snarky.Kimchi.Semantics
import Kimchi.Gate.Semantics.AddComplete

/-!
# The complete-addition gadget

Port of `Snarky.Circuit.Kimchi.AddComplete`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/AddComplete.purs): `addFast` seals
the two operand points, witnesses the gate's seven auxiliary columns in allocation
order (`sameX`, the mode-dependent `inf`, `infZ`, `x21Inv`, `s`, `x3`, `y3` — fixture
bytes), and emits one `KimchiConstraint.addComplete`. The finite mode is
`addFast .checkFinite`; OCaml spells it as that function's default argument.

Name map: `sealPoint`, `Finiteness` (constructors lowerCamel) and `addFast` keep
their names; the result record is `AddResult`; the witness
computations are named (`AddFast.sameXWit`, …) in the manner of the base `Field`
gadgets.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- `AffinePoint`'s `CircuitType`/`CheckedType` instances live here, beside their first
  Lean consumer — the PS home (`Snarky.Data.EllipticCurve`, package snarky-curves) is
  outside this port. The encoding is the PS generic one, `[x, y]`, checks free.
- Labels are not threaded (the base embedding's `labelOp` is inert; PS wraps
  `add_fast`/`seal_point`).
- The gadget definitions are polymorphic over the carrier through `KimchiSystem`
  (`Snarky/Kimchi/Semantics.lean`) so one definition serves the soundness reading at
  `KimchiConstraint` and the completeness reading at its prover tag (PS writes the
  gadget at the concrete sum).

The law pair reads the one emitted constraint through the semantic layer:
`AddFast.addFast_spec` (any satisfying valuation reads the output as the EC group
sum, via the verified gate's `sound`) and `AddFast.addFast_complete_spec` (the
honest `KimchiProverC` run accepts on-curve operands — the witness computations fill
the row the gate's completeness algebra certifies). `addFast_checkFinite_spec` is
the pinned-mode soundness form: the flag is the constant `0`, so the sum reads as
the finite branch with no disjunction.
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- Point bundles encode coordinatewise, `[x, y]` (the PS generic instance in
`Snarky.Data.EllipticCurve`; see the module docstring). -/
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

/-- A point's coordinates carry no check of their own (PS `genericCheck`). -/
instance [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] :
    CheckedType F c (AffinePoint F) (AffinePoint (FVar F)) where
  check _ := pure PUnit.unit
  post _ _ := True
  check_sound _ _ _ _ := trivial
  check_runs st _ := ⟨st, rfl⟩
  check_sat _ _ _ _ _ _ _ := Sat.pure

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

/-- Seal a point coordinatewise, `y` before `x` — OCaml's `seal` maps over the tuple
right to left (PS `sealPoint` preserves the order; emission order is fixture bytes). -/
def sealPoint [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
    (p : AffinePoint (FVar F)) : CircuitM F c (AffinePoint (FVar F)) := do
  let y ← sealVar p.y
  let x ← sealVar p.x
  pure ⟨x, y⟩

/-- The finiteness mode (OCaml `add_fast ?check_finite`): `checkFinite` pins the
infinity flag to the constant `0` with no witness; `dontCheckFinite` witnesses it. -/
inductive Finiteness where
  /-- The sum is asserted finite: `inf` is the constant zero. -/
  | checkFinite
  /-- The sum may be the point at infinity: `inf` is witnessed. -/
  | dontCheckFinite
  deriving DecidableEq

/-- The gate's three auxiliary scalar columns. Witnessed together because they are one
row's worth of advice, computed from the same four operand readings. -/
structure AddAux (a : Type) where
  /-- The value pinning the infinity flag. -/
  infZ : a
  /-- The inverse pinning `sameX`. -/
  x21Inv : a
  /-- The addition slope. -/
  s : a

/-- The auxiliary columns, as a triple — the encoding lays them out in gate order. -/
def AddAux.equiv (a : Type) : AddAux a ≃ a × a × a where
  toFun c := (c.infZ, c.x21Inv, c.s)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instCircuitTypeAddAux : CircuitType F (AddAux F) (AddAux (FVar F)) :=
  CircuitType.ofShape AddAux.equiv

instance instCheckedTypeAddAux [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] :
    CheckedType F c (AddAux F) (AddAux (FVar F)) :=
  CheckedType.ofShape AddAux.equiv

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

/-- Complete addition with explicit finiteness control (OCaml
`add_fast ~check_finite`): seal both points, witness the gate's auxiliary columns in
allocation order — `sameX`, the mode-dependent `inf`, `infZ`, `x21Inv`, the slope,
then the output point — and emit one `addComplete` constraint. -/
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
  /-- The infinity column: the constant `false` where the sum is asserted finite,
  otherwise witnessed. Named rather than matched inline, so the mode choice is one
  circuit and the gadget's body stays a chain of binds. -/
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
  /-- The three auxiliary columns, from one reading of the operands: the value pinning
  the infinity flag (`0` on equal y-coordinates, else the inverse of `y₂ − y₁` where the
  x-coordinates coincide), the inverse pinning `sameX`, and the slope — tangent where the
  x-coordinates coincide, secant otherwise. -/
  auxAdvice (p1 p2 : AffinePoint (FVar F)) (sameX : BoolVar F) : AsProver F (AddAux F) := do
    let sx ← readVar (val := Bool) sameX
    let x1 ← AsProver.readCVar p1.x
    let y1 ← AsProver.readCVar p1.y
    let x2 ← AsProver.readCVar p2.x
    let y2 ← AsProver.readCVar p2.y
    pure ⟨if y1 = y2 then 0 else if sx then (y2 - y1)⁻¹ else 0,
          if sx then 0 else (x2 - x1)⁻¹,
          if sx then 3 * x1 * x1 / (2 * y1) else (y2 - y1) / (x2 - x1)⟩
  /-- The sum: `x₃ = s² − (x₁ + x₂)` and `y₃ = s·(x₁ − x₃) − y₁`, witnessed as the
  one point the gate's last two columns hold. -/
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
/-- A circuit point reads as a curve point: its coordinates read as a nonsingular pair,
and the point they name is this one. Value-level, for the specs. -/
def OnCurveAt [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) (V : Valuation F)
    (p : AffinePoint (FVar F)) (P : W.Point) : Prop :=
  Kimchi.Gate.AddComplete.IsPoint W (p.x.val V) (p.y.val V) P

open WeierstrassCurve.Affine in
/-- …and in scope, so the same curve point is read at every later table. Carrying the
pair is what keeps a multi-stage proof from rebuilding the point at each stage. -/
def OnCurve [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) (st : ProverState F)
    (p : AffinePoint (FVar F)) (P : W.Point) : Prop :=
  CircuitType.Scoped (val := AffinePoint F) st p ∧ OnCurveAt W st.env.get p P

open WeierstrassCurve.Affine in
/-- Negating the `y` coordinate reads as the negated curve point: under the short shape
`negY x y = −y`, which is what the pure `CVar.negate_` computes. -/
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

/-- A curve read survives the table's growth — with the same curve point. -/
theorem OnCurve.mono [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    {st st' : ProverState F} {p : AffinePoint (FVar F)} {P : W.Point}
    (hnv : st.nv ≤ st'.nv) (hle : st.env.Le st'.env) (h : OnCurve W st p P) :
    OnCurve W st' p P := by
  obtain ⟨hsc, n, rfl⟩ := h
  rw [scoped_affinePoint] at hsc
  refine ⟨scoped_affinePoint.mpr ⟨hsc.1.mono hnv, hsc.2.mono hnv⟩, ?_, ?_⟩
  · rw [CVar.val_of_le hle hsc.1, CVar.val_of_le hle hsc.2]
    exact n
  · congr 1
    · rw [CVar.val_of_le hle hsc.1]
    · rw [CVar.val_of_le hle hsc.2]

open WeierstrassCurve.Affine in
/-- On a short curve an operand whose `y` vanishes is its own negation, hence 2-torsion.
The gate's slope divides by `2y₁`; this is that side condition's point-currency form,
and the two laws below take it that way so no caller of the addition handles a
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
/-- The infinity column grants nothing where the flag is witnessed — what it reads is
pinned by the gate's row, not by how it was produced — but under `checkFinite` it is the
constant `false`, which is what rules the infinite branch out. -/
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
/-- **`addFast`'s soundness.** Any valuation satisfying the emitted row reads the
result as the group sum: either the flag is set and the sum is the point at infinity,
or the flag is clear and the output point is the sum. The gate's own `sound` does the
work; the gadget's part is that the payload's reading is the operands' — the seals
preserve them — and the witnessed columns are whatever the row constrains them to be. -/
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

/-- Sealing a point: the run succeeds, its rows hold at every extension of the final
table, and the sealed point is scoped and reads as the operand. -/
theorem sealPoint_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (p : AffinePoint (FVar F)) (xv yv : F) :
    Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := F) st p.x xv ∧
        CircuitType.ReadsAs (val := F) st p.y yv)
      (sealPoint (c := c) p)
      (fun r st' => CircuitType.ReadsAs (val := F) st' r.x xv ∧
        CircuitType.ReadsAs (val := F) st' r.y yv) := by
  rintro st ⟨hx, hy⟩
  obtain ⟨ry, st₁, hrunY, hsatY, hry⟩ := sealVar_complete (c := c) p.y yv st hy
  obtain ⟨rx, st₂, hrunX, hsatX, hrx⟩ :=
    sealVar_complete (c := c) p.x xv st₁ (hx.mono hrunY.nv_le hrunY.le)
  exact ⟨⟨rx, ry⟩, st₂, hrunY.bind (hrunX.bind rfl), fun hnv hle =>
    Sat.bind hrunY (hsatY (Nat.le_trans hrunX.nv_le hnv) (hrunX.le.trans hle))
      (Sat.bind hrunX (hsatX hnv hle) Sat.pure),
    hrx, hry.mono hrunX.nv_le hrunX.le⟩

open WeierstrassCurve.Affine in
/-- **`addFast`'s completeness.** From operands lying on the curve, with `y₁ ≠ 0` and —
in the `checkFinite` mode — a finite sum, the run succeeds, the row it emits is satisfied
at every extension of the final table, the result is scoped, and where the sum is finite
the result READS it — the gadget's own soundness spec at the honest table, so a caller
never rebuilds the point.

The row's satisfaction is the verified gate's own completeness: the advice computes
exactly `Kimchi.Gate.AddComplete.build`'s canonical row, so the reading of
the emitted payload IS that row and `complete_build` discharges it. -/
theorem addFast_complete [Field F] [DecidableEq F] (fin : Finiteness)
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (htwo : (2 : F) ≠ 0) (p1' p2' : AffinePoint (FVar F)) (P Q : W.Point) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => OnCurve W st p1' P ∧ OnCurve W st p2' Q ∧
        P + P ≠ 0 ∧ (fin = .checkFinite → P + Q ≠ 0))
      (addFast (c := KimchiConstraint F) fin p1' p2')
      (fun r st' => CircuitType.Scoped (val := AffinePoint F) st' r.p ∧
        (↑r.isInfinity : CVar F).Scoped st' ∧
        (P + Q ≠ 0 → OnCurve W st' r.p (P + Q))) := by
  have hbase : Complete (F := F) (c := KimchiConstraint F)
      (fun st => OnCurve W st p1' P ∧ OnCurve W st p2' Q ∧
        P + P ≠ 0 ∧ (fin = .checkFinite → P + Q ≠ 0))
      (addFast (c := KimchiConstraint F) fin p1' p2')
      (fun r st' => CircuitType.Scoped (val := AffinePoint F) st' r.p ∧
        (↑r.isInfinity : CVar F).Scoped st') := by
    rintro st ⟨⟨hs1, hP⟩, ⟨hs2, n2, rfl⟩, hPP, hfinP⟩
    have hy1ne : p1'.y.val st.env.get ≠ 0 :=
      fun hy => hPP (two_torsion_of_y_eq_zero ha hP hy)
    obtain ⟨n1, rfl⟩ := hP
    have hon1 : W.Equation (p1'.x.val st.env.get) (p1'.y.val st.env.get) := n1.left
    have hon2 : W.Equation (p2'.x.val st.env.get) (p2'.y.val st.env.get) := n2.left
    have hfin : fin = .checkFinite → ¬(p1'.x.val st.env.get = p2'.x.val st.env.get ∧
        p1'.y.val st.env.get = W.negY (p2'.x.val st.env.get) (p2'.y.val st.env.get)) := by
      rintro hf ⟨hx, hy⟩
      refine hfinP hf ?_
      rw [add_eq_zero_iff_eq_neg, Point.neg_some]
      congr 1
    rw [scoped_affinePoint] at hs1 hs2
    obtain ⟨x1, hvx1⟩ : ∃ v, p1'.x.val st.env.get = v := ⟨_, rfl⟩
    obtain ⟨y1, hvy1⟩ : ∃ v, p1'.y.val st.env.get = v := ⟨_, rfl⟩
    obtain ⟨x2, hvx2⟩ : ∃ v, p2'.x.val st.env.get = v := ⟨_, rfl⟩
    obtain ⟨y2, hvy2⟩ : ∃ v, p2'.y.val st.env.get = v := ⟨_, rfl⟩
    rw [hvx1, hvy1] at hon1
    rw [hvx2, hvy2] at hon2
    rw [hvy1] at hy1ne
    rw [hvx1, hvy1, hvx2, hvy2] at hfin
    -- the sealed operands
    obtain ⟨q1, st₁, hrunS1, hsatS1, hR1x, hR1y⟩ :=
      sealPoint_complete (c := KimchiConstraint F) p1' x1 y1 st
        ⟨⟨CircuitType.scoped_fvar.mpr hs1.1, CircuitType.reads_fvar.mpr hvx1⟩,
          ⟨CircuitType.scoped_fvar.mpr hs1.2, CircuitType.reads_fvar.mpr hvy1⟩⟩
    obtain ⟨q2, st₂, hrunS2, hsatS2, hR2x, hR2y⟩ :=
      sealPoint_complete (c := KimchiConstraint F) p2' x2 y2 st₁
        ⟨⟨CircuitType.scoped_fvar.mpr (hs2.1.mono hrunS1.nv_le),
            CircuitType.reads_fvar.mpr (by rw [CVar.val_of_le hrunS1.le hs2.1, hvx2])⟩,
          ⟨CircuitType.scoped_fvar.mpr (hs2.2.mono hrunS1.nv_le),
            CircuitType.reads_fvar.mpr (by rw [CVar.val_of_le hrunS1.le hs2.2, hvy2])⟩⟩
    have hq1x : q1.x.Scoped st₁ := CircuitType.scoped_fvar.mp hR1x.1
    have hq1y : q1.y.Scoped st₁ := CircuitType.scoped_fvar.mp hR1y.1
    have hq2x : q2.x.Scoped st₂ := CircuitType.scoped_fvar.mp hR2x.1
    have hq2y : q2.y.Scoped st₂ := CircuitType.scoped_fvar.mp hR2y.1
    -- the sealed coordinates read as the operands
    have e1x : q1.x.val st₂.env.get = x1 :=
      CircuitType.reads_fvar.mp (CircuitType.ReadsAs.mono hrunS2.nv_le hrunS2.le hR1x).2
    have e1y : q1.y.val st₂.env.get = y1 :=
      CircuitType.reads_fvar.mp (CircuitType.ReadsAs.mono hrunS2.nv_le hrunS2.le hR1y).2
    have e2x : q2.x.val st₂.env.get = x2 := CircuitType.reads_fvar.mp hR2x.2
    have e2y : q2.y.val st₂.env.get = y2 := CircuitType.reads_fvar.mp hR2y.2
    have hq1x₂ : q1.x.Scoped st₂ := hq1x.mono hrunS2.nv_le
    have hq1y₂ : q1.y.Scoped st₂ := hq1y.mono hrunS2.nv_le
    -- the `sameX` column
    obtain ⟨sameXU, st₃, hrunX, hsatX, hnvX, hleX, hscX, hrdX⟩ :=
      witness_complete (c := KimchiConstraint F) (val := UnChecked Bool)
        (addFast.sameXAdvice q1 q2) (st := st₂) (v := ⟨decide (x1 = x2)⟩)
        (by simp [addFast.sameXAdvice, AsProver.readCVar_run hq1x₂,
          AsProver.readCVar_run hq2x, e1x, e2x])
    have hrdSX : CircuitType.Reads (val := Bool) st₃.env.get sameXU.val (decide (x1 = x2)) :=
      CircuitType.reads_unchecked.mp hrdX
    have hscSX : CircuitType.Scoped (val := Bool) st₃ sameXU.val :=
      CircuitType.scoped_unchecked.mp hscX
    have hvalSX : CircuitType.readVal (val := Bool) st₃.env.get sameXU.val = decide (x1 = x2) :=
      (CircuitType.reads_iff.mp hrdSX).2
    have hbitSX : (↑sameXU.val : CVar F).val st₃.env.get = bit (decide (x1 = x2)) :=
      CircuitType.reads_boolVar.mp hrdSX
    have e1x₃ : q1.x.val st₃.env.get = x1 := by
      rw [CVar.val_of_le hleX hq1x₂, e1x]
    have e1y₃ : q1.y.val st₃.env.get = y1 := by
      rw [CVar.val_of_le hleX hq1y₂, e1y]
    have e2x₃ : q2.x.val st₃.env.get = x2 := by
      rw [CVar.val_of_le hleX hq2x, e2x]
    have e2y₃ : q2.y.val st₃.env.get = y2 := by
      rw [CVar.val_of_le hleX hq2y, e2y]
    have hq1x₃ : q1.x.Scoped st₃ := hq1x₂.mono hnvX
    have hq1y₃ : q1.y.Scoped st₃ := hq1y₂.mono hnvX
    have hq2x₃ : q2.x.Scoped st₃ := hq2x.mono hnvX
    have hq2y₃ : q2.y.Scoped st₃ := hq2y.mono hnvX
    -- the infinity flag: constant in the checked mode, witnessed otherwise
    obtain ⟨inf, st₄, hrunI, hsatI, hnvI, hleI, hscI, hrdI⟩ :
        ∃ (inf : BoolVar F) (st₄ : ProverState F),
          Runs (addFast.infColumn (c := KimchiConstraint F) fin q1 q2 sameXU.val)
            st₃ inf st₄ ∧
          (∀ {stf : ProverState F}, st₄.nv ≤ stf.nv → st₄.env.Le stf.env →
            Sat (addFast.infColumn (c := KimchiConstraint F) fin q1 q2 sameXU.val) st₃ stf) ∧
          st₃.nv ≤ st₄.nv ∧ st₃.env.Le st₄.env ∧ (↑inf : CVar F).Scoped st₄ ∧
          (↑inf : CVar F).val st₄.env.get =
            (if fin = .checkFinite then 0
             else bit (decide (x1 = x2) && !decide (y1 = y2))) := by
      cases fin with
      | checkFinite =>
        exact ⟨false_, st₃, rfl,
          fun _ _ => by simp [Sat, addFast.infColumn, Snarky.build], Nat.le_refl _,
          Assignments.Le.refl _, by simp, by simp⟩
      | dontCheckFinite =>
        obtain ⟨r, st₄, hrun, hsat, hnv, hle, hsc, hrd⟩ :=
          witness_complete (c := KimchiConstraint F) (val := UnChecked Bool)
            (addFast.infAdvice q1 q2 sameXU.val) (st := st₃)
            (v := ⟨decide (x1 = x2) && !decide (y1 = y2)⟩)
            (by simp [addFast.infAdvice, readVar_run hscSX, hvalSX,
              AsProver.readCVar_run hq1y₃, AsProver.readCVar_run hq2y₃, e1y₃, e2y₃])
        exact ⟨r.val, st₄, hrun.bind rfl, fun hnv' hle' =>
          Sat.bind hrun (hsat hnv' hle') Sat.pure, hnv, hle,
          CircuitType.scoped_fvar.mp (CircuitType.scoped_unchecked.mp hsc),
          by rw [CircuitType.reads_boolVar.mp (CircuitType.reads_unchecked.mp hrd)]; simp⟩
    -- carry the readings past the flag
    have e1x₄ : q1.x.val st₄.env.get = x1 := by rw [CVar.val_of_le hleI hq1x₃, e1x₃]
    have e1y₄ : q1.y.val st₄.env.get = y1 := by rw [CVar.val_of_le hleI hq1y₃, e1y₃]
    have e2x₄ : q2.x.val st₄.env.get = x2 := by rw [CVar.val_of_le hleI hq2x₃, e2x₃]
    have e2y₄ : q2.y.val st₄.env.get = y2 := by rw [CVar.val_of_le hleI hq2y₃, e2y₃]
    have hq1x₄ : q1.x.Scoped st₄ := hq1x₃.mono hnvI
    have hq1y₄ : q1.y.Scoped st₄ := hq1y₃.mono hnvI
    have hq2x₄ : q2.x.Scoped st₄ := hq2x₃.mono hnvI
    have hq2y₄ : q2.y.Scoped st₄ := hq2y₃.mono hnvI
    have hscSX₄ : CircuitType.Scoped (val := Bool) st₄ sameXU.val := hscSX.mono hnvI
    have hvalSX₄ : CircuitType.readVal (val := Bool) st₄.env.get sameXU.val
        = decide (x1 = x2) :=
      (CircuitType.reads_iff.mp ((hrdSX.of_le hscSX hleI))).2
    -- the three auxiliary columns, in one witness
    obtain ⟨aux, st₅, hrunA, hsatA, hnvA, hleA, hscA, hrdA⟩ :=
      witness_complete (c := KimchiConstraint F) (val := AddAux F)
        (addFast.auxAdvice q1 q2 sameXU.val) (st := st₄)
        (v := ⟨if y1 = y2 then 0 else if x1 = x2 then (y2 - y1)⁻¹ else 0,
               if x1 = x2 then 0 else (x2 - x1)⁻¹,
               if x1 = x2 then 3 * x1 * x1 / (2 * y1) else (y2 - y1) / (x2 - x1)⟩)
        (by
          by_cases h : y1 = y2 <;> by_cases h2 : x1 = x2 <;>
            simp [addFast.auxAdvice, readVar_run hscSX₄, hvalSX₄,
              AsProver.readCVar_run hq1x₄, AsProver.readCVar_run hq1y₄,
              AsProver.readCVar_run hq2x₄, AsProver.readCVar_run hq2y₄,
              e1x₄, e1y₄, e2x₄, e2y₄, h, h2])
    rw [scoped_addAux] at hscA
    rw [reads_addAux] at hrdA
    obtain ⟨sv, hsv⟩ : ∃ v, (if x1 = x2 then 3 * x1 * x1 / (2 * y1)
        else (y2 - y1) / (x2 - x1)) = v := ⟨_, rfl⟩
    rw [hsv] at hrdA
    have e1x₅ : q1.x.val st₅.env.get = x1 := by rw [CVar.val_of_le hleA hq1x₄, e1x₄]
    have e1y₅ : q1.y.val st₅.env.get = y1 := by rw [CVar.val_of_le hleA hq1y₄, e1y₄]
    have e2x₅ : q2.x.val st₅.env.get = x2 := by rw [CVar.val_of_le hleA hq2x₄, e2x₄]
    have hq1x₅ : q1.x.Scoped st₅ := hq1x₄.mono hnvA
    have hq1y₅ : q1.y.Scoped st₅ := hq1y₄.mono hnvA
    have hq2x₅ : q2.x.Scoped st₅ := hq2x₄.mono hnvA
    -- the sum, witnessed as one point
    obtain ⟨p3, st₆, hrunP, hsatP, hnvP, hleP, hscP, hrdP⟩ :=
      witness_complete (c := KimchiConstraint F) (val := AffinePoint F)
        (addFast.sumAdvice q1 q2 aux.s) (st := st₅)
        (v := ⟨sv * sv - (x1 + x2), sv * (x1 - (sv * sv - (x1 + x2))) - y1⟩)
        (by
          simp [addFast.sumAdvice, AsProver.readCVar_run hscA.2.2,
            AsProver.readCVar_run hq1x₅, AsProver.readCVar_run hq2x₅,
            AsProver.readCVar_run hq1y₅, hrdA.2.2, e1x₅, e2x₅, e1y₅])
    rw [reads_affinePoint] at hrdP
    rw [scoped_affinePoint] at hscP
    refine ⟨⟨p3, inf⟩, st₆, ?_, ?_, ?_⟩
    · refine hrunS1.bind (hrunS2.bind (hrunX.bind (hrunI.bind (hrunA.bind
        (hrunP.bind ?_)))))
      exact Runs.addConstraint.bind rfl
    · intro stf hnvF hleF
      have L6 : st₆.env.Le stf.env := hleF
      have L5 : st₅.env.Le stf.env := hleP.trans L6
      have L4 : st₄.env.Le stf.env := hleA.trans L5
      have L3 : st₃.env.Le stf.env := hleI.trans L4
      have L2 : st₂.env.Le stf.env := hleX.trans L3
      have N6 : st₆.nv ≤ stf.nv := hnvF
      have N5 : st₅.nv ≤ stf.nv := Nat.le_trans hnvP N6
      have N4 : st₄.nv ≤ stf.nv := Nat.le_trans hnvA N5
      have N3 : st₃.nv ≤ stf.nv := Nat.le_trans hnvI N4
      have N2 : st₂.nv ≤ stf.nv := Nat.le_trans hnvX N3
      refine Sat.bind hrunS1 (hsatS1 (Nat.le_trans hrunS2.nv_le N2) (hrunS2.le.trans L2))
        (Sat.bind hrunS2 (hsatS2 N2 L2)
          (Sat.bind hrunX (hsatX N3 L3)
            (Sat.bind hrunI (hsatI N4 L4)
              (Sat.bind hrunA (hsatA N5 L5)
                (Sat.bind hrunP (hsatP N6 L6)
                  (Sat.bind Runs.addConstraint (Sat.addConstraint ?_) Sat.pure))))))
      -- the emitted row reads as the gate's canonical one
      show Kimchi.Gate.AddComplete.Holds (AddComplete.read stf.env.get _)
      have hread : AddComplete.read (F := F) stf.env.get
          { p1 := q1, p2 := q2, p3 := p3, inf := (↑inf : CVar F),
            sameX := (↑sameXU.val : CVar F), s := aux.s, infZ := aux.infZ,
            x21Inv := aux.x21Inv }
          = Kimchi.Gate.AddComplete.build (decide (fin = .checkFinite)) x1 y1 x2 y2 := by
        have r1x : q1.x.val stf.env.get = x1 := by rw [CVar.val_of_le L2 hq1x₂, e1x]
        have r1y : q1.y.val stf.env.get = y1 := by rw [CVar.val_of_le L2 hq1y₂, e1y]
        have r2x : q2.x.val stf.env.get = x2 := by rw [CVar.val_of_le L2 hq2x, e2x]
        have r2y : q2.y.val stf.env.get = y2 := by rw [CVar.val_of_le L2 hq2y, e2y]
        have rsx : (↑sameXU.val : CVar F).val stf.env.get = bit (decide (x1 = x2)) := by
          rw [CVar.val_of_le L3 (CircuitType.scoped_fvar.mp hscSX), hbitSX]
        have rinf : (↑inf : CVar F).val stf.env.get
            = (if fin = .checkFinite then 0
               else bit (decide (x1 = x2) && !decide (y1 = y2))) := by
          rw [CVar.val_of_le L4 hscI, hrdI]
        have rz : aux.infZ.val stf.env.get
            = (if y1 = y2 then 0 else if x1 = x2 then (y2 - y1)⁻¹ else 0) := by
          rw [CVar.val_of_le L5 hscA.1, hrdA.1]
        have rv : aux.x21Inv.val stf.env.get = (if x1 = x2 then 0 else (x2 - x1)⁻¹) := by
          rw [CVar.val_of_le L5 hscA.2.1, hrdA.2.1]
        have rl : aux.s.val stf.env.get = sv := by
          rw [CVar.val_of_le L5 hscA.2.2, hrdA.2.2]
        have r3x : p3.x.val stf.env.get = sv * sv - (x1 + x2) := by
          rw [CVar.val_of_le L6 hscP.1, hrdP.1]
        have r3y : p3.y.val stf.env.get = sv * (x1 - (sv * sv - (x1 + x2))) - y1 := by
          rw [CVar.val_of_le L6 hscP.2, hrdP.2]
        simp only [AddComplete.read, Kimchi.Gate.AddComplete.build, r1x, r1y, r2x, r2y,
          rsx, rinf, rz, rv, rl, r3x, r3y, ← hsv]
        cases fin <;> simp [bit]
      rw [hread]
      exact Kimchi.Gate.AddComplete.complete_build W ha hon1 hon2 hy1ne htwo
        (fun h => hfin (of_decide_eq_true h))
    · exact ⟨scoped_affinePoint.mpr ⟨hscP.1, hscP.2⟩, hscI.mono (Nat.le_trans hnvA hnvP)⟩
  intro st hpre
  obtain ⟨r, st', hrun, hsat, ⟨hscP, hscI⟩, hspec⟩ :=
    Complete.post (fun V => addFast_spec (V := V) fin W ha htwo p1' p2') hbase st hpre
  refine ⟨r, st', hrun, hsat, hscP, hscI, ?_⟩
  intro hPQ
  obtain ⟨hp1, hp2, hPP, -⟩ := hpre
  rcases hspec.2 P Q (hp1.mono hrun.nv_le hrun.le).2 (hp2.mono hrun.nv_le hrun.le).2 hPP with
    ⟨-, hzero⟩ | ⟨-, hon⟩
  · exact absurd hzero hPQ
  · exact ⟨hscP, hon⟩

attribute [irreducible] sealPoint addFast addFast.infColumn

end Snarky.Kimchi
