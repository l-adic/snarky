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
  check_runs _ _ _ := rfl
  check_sat _ _ _ _ _ _ _ _ con hcon := by simp [build] at hcon

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
  let infZ ← witness (val := F) (infZAdvice p1 p2 sameX)
  let x21Inv ← witness (val := F) (x21InvAdvice p1 p2 sameX)
  let s ← witness (val := F) (slopeAdvice p1 p2 sameX)
  let p3 ← witness (val := AffinePoint F) (sumAdvice p1 p2 s)
  addConstraint (KimchiSystem.addComplete
    { p1 := p1, p2 := p2, p3 := p3, inf := inf.toCVar,
      sameX := sameX.toCVar, s := s, infZ := infZ, x21Inv := x21Inv })
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
  /-- `0` on equal y-coordinates, else the inverse of `y₂ − y₁` where the
  x-coordinates coincide — the value pinning the infinity flag. -/
  infZAdvice (p1 p2 : AffinePoint (FVar F)) (sameX : BoolVar F) : AsProver F F := do
    let y1 ← AsProver.readCVar p1.y
    let y2 ← AsProver.readCVar p2.y
    if y1 = y2 then pure 0
    else do
      let sx ← readVar (val := Bool) sameX
      if sx then pure (y2 - y1)⁻¹ else pure 0
  /-- The inverse of `x₂ − x₁` where the x-coordinates differ — the value pinning
  `sameX`. -/
  x21InvAdvice (p1 p2 : AffinePoint (FVar F)) (sameX : BoolVar F) : AsProver F F := do
    let sx ← readVar (val := Bool) sameX
    if sx then pure 0
    else do
      let x1 ← AsProver.readCVar p1.x
      let x2 ← AsProver.readCVar p2.x
      pure (x2 - x1)⁻¹
  /-- The slope: the tangent `3x₁²/(2y₁)` where the x-coordinates coincide, else the
  secant `(y₂−y₁)/(x₂−x₁)`. -/
  slopeAdvice (p1 p2 : AffinePoint (FVar F)) (sameX : BoolVar F) : AsProver F F := do
    let sx ← readVar (val := Bool) sameX
    let x1 ← AsProver.readCVar p1.x
    let y1 ← AsProver.readCVar p1.y
    if sx then pure (3 * x1 * x1 / (2 * y1))
    else do
      let x2 ← AsProver.readCVar p2.x
      let y2 ← AsProver.readCVar p2.y
      pure ((y2 - y1) / (x2 - x1))
  /-- The sum: `x₃ = s² − (x₁ + x₂)` and `y₃ = s·(x₁ − x₃) − y₁`, witnessed as the
  one point the gate's last two columns hold. -/
  sumAdvice (p1 p2 : AffinePoint (FVar F)) (s : FVar F) : AsProver F (AffinePoint F) := do
    let sv ← AsProver.readCVar s
    let x1 ← AsProver.readCVar p1.x
    let x2 ← AsProver.readCVar p2.x
    let y1 ← AsProver.readCVar p1.y
    let x3 := sv * sv - (x1 + x2)
    pure ⟨x3, sv * (x1 - x3) - y1⟩

/-! ## Completeness -/

/-- Sealing a point: the run succeeds, its rows hold at every extension of the final
table, and the sealed point is scoped and reads as the operand. -/
theorem sealPoint_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (p : AffinePoint (FVar F)) :
    Complete (F := F) (c := c)
      (fun st => p.x.Scoped st ∧ p.y.Scoped st)
      (sealPoint (c := c) p)
      (fun r st' => r.x.Scoped st' ∧ r.y.Scoped st' ∧
        r.x.val st'.env.get = p.x.val st'.env.get ∧
        r.y.val st'.env.get = p.y.val st'.env.get) := by
  rintro st ⟨hx, hy⟩
  obtain ⟨ry, st₁, hrunY, hsatY, hscopeY, hreadY⟩ :=
    Complete.post (fun V => sealVar_spec (c := c) (V := V) p.y) (sealVar_complete p.y) st hy
  obtain ⟨rx, st₂, hrunX, hsatX, hscopeX, hreadX⟩ :=
    Complete.post (fun V => sealVar_spec (c := c) (V := V) p.x) (sealVar_complete p.x) st₁
      (hx.mono hrunY.nv_le)
  refine ⟨⟨rx, ry⟩, st₂, hrunY.bind (hrunX.bind rfl), fun hnv hle =>
    Sat.bind hrunY (hsatY (Nat.le_trans hrunX.nv_le hnv) (hrunX.le.trans hle))
      (Sat.bind hrunX (hsatX hnv hle) Sat.pure),
    hscopeX, hscopeY.mono hrunX.nv_le, hreadX, ?_⟩
  rw [CVar.val_of_le hrunX.le hscopeY,
    CVar.val_of_le hrunX.le (hy.mono hrunY.nv_le), hreadY]

/-- **`addFast`'s completeness.** From scoped operands lying on the curve, with
`y₁ ≠ 0` and — in the `checkFinite` mode — a finite sum, the run succeeds, the row it
emits is satisfied at every extension of the final table, and the result is scoped.

The row's satisfaction is the verified gate's own completeness: the advice computes
exactly `Kimchi.Gate.AddComplete.build`'s canonical row, so the reading of
the emitted payload IS that row and `complete_build` discharges it. -/
theorem addFast_complete [Field F] [DecidableEq F] (fin : Finiteness)
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (htwo : (2 : F) ≠ 0) (p1' p2' : AffinePoint (FVar F)) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => CircuitType.Scoped (val := AffinePoint F) st p1' ∧
        CircuitType.Scoped (val := AffinePoint F) st p2' ∧
        W.Equation (p1'.x.val st.env.get) (p1'.y.val st.env.get) ∧
        W.Equation (p2'.x.val st.env.get) (p2'.y.val st.env.get) ∧
        p1'.y.val st.env.get ≠ 0 ∧
        (fin = .checkFinite → ¬(p1'.x.val st.env.get = p2'.x.val st.env.get ∧
          p1'.y.val st.env.get = W.negY (p2'.x.val st.env.get) (p2'.y.val st.env.get))))
      (addFast (c := KimchiConstraint F) fin p1' p2')
      (fun r st' => CircuitType.Scoped (val := AffinePoint F) st' r.p ∧
        (↑r.isInfinity : CVar F).Scoped st') := by
  rintro st ⟨hs1, hs2, hon1, hon2, hy1ne, hfin⟩
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
  obtain ⟨q1, st₁, hrunS1, hsatS1, hq1x, hq1y, hr1x, hr1y⟩ :=
    sealPoint_complete (c := KimchiConstraint F) p1' st hs1
  obtain ⟨q2, st₂, hrunS2, hsatS2, hq2x, hq2y, hr2x, hr2y⟩ :=
    sealPoint_complete (c := KimchiConstraint F) p2' st₁
      ⟨hs2.1.mono hrunS1.nv_le, hs2.2.mono hrunS1.nv_le⟩
  -- the sealed coordinates read as the operands
  have e1x : q1.x.val st₂.env.get = x1 := by
    rw [CVar.val_of_le hrunS2.le hq1x, hr1x, CVar.val_of_le hrunS1.le hs1.1, hvx1]
  have e1y : q1.y.val st₂.env.get = y1 := by
    rw [CVar.val_of_le hrunS2.le hq1y, hr1y, CVar.val_of_le hrunS1.le hs1.2, hvy1]
  have e2x : q2.x.val st₂.env.get = x2 := by
    rw [hr2x, CVar.val_of_le hrunS2.le (hs2.1.mono hrunS1.nv_le),
      CVar.val_of_le hrunS1.le hs2.1, hvx2]
  have e2y : q2.y.val st₂.env.get = y2 := by
    rw [hr2y, CVar.val_of_le hrunS2.le (hs2.2.mono hrunS1.nv_le),
      CVar.val_of_le hrunS1.le hs2.2, hvy2]
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
  -- `infZ`
  obtain ⟨infZ, st₅, hrunZ, hsatZ, hnvZ, hleZ, hscZ, hrdZ⟩ :=
    witness_complete (c := KimchiConstraint F) (val := F)
      (addFast.infZAdvice q1 q2 sameXU.val) (st := st₄)
      (v := if y1 = y2 then 0 else if x1 = x2 then (y2 - y1)⁻¹ else 0)
      (by
        by_cases h : y1 = y2 <;> by_cases h2 : x1 = x2 <;>
          simp [addFast.infZAdvice, AsProver.readCVar_run hq1y₄,
            AsProver.readCVar_run hq2y₄, e1y₄, e2y₄, readVar_run hscSX₄, hvalSX₄, h, h2])
  have e1x₅ : q1.x.val st₅.env.get = x1 := by rw [CVar.val_of_le hleZ hq1x₄, e1x₄]
  have e1y₅ : q1.y.val st₅.env.get = y1 := by rw [CVar.val_of_le hleZ hq1y₄, e1y₄]
  have e2x₅ : q2.x.val st₅.env.get = x2 := by rw [CVar.val_of_le hleZ hq2x₄, e2x₄]
  have e2y₅ : q2.y.val st₅.env.get = y2 := by rw [CVar.val_of_le hleZ hq2y₄, e2y₄]
  have hq1x₅ : q1.x.Scoped st₅ := hq1x₄.mono hnvZ
  have hq1y₅ : q1.y.Scoped st₅ := hq1y₄.mono hnvZ
  have hq2x₅ : q2.x.Scoped st₅ := hq2x₄.mono hnvZ
  have hq2y₅ : q2.y.Scoped st₅ := hq2y₄.mono hnvZ
  have hscSX₅ : CircuitType.Scoped (val := Bool) st₅ sameXU.val := hscSX₄.mono hnvZ
  have hvalSX₅ : CircuitType.readVal (val := Bool) st₅.env.get sameXU.val
      = decide (x1 = x2) :=
    (CircuitType.reads_iff.mp ((hrdSX.of_le hscSX (hleI.trans hleZ)))).2
  -- `x21Inv`
  obtain ⟨x21Inv, st₆, hrunV, hsatV, hnvV, hleV, hscV, hrdV⟩ :=
    witness_complete (c := KimchiConstraint F) (val := F)
      (addFast.x21InvAdvice q1 q2 sameXU.val) (st := st₅)
      (v := if x1 = x2 then 0 else (x2 - x1)⁻¹)
      (by
        by_cases h2 : x1 = x2 <;>
          simp [addFast.x21InvAdvice, AsProver.readCVar_run hq1x₅,
            AsProver.readCVar_run hq2x₅, e1x₅, e2x₅, readVar_run hscSX₅, hvalSX₅, h2])
  have e1x₆ : q1.x.val st₆.env.get = x1 := by rw [CVar.val_of_le hleV hq1x₅, e1x₅]
  have e1y₆ : q1.y.val st₆.env.get = y1 := by rw [CVar.val_of_le hleV hq1y₅, e1y₅]
  have e2x₆ : q2.x.val st₆.env.get = x2 := by rw [CVar.val_of_le hleV hq2x₅, e2x₅]
  have e2y₆ : q2.y.val st₆.env.get = y2 := by rw [CVar.val_of_le hleV hq2y₅, e2y₅]
  have hq1x₆ : q1.x.Scoped st₆ := hq1x₅.mono hnvV
  have hq1y₆ : q1.y.Scoped st₆ := hq1y₅.mono hnvV
  have hq2x₆ : q2.x.Scoped st₆ := hq2x₅.mono hnvV
  have hq2y₆ : q2.y.Scoped st₆ := hq2y₅.mono hnvV
  have hscSX₆ : CircuitType.Scoped (val := Bool) st₆ sameXU.val := hscSX₅.mono hnvV
  have hvalSX₆ : CircuitType.readVal (val := Bool) st₆.env.get sameXU.val
      = decide (x1 = x2) :=
    (CircuitType.reads_iff.mp ((hrdSX.of_le hscSX ((hleI.trans hleZ).trans hleV)))).2
  -- the slope
  obtain ⟨sl, st₇, hrunL, hsatL, hnvL, hleL, hscL, hrdL⟩ :=
    witness_complete (c := KimchiConstraint F) (val := F)
      (addFast.slopeAdvice q1 q2 sameXU.val) (st := st₆)
      (v := if x1 = x2 then 3 * x1 * x1 / (2 * y1) else (y2 - y1) / (x2 - x1))
      (by
        by_cases h2 : x1 = x2 <;>
          simp [addFast.slopeAdvice, AsProver.readCVar_run hq1x₆,
            AsProver.readCVar_run hq1y₆, AsProver.readCVar_run hq2x₆,
            AsProver.readCVar_run hq2y₆, e1x₆, e1y₆, e2x₆, e2y₆,
            readVar_run hscSX₆, hvalSX₆, h2])
  obtain ⟨sv, hsv⟩ : ∃ v, (if x1 = x2 then 3 * x1 * x1 / (2 * y1)
      else (y2 - y1) / (x2 - x1)) = v := ⟨_, rfl⟩
  rw [hsv] at hrdL
  have hslSc : sl.Scoped st₇ := CircuitType.scoped_fvar.mp hscL
  have hslRd : sl.val st₇.env.get = sv := CircuitType.reads_fvar.mp hrdL
  have e1x₇ : q1.x.val st₇.env.get = x1 := by rw [CVar.val_of_le hleL hq1x₆, e1x₆]
  have e1y₇ : q1.y.val st₇.env.get = y1 := by rw [CVar.val_of_le hleL hq1y₆, e1y₆]
  have e2x₇ : q2.x.val st₇.env.get = x2 := by rw [CVar.val_of_le hleL hq2x₆, e2x₆]
  have hq1x₇ : q1.x.Scoped st₇ := hq1x₆.mono hnvL
  have hq1y₇ : q1.y.Scoped st₇ := hq1y₆.mono hnvL
  have hq2x₇ : q2.x.Scoped st₇ := hq2x₆.mono hnvL
  -- the sum, witnessed as one point
  obtain ⟨p3, st₈, hrunP, hsatP, hnvP, hleP, hscP, hrdP⟩ :=
    witness_complete (c := KimchiConstraint F) (val := AffinePoint F)
      (addFast.sumAdvice q1 q2 sl) (st := st₇)
      (v := ⟨sv * sv - (x1 + x2), sv * (x1 - (sv * sv - (x1 + x2))) - y1⟩)
      (by
        simp [addFast.sumAdvice, AsProver.readCVar_run hslSc, AsProver.readCVar_run hq1x₇,
          AsProver.readCVar_run hq2x₇, AsProver.readCVar_run hq1y₇, hslRd, e1x₇, e2x₇, e1y₇])
  rw [reads_affinePoint] at hrdP
  rw [scoped_affinePoint] at hscP
  refine ⟨⟨p3, inf⟩, st₈, ?_, ?_, ?_⟩
  · refine hrunS1.bind (hrunS2.bind (hrunX.bind (hrunI.bind (hrunZ.bind (hrunV.bind
      (hrunL.bind (hrunP.bind ?_)))))))
    exact Runs.addConstraint.bind rfl
  · intro stf hnvF hleF
    have L8 : st₈.env.Le stf.env := hleF
    have L7 : st₇.env.Le stf.env := hleP.trans L8
    have L6 : st₆.env.Le stf.env := hleL.trans L7
    have L5 : st₅.env.Le stf.env := hleV.trans L6
    have L4 : st₄.env.Le stf.env := hleZ.trans L5
    have L3 : st₃.env.Le stf.env := hleI.trans L4
    have L2 : st₂.env.Le stf.env := hleX.trans L3
    have N8 : st₈.nv ≤ stf.nv := hnvF
    have N7 : st₇.nv ≤ stf.nv := Nat.le_trans hnvP N8
    have N6 : st₆.nv ≤ stf.nv := Nat.le_trans hnvL N7
    have N5 : st₅.nv ≤ stf.nv := Nat.le_trans hnvV N6
    have N4 : st₄.nv ≤ stf.nv := Nat.le_trans hnvZ N5
    have N3 : st₃.nv ≤ stf.nv := Nat.le_trans hnvI N4
    have N2 : st₂.nv ≤ stf.nv := Nat.le_trans hnvX N3
    refine Sat.bind hrunS1 (hsatS1 (Nat.le_trans hrunS2.nv_le N2) (hrunS2.le.trans L2))
      (Sat.bind hrunS2 (hsatS2 N2 L2)
        (Sat.bind hrunX (hsatX N3 L3)
          (Sat.bind hrunI (hsatI N4 L4)
            (Sat.bind hrunZ (hsatZ N5 L5)
              (Sat.bind hrunV (hsatV N6 L6)
                (Sat.bind hrunL (hsatL N7 L7)
                  (Sat.bind hrunP (hsatP N8 L8)
                    (Sat.bind Runs.addConstraint (Sat.addConstraint ?_) Sat.pure))))))))
    -- the emitted row reads as the gate's canonical one
    show Kimchi.Gate.AddComplete.Holds (AddComplete.read stf.env.get _)
    have hread : AddComplete.read (F := F) stf.env.get
        { p1 := q1, p2 := q2, p3 := p3, inf := (↑inf : CVar F),
          sameX := (↑sameXU.val : CVar F), s := sl, infZ := infZ, x21Inv := x21Inv }
        = Kimchi.Gate.AddComplete.build (decide (fin = .checkFinite)) x1 y1 x2 y2 := by
      have r1x : q1.x.val stf.env.get = x1 := by rw [CVar.val_of_le L2 hq1x₂, e1x]
      have r1y : q1.y.val stf.env.get = y1 := by rw [CVar.val_of_le L2 hq1y₂, e1y]
      have r2x : q2.x.val stf.env.get = x2 := by rw [CVar.val_of_le L2 hq2x, e2x]
      have r2y : q2.y.val stf.env.get = y2 := by rw [CVar.val_of_le L2 hq2y, e2y]
      have rsx : (↑sameXU.val : CVar F).val stf.env.get = bit (decide (x1 = x2)) := by
        rw [CVar.val_of_le L3 (CircuitType.scoped_fvar.mp hscSX), hbitSX]
      have rinf : (↑inf : CVar F).val stf.env.get
          = (if fin = .checkFinite then 0 else bit (decide (x1 = x2) && !decide (y1 = y2))) := by
        rw [CVar.val_of_le L4 hscI, hrdI]
      have rz : infZ.val stf.env.get
          = (if y1 = y2 then 0 else if x1 = x2 then (y2 - y1)⁻¹ else 0) := by
        rw [CVar.val_of_le L5 (CircuitType.scoped_fvar.mp hscZ),
          CircuitType.reads_fvar.mp hrdZ]
      have rv : x21Inv.val stf.env.get = (if x1 = x2 then 0 else (x2 - x1)⁻¹) := by
        rw [CVar.val_of_le L6 (CircuitType.scoped_fvar.mp hscV),
          CircuitType.reads_fvar.mp hrdV]
      have rl : sl.val stf.env.get = sv := by rw [CVar.val_of_le L7 hslSc, hslRd]
      have r3x : p3.x.val stf.env.get = sv * sv - (x1 + x2) := by
        rw [CVar.val_of_le L8 hscP.1, hrdP.1]
      have r3y : p3.y.val stf.env.get = sv * (x1 - (sv * sv - (x1 + x2))) - y1 := by
        rw [CVar.val_of_le L8 hscP.2, hrdP.2]
      simp only [AddComplete.read, Kimchi.Gate.AddComplete.build, r1x, r1y, r2x, r2y,
        rsx, rinf, rz, rv, rl, r3x, r3y, ← hsv]
      cases fin <;> simp [bit]
    rw [hread]
    exact Kimchi.Gate.AddComplete.complete_build W ha hon1 hon2 hy1ne htwo
      (fun h => hfin (of_decide_eq_true h))
  · exact ⟨scoped_affinePoint.mpr ⟨hscP.1, hscP.2⟩,
      hscI.mono (Nat.le_trans hnvZ (Nat.le_trans hnvV (Nat.le_trans hnvL hnvP)))⟩

/- PORT: the gadget's laws are OFF.

Soundness ports with friction (the reading vocabulary moved to a valuation) and
completeness is written fresh against `Complete`; neither is done. The definitions
above are what the constraint-system oracle exercises.

/-! ## Soundness: satisfied constraints read as the group sum -/

open Std.Do

/-- `sealPoint`'s promise: both sealed coordinates read as the operand point —
`sealVar_spec` walked over the two seals. -/
@[spec] private theorem sealPoint_spec [Field F] [DecidableEq F]
    (q : AffinePoint (FVar F))
    (Q : PostCond (AffinePoint (FVar F)) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AffinePoint (FVar F)) =>
        r.x.val V = q.x.val V ∧ r.y.val V = q.y.val V) Q⦄
    sealPoint (c := KimchiConstraint F) q
    ⦃Q⦄ := by
  simp only [sealPoint]
  mvcgen
  rename_i s hpre
  intro y _ hy
  mvcgen
  intro x _ hx
  intro _
  exact hpre ⟨x, y⟩ _ hx hy

open Std.Do in
/-- `sealPoint`'s honest run: readable coordinates seal, and the sealed point reads
as the operand — `sealVar_complete_spec` walked over the two seals. -/
@[spec] private theorem sealPoint_complete_spec {F c : Type} [CommSemiring F]
    [DecidableEq F] [BasicSystem F c] [Checker F c] [LawfulChecker F c]
    (q : AffinePoint (FVar F))
    (Q : PostCond (AffinePoint (FVar F))
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (q.x.eval env).isOk ∧ (q.y.eval env).isOk)
        (fun env r env' => ∀ xv yv, q.x.eval env = .ok xv → q.y.eval env = .ok yv →
          r.x.eval env' = .ok xv ∧ r.y.eval env' = .ok yv) Q⦄
    sealPoint (c := Prover c) q
    ⦃Q⦄ := by
  simp only [sealPoint]
  mvcgen
  rename_i st hpre
  obtain ⟨⟨hxok, hyok⟩, hk⟩ := hpre
  obtain ⟨xv, hxv⟩ := CVar.evalOk hxok
  refine ⟨hyok, fun ry sty hry hley => ?_⟩
  mvcgen
  refine ⟨by rw [CVar.eval_le hley hxv]; rfl, fun rx stx hrx hlex => ?_⟩
  mvcgen
  refine hk ⟨rx, ry⟩ stx (fun xv' yv' hx' hy' => ⟨?_, ?_⟩) (hley.trans hlex)
  · exact hrx xv' (CVar.eval_le hley hx')
  · exact CVar.eval_le hlex (hry yv' hy')

namespace AddFast

open WeierstrassCurve.Affine

/-- The tail's soundness, at the sealed operands: any satisfying valuation reads the
result as the group sum, via the verified gate's `sound`; the returned flag is the
`inf` argument itself (structural — how the `checkFinite` mode pins the finite
branch). Applied manually per mode — the curve parameters appear only in the promise,
so a registry application could not infer them. -/
private theorem addFastTail_spec [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0) (htwo : (2 : F) ≠ 0)
    (p1 p2 : AffinePoint (FVar F)) (sameX inf : BoolVar F)
    (Q : PostCond (AddResult F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AddResult F) =>
        r.isInfinity = inf ∧
        ∀ (h1 : W.Nonsingular (p1.x.val V) (p1.y.val V))
          (h2 : W.Nonsingular (p2.x.val V) (p2.y.val V)),
          p1.y.val V ≠ 0 →
          ((r.isInfinity.toCVar.val V = 1 ∧
             Point.some _ _ h1 + Point.some _ _ h2 = 0) ∨
           (r.isInfinity.toCVar.val V = 0 ∧
             ∃ h3 : W.Nonsingular (r.p.x.val V) (r.p.y.val V),
               Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3))) Q⦄
    addFastTail (c := KimchiConstraint F) p1 p2 sameX inf
    ⦃Q⦄ := by
  simp only [addFastTail]
  mvcgen
  rename_i s hpre
  intro infZ _
  mvcgen
  intro x21Inv _
  mvcgen
  intro sv _
  mvcgen
  intro x3 _
  mvcgen
  intro y3 _
  mvcgen
  intro u _ hpay
  intro _
  refine hpre _ _ rfl ?_
  intro h1 h2 hy1ne
  rcases Kimchi.Gate.AddComplete.sound W ha _ h1 h2 hpay hy1ne htwo with
    ⟨hinf, hsum⟩ | ⟨hinf, h3, hsum⟩
  · simp only [AddComplete.read] at hsum
    exact Or.inl ⟨hinf, hsum⟩
  · simp only [AddComplete.read] at hsum
    exact Or.inr ⟨hinf, h3, hsum⟩

/-- `addFast` is sound: under any satisfying valuation, for nonsingular operand
points with the first finite (`y ≠ 0`), the result reads as the EC group sum —
the returned point's coordinates when the flag reads `0`, the zero sum when it
reads `1`. The nonsingularity binders sit inside the promise because they are
valuation-dependent; proof irrelevance makes any instances agree. The walk shares
the mode-independent parts: seals and glue before the mode split, the tail behind
`addFastTail_spec`. -/
theorem addFast_spec [Field F] [DecidableEq F]
    (fin : Finiteness) (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0) (htwo : (2 : F) ≠ 0)
    (p1' p2' : AffinePoint (FVar F))
    (Q : PostCond (AddResult F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AddResult F) =>
        ∀ (h1 : W.Nonsingular (p1'.x.val V) (p1'.y.val V))
          (h2 : W.Nonsingular (p2'.x.val V) (p2'.y.val V)),
          p1'.y.val V ≠ 0 →
          ((r.isInfinity.toCVar.val V = 1 ∧
             Point.some _ _ h1 + Point.some _ _ h2 = 0) ∨
           (r.isInfinity.toCVar.val V = 0 ∧
             ∃ h3 : W.Nonsingular (r.p.x.val V) (r.p.y.val V),
               Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3))) Q⦄
    addFast (c := KimchiConstraint F) fin p1' p2'
    ⦃Q⦄ := by
  simp only [addFast]
  mvcgen
  rename_i s hpre
  intro p1 _ hp1x hp1y
  mvcgen
  intro p2 _ hp2x hp2y
  mvcgen
  intro sameXU _
  have hglue : ∀ (r : AddResult F) (nv' : Nat),
      (∀ (h1 : W.Nonsingular (p1.x.val s.V) (p1.y.val s.V))
         (h2 : W.Nonsingular (p2.x.val s.V) (p2.y.val s.V)),
         p1.y.val s.V ≠ 0 →
         ((r.isInfinity.toCVar.val s.V = 1 ∧
            Point.some _ _ h1 + Point.some _ _ h2 = 0) ∨
          (r.isInfinity.toCVar.val s.V = 0 ∧
            ∃ h3 : W.Nonsingular (r.p.x.val s.V) (r.p.y.val s.V),
              Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3))) →
      (Q.1 r ⟨s.V, nv'⟩).down := by
    intro r nv' hp
    refine hpre r nv' ?_
    intro h1 h2 hy1ne
    have h1' := h1
    rw [← hp1x, ← hp1y] at h1'
    have h2' := h2
    rw [← hp2x, ← hp2y] at h2'
    have hy1ne' := hy1ne
    rw [← hp1y] at hy1ne'
    rcases hp h1' h2' hy1ne' with ⟨hinf, hsum⟩ | ⟨hinf, h3, hsum⟩
    · simp only [hp1x, hp1y, hp2x, hp2y] at hsum
      exact Or.inl ⟨hinf, hsum⟩
    · simp only [hp1x, hp1y, hp2x, hp2y] at hsum
      exact Or.inr ⟨hinf, h3, hsum⟩
  cases fin with
  | checkFinite =>
    mvcgen
    exact addFastTail_spec W ha htwo p1 p2 sameXU.val false_ Q _
      (fun r nv' hp => hglue r nv' hp.2)
  | dontCheckFinite =>
    mvcgen
    intro infU _
    mvcgen
    exact addFastTail_spec W ha htwo p1 p2 sameXU.val infU.val Q _
      (fun r nv' hp => hglue r nv' hp.2)

/-- `addFast` in `checkFinite` mode is sound with the infinity branch refuted: the
returned flag is the pinned constant `0` (it reads `0`, never `1`), so under any
satisfying valuation, for nonsingular operand points with the first finite (`y ≠ 0`),
the result reads as the finite EC group sum. The pinned-mode consumers (the `endoMul`
init chain) apply this form. -/
theorem addFast_checkFinite_spec [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0) (htwo : (2 : F) ≠ 0)
    (p1' p2' : AffinePoint (FVar F))
    (Q : PostCond (AddResult F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AddResult F) =>
        ∀ (h1 : W.Nonsingular (p1'.x.val V) (p1'.y.val V))
          (h2 : W.Nonsingular (p2'.x.val V) (p2'.y.val V)),
          p1'.y.val V ≠ 0 →
          ∃ h3 : W.Nonsingular (r.p.x.val V) (r.p.y.val V),
            Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3) Q⦄
    addFast (c := KimchiConstraint F) .checkFinite p1' p2'
    ⦃Q⦄ := by
  simp only [addFast]
  mvcgen
  rename_i s hpre
  intro p1 _ hp1x hp1y
  mvcgen
  intro p2 _ hp2x hp2y
  mvcgen
  intro sameXU _
  mvcgen
  refine addFastTail_spec W ha htwo p1 p2 sameXU.val false_ Q _ ?_
  intro r nv' hrp
  obtain ⟨hrinf, hp⟩ := hrp
  refine hpre r nv' ?_
  intro h1 h2 hy1ne
  have h1' := h1
  rw [← hp1x, ← hp1y] at h1'
  have h2' := h2
  rw [← hp2x, ← hp2y] at h2'
  have hy1ne' := hy1ne
  rw [← hp1y] at hy1ne'
  rcases hp h1' h2' hy1ne' with ⟨hinf, -⟩ | ⟨-, h3, hsum⟩
  · rw [hrinf] at hinf
    exact absurd hinf (by simp [false_, BoolVar.toCVar_unchecked, CVar.val])
  · simp only [hp1x, hp1y, hp2x, hp2y] at hsum
    exact ⟨h3, hsum⟩

end AddFast

/-! ## Completeness: the honest run accepts -/

namespace AddFast

open WeierstrassCurve.Affine

/-- Reading a bit variable back through the `Bool` decode: an encoded bit decodes to
itself (the field is nontrivial). -/
private theorem readVar_bool_of_eval [Field F] [DecidableEq F]
    {v : BoolVar F} {env : Assignments F} {b : Bool}
    (h : (↑v : CVar F).eval env = .ok (bit b)) :
    readVar (val := Bool) v env = .ok b := by
  cases b with
  | false =>
    simp [readVar, h, Bind.bind, Except.bind, bit, CircuitType.fieldsToValue,
      CircuitType.varToFields, Pure.pure, Except.pure]
    rfl
  | true =>
    simp [readVar, h, Bind.bind, Except.bind, bit, CircuitType.fieldsToValue,
      CircuitType.varToFields, Pure.pure, Except.pure, one_ne_zero]
    rfl

open Std.Do in
/-- The tail's honest run, from pinned operand reads: with the sealed coordinates,
`sameX`, and `inf` reading the row's operand values, and the row those values fill
satisfying the verified gate, every check accepts; the outputs read the honest
row's values on the final table. Applied manually per mode — its value arguments
are not inferable from a call site. -/
private theorem addFastTail_complete_spec [Field F] [DecidableEq F]
    (p1 p2 : AffinePoint (FVar F)) (sameX inf : BoolVar F)
    (x1v y1v x2v y2v : F) (ib : Bool)
    (hHolds : Kimchi.Gate.AddComplete.Holds
      { Kimchi.Gate.AddComplete.build true x1v y1v x2v y2v with inf := bit ib })
    (Q : PostCond (AddResult F) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env =>
          p1.x.eval env = .ok x1v ∧ p1.y.eval env = .ok y1v ∧
          p2.x.eval env = .ok x2v ∧ p2.y.eval env = .ok y2v ∧
          (↑sameX : CVar F).eval env = .ok (bit (decide (x1v = x2v))) ∧
          (↑inf : CVar F).eval env = .ok (bit ib))
        (fun _ (r : AddResult F) env' =>
          r.p.x.eval env' = .ok (Kimchi.Gate.AddComplete.build true x1v y1v x2v y2v).x3 ∧
          r.p.y.eval env' = .ok (Kimchi.Gate.AddComplete.build true x1v y1v x2v y2v).y3 ∧
          (↑r.isInfinity : CVar F).eval env' = .ok (bit ib))
        Q⦄
    addFastTail (c := KimchiProverC F) p1 p2 sameX inf
    ⦃Q⦄ := by
  simp only [addFastTail]
  mvcgen
  rename_i st hpre
  obtain ⟨⟨hp1x, hp1y, hp2x, hp2y, hsx, hinf⟩, hk⟩ := hpre
  have hinfZw : infZWit p1 p2 sameX st.env
      = .ok (if y1v = y2v then 0 else if x1v = x2v then (y2v - y1v)⁻¹ else 0) := by
    by_cases hy : y1v = y2v <;> by_cases hx : x1v = x2v <;>
      simp [infZWit, AsProver.readCVar, hp1y, hp2y, readVar_bool_of_eval hsx, hy, hx,
        Bind.bind, ReaderT.bind, Except.bind, Pure.pure, ReaderT.pure, Except.pure]
  refine ⟨by rw [hinfZw]; rfl, fun infZ st₁ hr₁ hle₁ => ?_⟩
  have hinfZ : _ = _ := hr₁ _ hinfZw
  mvcgen
  have hx21w : x21InvWit p1 p2 sameX st₁.env
      = .ok (if x1v = x2v then 0 else (x2v - x1v)⁻¹) := by
    by_cases hx : x1v = x2v <;>
      simp [x21InvWit, AsProver.readCVar, CVar.eval_le hle₁ hp1x,
        CVar.eval_le hle₁ hp2x, readVar_bool_of_eval (CVar.eval_le hle₁ hsx), hx,
        Bind.bind, ReaderT.bind, Except.bind, Pure.pure, ReaderT.pure, Except.pure]
  refine ⟨by rw [hx21w]; rfl, fun x21Inv st₂ hr₂ hle₂ => ?_⟩
  have hx21 : _ = _ := hr₂ _ hx21w
  have hle02 := hle₁.trans hle₂
  mvcgen
  have hsw : slopeWit p1 p2 sameX st₂.env
      = .ok (if x1v = x2v then 3 * x1v * x1v / (2 * y1v)
          else (y2v - y1v) / (x2v - x1v)) := by
    by_cases hx : x1v = x2v <;>
      simp [slopeWit, AsProver.readCVar, CVar.eval_le hle02 hp1x,
        CVar.eval_le hle02 hp1y, CVar.eval_le hle02 hp2x, CVar.eval_le hle02 hp2y,
        readVar_bool_of_eval (CVar.eval_le hle02 hsx), hx,
        Bind.bind, ReaderT.bind, Except.bind, Pure.pure, ReaderT.pure, Except.pure]
  refine ⟨by rw [hsw]; rfl, fun s st₃ hr₃ hle₃ => ?_⟩
  have hs : _ = _ := hr₃ _ hsw
  have hle03 := hle02.trans hle₃
  mvcgen
  have hx3w : x3Wit p1 p2 s st₃.env
      = .ok ((if x1v = x2v then 3 * x1v * x1v / (2 * y1v)
            else (y2v - y1v) / (x2v - x1v)) *
          (if x1v = x2v then 3 * x1v * x1v / (2 * y1v)
            else (y2v - y1v) / (x2v - x1v)) - (x1v + x2v)) := by
    simp [x3Wit, AsProver.readCVar, hs, CVar.eval_le hle03 hp1x,
      CVar.eval_le hle03 hp2x,
      Bind.bind, ReaderT.bind, Except.bind, Pure.pure, ReaderT.pure, Except.pure]
  refine ⟨by rw [hx3w]; rfl, fun x3 st₄ hr₄ hle₄ => ?_⟩
  have hx3 : _ = _ := hr₄ _ hx3w
  have hle04 := hle03.trans hle₄
  mvcgen
  have hy3w : y3Wit p1 s x3 st₄.env
      = .ok ((if x1v = x2v then 3 * x1v * x1v / (2 * y1v)
            else (y2v - y1v) / (x2v - x1v)) *
          (x1v -
            ((if x1v = x2v then 3 * x1v * x1v / (2 * y1v)
              else (y2v - y1v) / (x2v - x1v)) *
            (if x1v = x2v then 3 * x1v * x1v / (2 * y1v)
              else (y2v - y1v) / (x2v - x1v)) - (x1v + x2v))) - y1v) := by
    simp [y3Wit, AsProver.readCVar, CVar.eval_le hle₄ hs, hx3,
      CVar.eval_le hle04 hp1x, CVar.eval_le hle04 hp1y,
      Bind.bind, ReaderT.bind, Except.bind, Pure.pure, ReaderT.pure, Except.pure]
  refine ⟨by rw [hy3w]; rfl, fun y3 st₅ hr₅ hle₅ => ?_⟩
  have hy3 : _ = _ := hr₅ _ hy3w
  have hle05 := hle04.trans hle₅
  have hle25 := hle₃.trans (hle₄.trans hle₅)
  mvcgen
  refine addConstraint_complete_spec (c := KimchiConstraint F) _ _ st₅
    ⟨?_, fun u st₆ _ hle₆ => ?_⟩
  · show KimchiConstraint.check (.addComplete _) st₅.env = true
    have heval : AddComplete.eval st₅.env
        ⟨p1, p2, ⟨x3, y3⟩, inf.toCVar, sameX.toCVar, s, infZ, x21Inv⟩
        = .ok { Kimchi.Gate.AddComplete.build true x1v y1v x2v y2v with inf := bit ib } := by
      simp [AddComplete.eval, Kimchi.Gate.AddComplete.build, bit,
        CVar.eval_le hle05 hp1x, CVar.eval_le hle05 hp1y,
        CVar.eval_le hle05 hp2x, CVar.eval_le hle05 hp2y,
        CVar.eval_le hle₅ hx3, hy3, CVar.eval_le (hle₄.trans hle₅) hs,
        CVar.eval_le (hle₂.trans hle25) hinfZ, CVar.eval_le hle25 hx21,
        CVar.eval_le hle05 hinf, CVar.eval_le hle05 hsx,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    simp only [KimchiConstraint.check, heval]
    exact (Kimchi.Gate.AddComplete.ok_iff _).mpr hHolds
  · mvcgen
    refine hk _ st₆ ?_ ?_ ?_ (hle05.trans hle₆)
    · exact CVar.eval_le (hle₅.trans hle₆) hx3
    · exact CVar.eval_le hle₆ hy3
    · exact CVar.eval_le (hle05.trans hle₆) hinf

/-- `addFast`'s honest run succeeds at the prover carrier: with the four operand
coordinates readable, the operands nonsingular (short shape), the first finite
(`y ≠ 0`), and — under `checkFinite` — the group sum nonzero, the checking
interpreter at `KimchiProverC` accepts every row the gadget emits, and the outputs
read as the sum
in Mathlib's group — *either* the infinity flag reads `1` and the sum is `0`, *or*
it reads `0` and the output coordinates are a nonsingular point equal to the sum
(the accepted row satisfies the verified gate, so its `sound` characterizes what
was computed). The executable seam (`kimchiSolve` at `kimchiOps`) is outside this
statement: its ops-coherence lockstep is the open obligation
`Snarky.Kimchi.Constraint` records. -/
theorem addFast_complete_spec [Field F] [DecidableEq F]
    (fin : Finiteness) (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0) (htwo : (2 : F) ≠ 0)
    (p1' p2' : AffinePoint (FVar F))
    (Q : PostCond (AddResult F) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env =>
          (p1'.x.eval env).isOk ∧ (p1'.y.eval env).isOk ∧
          (p2'.x.eval env).isOk ∧ (p2'.y.eval env).isOk ∧
          (∀ x1 y1 x2 y2, p1'.x.eval env = .ok x1 → p1'.y.eval env = .ok y1 →
            p2'.x.eval env = .ok x2 → p2'.y.eval env = .ok y2 →
            ∃ (h1 : W.Nonsingular x1 y1) (h2 : W.Nonsingular x2 y2),
              y1 ≠ 0 ∧ (fin = .checkFinite →
                Point.some _ _ h1 + Point.some _ _ h2 ≠ 0)))
        (fun env (r : AddResult F) env' =>
          ∀ x1 y1 x2 y2, p1'.x.eval env = .ok x1 → p1'.y.eval env = .ok y1 →
            p2'.x.eval env = .ok x2 → p2'.y.eval env = .ok y2 →
            ∀ (h1 : W.Nonsingular x1 y1) (h2 : W.Nonsingular x2 y2),
              ((↑r.isInfinity : CVar F).eval env' = .ok 1 ∧
                Point.some _ _ h1 + Point.some _ _ h2 = 0) ∨
              (∃ x3 y3, r.p.x.eval env' = .ok x3 ∧ r.p.y.eval env' = .ok y3 ∧
                (↑r.isInfinity : CVar F).eval env' = .ok 0 ∧
                ∃ h3 : W.Nonsingular x3 y3,
                  Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3))
        Q⦄
    addFast (c := KimchiProverC F) fin p1' p2'
    ⦃Q⦄ := by
  simp only [addFast]
  mvcgen
  rename_i st hpre
  obtain ⟨⟨hx1ok, hy1ok, hx2ok, hy2ok, hcond⟩, hk⟩ := hpre
  obtain ⟨x1v, hx1⟩ := CVar.evalOk hx1ok
  obtain ⟨y1v, hy1⟩ := CVar.evalOk hy1ok
  obtain ⟨x2v, hx2⟩ := CVar.evalOk hx2ok
  obtain ⟨y2v, hy2⟩ := CVar.evalOk hy2ok
  obtain ⟨h1n, h2n, hy1ne, hsumne⟩ := hcond _ _ _ _ hx1 hy1 hx2 hy2
  have hon1 := h1n.1
  have hon2 := h2n.1
  have hfin : fin = .checkFinite → ¬(x1v = x2v ∧ y1v = W.negY x2v y2v) := by
    intro hf
    rintro ⟨rfl, hyeq⟩
    subst hyeq
    apply hsumne hf
    rw [show Point.some x1v (W.negY x1v y2v) h1n = -Point.some x1v y2v h2n from by
      rw [WeierstrassCurve.Affine.Point.neg_some]]
    exact neg_add_cancel _
  refine ⟨⟨hx1ok, hy1ok⟩, fun p1 st₁ hp1 hle₁ => ?_⟩
  obtain ⟨hp1x, hp1y⟩ := hp1 _ _ hx1 hy1
  mvcgen
  refine ⟨⟨by rw [CVar.eval_le hle₁ hx2]; rfl, by rw [CVar.eval_le hle₁ hy2]; rfl⟩,
    fun p2 st₂ hp2 hle₂ => ?_⟩
  obtain ⟨hp2x, hp2y⟩ := hp2 _ _ (CVar.eval_le hle₁ hx2) (CVar.eval_le hle₁ hy2)
  mvcgen
  have hsw : (UnChecked.mk <$> sameXWit p1 p2) st₂.env
      = .ok ⟨decide (x1v = x2v)⟩ := by
    simp [sameXWit, AsProver.readCVar, CVar.eval_le hle₂ hp1x, hp2x,
      Functor.map, Bind.bind, ReaderT.bind, Except.bind, Except.map,
      Pure.pure, ReaderT.pure, Except.pure]
  refine ⟨by rw [hsw]; rfl, fun sameXU st₃ hsxr hle₃ => ?_⟩
  have hsx : _ = _ := hsxr _ hsw
  cases fin with
  | checkFinite =>
    mvcgen
    have hHolds := Kimchi.Gate.AddComplete.complete_build (checkFinite := true) W ha
      hon1 hon2 hy1ne htwo (fun _ => hfin)
    refine addFastTail_complete_spec p1 p2 sameXU.val false_ x1v y1v x2v y2v false
      hHolds Q st₃
      ⟨⟨CVar.eval_le (hle₂.trans hle₃) hp1x, CVar.eval_le (hle₂.trans hle₃) hp1y,
        CVar.eval_le hle₃ hp2x, CVar.eval_le hle₃ hp2y, hsx, rfl⟩,
      fun r st' hpost hle => hk r st' ?_
        ((hle₁.trans (hle₂.trans hle₃)).trans hle)⟩
    intro a1 b1 a2 b2 ha1 hb1 ha2 hb2 h1 h2
    rw [hx1] at ha1; rw [hy1] at hb1; rw [hx2] at ha2; rw [hy2] at hb2
    injection ha1 with ha1; injection hb1 with hb1
    injection ha2 with ha2; injection hb2 with hb2
    subst ha1 hb1 ha2 hb2
    rcases Kimchi.Gate.AddComplete.sound W ha _ h1 h2 hHolds hy1ne htwo with
      ⟨hinf1, _⟩ | ⟨_, h3, hsum⟩
    · exact absurd (hinf1 : (0 : F) = 1) zero_ne_one
    · exact Or.inr ⟨_, _, hpost.1, hpost.2.1, hpost.2.2, h3, hsum⟩
  | dontCheckFinite =>
    mvcgen
    have hiw : (UnChecked.mk <$> infWit p1 p2 sameXU.val) st₃.env
        = .ok ⟨decide (x1v = x2v) && !decide (y1v = y2v)⟩ := by
      simp [infWit, AsProver.readCVar, readVar_bool_of_eval hsx,
        CVar.eval_le (hle₂.trans hle₃) hp1y, CVar.eval_le hle₃ hp2y,
        Functor.map, Bind.bind, ReaderT.bind, Except.bind, Except.map,
        Pure.pure, ReaderT.pure, Except.pure]
    refine ⟨by rw [hiw]; rfl, fun infU st₄ hinfr hle₄ => ?_⟩
    have hinfb : _ = _ := hinfr _ hiw
    mvcgen
    have hHolds := Kimchi.Gate.AddComplete.complete_build (checkFinite := false) W ha
      hon1 hon2 hy1ne htwo (fun h => Bool.noConfusion h)
    refine addFastTail_complete_spec p1 p2 sameXU.val infU.val x1v y1v x2v y2v
      (decide (x1v = x2v) && !decide (y1v = y2v))
      hHolds Q st₄
      ⟨⟨CVar.eval_le (hle₂.trans (hle₃.trans hle₄)) hp1x,
        CVar.eval_le (hle₂.trans (hle₃.trans hle₄)) hp1y,
        CVar.eval_le (hle₃.trans hle₄) hp2x, CVar.eval_le (hle₃.trans hle₄) hp2y,
        CVar.eval_le hle₄ hsx, hinfb⟩,
      fun r st' hpost hle => hk r st' ?_
        ((hle₁.trans (hle₂.trans (hle₃.trans hle₄))).trans hle)⟩
    intro a1 b1 a2 b2 ha1 hb1 ha2 hb2 h1 h2
    rw [hx1] at ha1; rw [hy1] at hb1; rw [hx2] at ha2; rw [hy2] at hb2
    injection ha1 with ha1; injection hb1 with hb1
    injection ha2 with ha2; injection hb2 with hb2
    subst ha1 hb1 ha2 hb2
    rcases Kimchi.Gate.AddComplete.sound W ha _ h1 h2 hHolds hy1ne htwo with
      ⟨hinf1, hsum⟩ | ⟨hinf0, h3, hsum⟩
    · exact Or.inl ⟨hinf1 ▸ hpost.2.2, hsum⟩
    · exact Or.inr ⟨_, _, hpost.1, hpost.2.1, hinf0 ▸ hpost.2.2, h3, hsum⟩

open WeierstrassCurve.Affine in
/-- The negated operand's reading, on a short curve: `(x, −y)` is nonsingular and is
the group negation — the face a subtracting caller consumes. -/
theorem neg_point_reading [Field F] (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0) {xv yv : F} (hT : W.Nonsingular xv yv) :
    ∃ hn : W.Nonsingular xv (-yv),
      (Point.some _ _ hn : W.Point) = -Point.some _ _ hT := by
  have hy : W.negY xv yv = -yv := by
    rw [WeierstrassCurve.Affine.negY, ha.1, ha.2.2]
    ring
  have hn : W.Nonsingular xv (-yv) := hy ▸ (W.nonsingular_neg xv yv).mpr hT
  refine ⟨hn, ?_⟩
  rw [WeierstrassCurve.Affine.Point.neg_some]
  simp only [hy]

end AddFast
-/

end Snarky.Kimchi
