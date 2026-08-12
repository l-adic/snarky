import Snarky.Circuit.DSL.Utils
import Snarky.Kimchi.Semantics
import Kimchi.Gate.Semantics.AddComplete

/-!
# The complete-addition gadget

Port of `Snarky.Circuit.Kimchi.AddComplete`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/AddComplete.purs): `addFast` seals
the two operand points, witnesses the gate's seven auxiliary columns in allocation
order (`sameX`, the mode-dependent `inf`, `infZ`, `x21Inv`, `s`, `x3`, `y3` — fixture
bytes), and emits one `KimchiConstraint.addComplete`. `addComplete` is the
`checkFinite` specialization (OCaml `add_fast` with its default).

Name map: `sealPoint`, `Finiteness` (constructors lowerCamel), `addFast`,
`addComplete` keep their names; the result record is `AddResult`; the witness
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
honest run accepts on-curve operands — the witness computations fill the row the
gate's completeness algebra certifies).
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

/-- A point's coordinates carry no check of their own (PS `genericCheck`). -/
instance : CheckedType F c (AffinePoint (FVar F)) where
  check _ := .pure PUnit.unit

/-- Seal a point coordinatewise, `y` before `x` — OCaml's `seal` maps over the tuple
right to left (PS `sealPoint` preserves the order; emission order is fixture bytes). -/
private def sealPoint [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
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

/-- `addFast`'s result: the output point and the (mode-dependent) infinity flag. -/
structure AddResult (F : Type) where
  /-- The output sum. -/
  p : AffinePoint (FVar F)
  /-- The infinity flag: constant `false` under `checkFinite`, else witnessed. -/
  isInfinity : BoolVar F

namespace AddFast

/-- `sameX`'s witness: whether the operand x-coordinates coincide. Public only for
the gadget laws. -/
private def sameXWit [Add F] [Mul F] [DecidableEq F] (p1 p2 : AffinePoint (FVar F)) :
    AsProver F Bool := do
  let x1 ← AsProver.readCVar p1.x
  let x2 ← AsProver.readCVar p2.x
  pure (decide (x1 = x2))

/-- `inf`'s witness (`dontCheckFinite` mode): same x-coordinates with different
y-coordinates — the inverse-pair test. Public only for the gadget laws. -/
private def infWit [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    (p1 p2 : AffinePoint (FVar F)) (sameX : BoolVar F) : AsProver F Bool := do
  let sx ← readVar (val := Bool) sameX
  let y1 ← AsProver.readCVar p1.y
  let y2 ← AsProver.readCVar p2.y
  pure (sx && !(decide (y1 = y2)))

/-- `infZ`'s witness: `0` on equal y-coordinates, else the inverse of `y₂ − y₁` when
the x-coordinates coincide (pinning the infinity flag), else `0`. Public only for the
gadget laws. -/
private def infZWit [Field F] [DecidableEq F] (p1 p2 : AffinePoint (FVar F))
    (sameX : BoolVar F) : AsProver F F := do
  let y1 ← AsProver.readCVar p1.y
  let y2 ← AsProver.readCVar p2.y
  if y1 = y2 then pure 0
  else do
    let sx ← readVar (val := Bool) sameX
    if sx then pure (y2 - y1)⁻¹ else pure 0

/-- `x21Inv`'s witness: the inverse of `x₂ − x₁` when the x-coordinates differ
(pinning `sameX`), else `0`. Public only for the gadget laws. -/
private def x21InvWit [Field F] [DecidableEq F] (p1 p2 : AffinePoint (FVar F))
    (sameX : BoolVar F) : AsProver F F := do
  let sx ← readVar (val := Bool) sameX
  if sx then pure 0
  else do
    let x1 ← AsProver.readCVar p1.x
    let x2 ← AsProver.readCVar p2.x
    pure (x2 - x1)⁻¹

/-- The slope's witness: tangent `3x₁²/(2y₁)` in the equal-x case, else the secant
`(y₂−y₁)/(x₂−x₁)`. Public only for the gadget laws. -/
private def slopeWit [Field F] [DecidableEq F] (p1 p2 : AffinePoint (FVar F))
    (sameX : BoolVar F) : AsProver F F := do
  let sx ← readVar (val := Bool) sameX
  if sx then do
    let x1 ← AsProver.readCVar p1.x
    let y1 ← AsProver.readCVar p1.y
    pure (3 * x1 * x1 / (2 * y1))
  else do
    let y1 ← AsProver.readCVar p1.y
    let y2 ← AsProver.readCVar p2.y
    let x1 ← AsProver.readCVar p1.x
    let x2 ← AsProver.readCVar p2.x
    pure ((y2 - y1) / (x2 - x1))

/-- `x3`'s witness: `s² − (x₁ + x₂)`. Public only for the gadget laws. -/
private def x3Wit [Add F] [Mul F] [Sub F] (p1 p2 : AffinePoint (FVar F)) (s : FVar F) :
    AsProver F F := do
  let sv ← AsProver.readCVar s
  let x1 ← AsProver.readCVar p1.x
  let x2 ← AsProver.readCVar p2.x
  pure (sv * sv - (x1 + x2))

/-- `y3`'s witness: `s·(x₁ − x₃) − y₁`. Public only for the gadget laws. -/
private def y3Wit [Add F] [Mul F] [Sub F] (p1 : AffinePoint (FVar F)) (s x3 : FVar F) :
    AsProver F F := do
  let sv ← AsProver.readCVar s
  let x1 ← AsProver.readCVar p1.x
  let x3v ← AsProver.readCVar x3
  let y1 ← AsProver.readCVar p1.y
  pure (sv * (x1 - x3v) - y1)

end AddFast

/-- The mode-independent suffix of `addFast`: witness the five auxiliary columns and
emit the one `addComplete` constraint. -/
def addFastTail [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c]
    (p1 p2 : AffinePoint (FVar F)) (sameX inf : BoolVar F) :
    CircuitM F c (AddResult F) := do
  let infZ ← witness (val := F) (AddFast.infZWit p1 p2 sameX)
  let x21Inv ← witness (val := F) (AddFast.x21InvWit p1 p2 sameX)
  let s ← witness (val := F) (AddFast.slopeWit p1 p2 sameX)
  let x3 ← witness (val := F) (AddFast.x3Wit p1 p2 s)
  let y3 ← witness (val := F) (AddFast.y3Wit p1 s x3)
  addConstraint (KimchiSystem.addComplete
    { p1 := p1, p2 := p2, p3 := ⟨x3, y3⟩, inf := inf.toCVar,
      sameX := sameX.toCVar, s := s, infZ := infZ, x21Inv := x21Inv })
  pure ⟨⟨x3, y3⟩, inf⟩

/-- Complete addition with explicit finiteness control (OCaml
`add_fast ~check_finite`): seal both points, witness the gate's auxiliary columns in
allocation order, emit one `addComplete` constraint. -/
def addFast [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c]
    (finiteness : Finiteness) (p1' p2' : AffinePoint (FVar F)) :
    CircuitM F c (AddResult F) := do
  let p1 ← sealPoint p1'
  let p2 ← sealPoint p2'
  let sameXU ← witness (val := UnChecked Bool) (.mk <$> AddFast.sameXWit p1 p2)
  let sameX := sameXU.val
  let inf ← match finiteness with
    | .checkFinite => pure false_
    | .dontCheckFinite => do
      let r ← witness (val := UnChecked Bool) (.mk <$> AddFast.infWit p1 p2 sameX)
      pure r.val
  addFastTail p1 p2 sameX inf

/-- Complete addition assuming finite inputs (OCaml `add_fast`'s default mode). -/
def addComplete [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c]
    (p1 p2 : AffinePoint (FVar F)) : CircuitM F c (AddResult F) :=
  addFast .checkFinite p1 p2

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
result as the group sum, via the verified gate's `sound`. Applied manually per mode —
the curve parameters appear only in the promise, so a registry application could not
infer them. -/
private theorem addFastTail_spec [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0) (htwo : (2 : F) ≠ 0)
    (p1 p2 : AffinePoint (FVar F)) (sameX inf : BoolVar F)
    (Q : PostCond (AddResult F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AddResult F) =>
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
  refine hpre _ _ ?_
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
    exact addFastTail_spec W ha htwo p1 p2 sameXU.val false_ Q _ hglue
  | dontCheckFinite =>
    mvcgen
    intro infU _
    mvcgen
    exact addFastTail_spec W ha htwo p1 p2 sameXU.val infU.val Q _ hglue

end AddFast

/-! ## Completeness: the honest run accepts -/

namespace AddFast

/-- The value all seven witness computations jointly produce, as one pure function of
the (sealed) operand coordinates: the row the honest prover fills. `checkFinite` pins
`inf` to `0`; otherwise `inf` is the inverse-pair test. -/
private def valueWitness [Field F] [DecidableEq F] (checkFinite : Bool)
    (x1 y1 x2 y2 : F) : Kimchi.Gate.AddComplete.Witness F :=
  let s : F := if x1 = x2 then 3 * x1 * x1 / (2 * y1) else (y2 - y1) / (x2 - x1)
  let x3 : F := s * s - (x1 + x2)
  { x1 := x1, y1 := y1, x2 := x2, y2 := y2
    x3 := x3
    y3 := s * (x1 - x3) - y1
    inf := if checkFinite then 0 else bit (decide (x1 = x2) && !decide (y1 = y2))
    sameX := bit (decide (x1 = x2))
    s := s
    infZ := if y1 = y2 then 0 else if x1 = x2 then (y2 - y1)⁻¹ else 0
    x21Inv := if x1 = x2 then 0 else (x2 - x1)⁻¹ }

/-- The honest witness satisfies the verified gate: for on-curve operands on a
short-shape curve — `checkFinite` mode adding the finite-sum precondition — the row
`addFast` computes meets `Kimchi.Gate.AddComplete.Holds`. The proof replays the
algebra of the gate's `complete_noninf`/`complete_inf` at the gadget's computed
values (those theorems pin an existential witness, not this one). -/
private theorem valueWitness_holds [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    {checkFinite : Bool} {x1 y1 x2 y2 : F}
    (hon1 : W.Equation x1 y1) (hon2 : W.Equation x2 y2)
    (hy1 : y1 ≠ 0) (h2 : (2 : F) ≠ 0)
    (hfin : checkFinite = true → ¬(x1 = x2 ∧ y1 = W.negY x2 y2)) :
    Kimchi.Gate.AddComplete.Holds (valueWitness checkFinite x1 y1 x2 y2) := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  have hcancel := mul_inv_cancel₀ (mul_ne_zero h2 hy1)
  rw [Kimchi.Gate.AddComplete.holds_iff]
  by_cases hx : x1 = x2
  · -- Equal x-coordinates: on-curve, the y-coordinates agree or are opposite.
    have hyy : (y1 - y2) * (y1 + y2) = 0 := by
      rw [WeierstrassCurve.Affine.equation_iff] at hon1 hon2
      rw [ha1, ha2, ha3, ha4] at hon1 hon2
      rw [hx] at hon1
      linear_combination hon1 - hon2
    by_cases hy : y1 = y2
    · -- Doubling: `inf = 0` in both modes, `infZ = 0`.
      simp only [valueWitness, if_pos hx, if_pos hy, decide_eq_true hx,
        decide_eq_true hy, Bool.not_true, Bool.and_false, bit, Bool.false_eq_true,
        if_false, if_true, ite_self]
      refine ⟨by ring, by linear_combination -hx, ?_, by ring, by ring, ?_, by ring⟩
      · linear_combination (3 * x1 * x1) * hcancel
      · linear_combination -hy
    · -- Inverse pair: `y₂ = −y₁`; excluded under `checkFinite`, else `inf = 1`.
      have hy2 : y2 = -y1 := by
        rcases mul_eq_zero.mp hyy with h | h
        · exact absurd (by linear_combination h) hy
        · linear_combination h
      have hne : y2 - y1 ≠ 0 := by
        rw [hy2]
        intro h
        rcases mul_eq_zero.mp (show y1 * 2 = 0 by linear_combination -h) with h' | h'
        · exact hy1 h'
        · exact h2 h'
      cases checkFinite with
      | true =>
        exact absurd ⟨hx, by rw [WeierstrassCurve.Affine.negY, ha1, ha3, hy2]; ring⟩
          (hfin rfl)
      | false =>
        simp only [valueWitness, if_pos hx, if_neg hy, decide_eq_true hx,
          decide_eq_false hy, Bool.not_false, Bool.and_true, bit,
          Bool.false_eq_true, if_false, if_true]
        refine ⟨by ring, by linear_combination -hx, ?_, by ring, by ring, by ring, ?_⟩
        · linear_combination (3 * x1 * x1) * hcancel
        · linear_combination mul_inv_cancel₀ hne
  · -- Distinct x-coordinates: the secant row; `inf = 0` in both modes.
    have hne : x2 - x1 ≠ 0 := fun h => hx (by linear_combination -h)
    simp only [valueWitness, if_neg hx, decide_eq_false hx, Bool.false_and, bit,
      Bool.false_eq_true, if_false, ite_self]
    refine ⟨?_, by ring, ?_, by ring, by ring, by ring, by ring⟩
    · linear_combination mul_inv_cancel₀ hne
    · linear_combination (y2 - y1) * mul_inv_cancel₀ hne

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
satisfying the verified gate, every check accepts; the outputs read on the final
table. Applied manually per mode — its value arguments are not inferable from a call
site. -/
private theorem addFastTail_complete_spec [Field F] [DecidableEq F]
    (p1 p2 : AffinePoint (FVar F)) (sameX inf : BoolVar F)
    (x1v y1v x2v y2v : F) (ib : Bool)
    (hHolds : Kimchi.Gate.AddComplete.Holds
      { valueWitness true x1v y1v x2v y2v with inf := bit ib })
    (Q : PostCond (AddResult F) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env =>
          p1.x.eval env = .ok x1v ∧ p1.y.eval env = .ok y1v ∧
          p2.x.eval env = .ok x2v ∧ p2.y.eval env = .ok y2v ∧
          (↑sameX : CVar F).eval env = .ok (bit (decide (x1v = x2v))) ∧
          (↑inf : CVar F).eval env = .ok (bit ib))
        (fun _ (r : AddResult F) env' =>
          (r.p.x.eval env').isOk ∧ (r.p.y.eval env').isOk ∧
          ((↑r.isInfinity : CVar F).eval env').isOk)
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
  have hinfZ := hr₁ _ hinfZw
  mvcgen
  have hx21w : x21InvWit p1 p2 sameX st₁.env
      = .ok (if x1v = x2v then 0 else (x2v - x1v)⁻¹) := by
    by_cases hx : x1v = x2v <;>
      simp [x21InvWit, AsProver.readCVar, CVar.eval_le hle₁ hp1x,
        CVar.eval_le hle₁ hp2x, readVar_bool_of_eval (CVar.eval_le hle₁ hsx), hx,
        Bind.bind, ReaderT.bind, Except.bind, Pure.pure, ReaderT.pure, Except.pure]
  refine ⟨by rw [hx21w]; rfl, fun x21Inv st₂ hr₂ hle₂ => ?_⟩
  have hx21 := hr₂ _ hx21w
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
  have hs := hr₃ _ hsw
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
  have hx3 := hr₄ _ hx3w
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
  have hy3 := hr₅ _ hy3w
  have hle05 := hle04.trans hle₅
  have hle25 := hle₃.trans (hle₄.trans hle₅)
  mvcgen
  refine addConstraint_complete_spec (c := KimchiConstraint F) _ _ st₅
    ⟨?_, fun u st₆ _ hle₆ => ?_⟩
  · show KimchiConstraint.check (.addComplete _) st₅.env = true
    have heval : AddComplete.eval st₅.env
        ⟨p1, p2, ⟨x3, y3⟩, inf.toCVar, sameX.toCVar, s, infZ, x21Inv⟩
        = .ok { valueWitness true x1v y1v x2v y2v with inf := bit ib } := by
      simp [AddComplete.eval, valueWitness,
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
    · rw [CVar.eval_le (hle₅.trans hle₆) hx3]; rfl
    · rw [CVar.eval_le hle₆ hy3]; rfl
    · rw [CVar.eval_le (hle05.trans hle₆) hinf]; rfl

/-- `addFast`'s honest run succeeds: with the four operand coordinates readable, the
operands on-curve (short shape), the first finite (`y ≠ 0`), and — under
`checkFinite` — the sum finite, the prover accepts every row the gadget emits. The
grant is the outputs reading on the final table. -/
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
            W.Equation x1 y1 ∧ W.Equation x2 y2 ∧ y1 ≠ 0 ∧
              (fin = .checkFinite → ¬(x1 = x2 ∧ y1 = W.negY x2 y2))))
        (fun _ (r : AddResult F) env' =>
          (r.p.x.eval env').isOk ∧ (r.p.y.eval env').isOk ∧
          ((↑r.isInfinity : CVar F).eval env').isOk)
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
  obtain ⟨hon1, hon2, hy1ne, hfin⟩ := hcond _ _ _ _ hx1 hy1 hx2 hy2
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
  have hsx := hsxr _ hsw
  cases fin with
  | checkFinite =>
    mvcgen
    refine addFastTail_complete_spec p1 p2 sameXU.val false_ x1v y1v x2v y2v false
      (valueWitness_holds (checkFinite := true) W ha hon1 hon2 hy1ne htwo
        (fun _ => hfin)) Q st₃
      ⟨⟨CVar.eval_le (hle₂.trans hle₃) hp1x, CVar.eval_le (hle₂.trans hle₃) hp1y,
        CVar.eval_le hle₃ hp2x, CVar.eval_le hle₃ hp2y, hsx, rfl⟩,
      fun r st' hpost hle => hk r st' hpost.1 hpost.2.1 hpost.2.2
        ((hle₁.trans (hle₂.trans hle₃)).trans hle)⟩
  | dontCheckFinite =>
    mvcgen
    have hiw : (UnChecked.mk <$> infWit p1 p2 sameXU.val) st₃.env
        = .ok ⟨decide (x1v = x2v) && !decide (y1v = y2v)⟩ := by
      simp [infWit, AsProver.readCVar, readVar_bool_of_eval hsx,
        CVar.eval_le (hle₂.trans hle₃) hp1y, CVar.eval_le hle₃ hp2y,
        Functor.map, Bind.bind, ReaderT.bind, Except.bind, Except.map,
        Pure.pure, ReaderT.pure, Except.pure]
    refine ⟨by rw [hiw]; rfl, fun infU st₄ hinfr hle₄ => ?_⟩
    have hinfb := hinfr _ hiw
    mvcgen
    refine addFastTail_complete_spec p1 p2 sameXU.val infU.val x1v y1v x2v y2v
      (decide (x1v = x2v) && !decide (y1v = y2v))
      (valueWitness_holds (checkFinite := false) W ha hon1 hon2 hy1ne htwo
        (fun h => Bool.noConfusion h)) Q st₄
      ⟨⟨CVar.eval_le (hle₂.trans (hle₃.trans hle₄)) hp1x,
        CVar.eval_le (hle₂.trans (hle₃.trans hle₄)) hp1y,
        CVar.eval_le (hle₃.trans hle₄) hp2x, CVar.eval_le (hle₃.trans hle₄) hp2y,
        CVar.eval_le hle₄ hsx, hinfb⟩,
      fun r st' hpost hle => hk r st' hpost.1 hpost.2.1 hpost.2.2
        ((hle₁.trans (hle₂.trans (hle₃.trans hle₄))).trans hle)⟩

end AddFast

end Snarky.Kimchi
