import Snarky.Circuit.DSL.Utils
import Snarky.Kimchi.Circuit.Curve
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
honest `KimchiProverC` run accepts on-curve operands — the witness computations fill
the row the gate's completeness algebra certifies). `addFast_checkFinite_spec` is
the pinned-mode soundness form: the flag is the constant `0`, so the sum reads as
the finite branch with no disjunction.
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- A point's coordinates carry no check of their own (PS `genericCheck`). -/
instance : CheckedType F c (AffinePoint (FVar F)) where
  check _ := .pure PUnit.unit

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
@[spec] private theorem sealPoint_spec {V : Valuation F} [Field F] [DecidableEq F]
    (q : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄
    sealPoint (c := Builder V (KimchiConstraint F)) q
    ⦃⇓ r _ => ⌜r.x.val V = q.x.val V ∧ r.y.val V = q.y.val V⌝⦄ := by
  simp only [sealPoint]
  mvcgen

/-- The state and result of `sealPoint`'s honest run: `y`'s seal, then `x`'s. -/
def sealPointRun [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] (st : ProverState F)
    (p : AffinePoint (FVar F)) : ProverState F × AffinePoint (FVar F) :=
  let ry := sealRun st p.y
  let rx := sealRun ry.1 p.x
  (rx.1, ⟨rx.2, ry.2⟩)

/-- `sealPoint`'s honest run on an in-scope point lands at `sealPointRun`. -/
theorem sealPoint_run [CommSemiring F] [DecidableEq F] [BasicSystem F c] [Checker F c]
    [LawfulChecker F c] {p : AffinePoint (FVar F)} (st : ProverState F) (hx : p.x.Scoped st)
    (hy : p.y.Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (sealPoint (c := c) p) st.nv st.env
      = .ok ((sealPointRun st p).1.out (sealPointRun st p).2) := by
  have hg := sealRun_grants (st := st) hy
  simp only [sealPoint, sealPointRun, prove_bind, sealVar_run st hy, Except.bind,
    sealVar_run _ (hx.of_le hg.le)]
  rfl

/-- `sealPointRun` reads as the point, coordinate by coordinate. -/
theorem sealPointRun_grants [CommSemiring F] [DecidableEq F] {st : ProverState F}
    {p : AffinePoint (FVar F)} (hx : p.x.Scoped st) (hy : p.y.Scoped st) :
    Grants F st ((sealPointRun st p).1, (sealPointRun st p).2.x) (p.x.val st.env.toValuation) ∧
      Grants F st ((sealPointRun st p).1, (sealPointRun st p).2.y)
        (p.y.val st.env.toValuation) := by
  have hgy := sealRun_grants (st := st) hy
  have hgx := sealRun_grants (st := (sealRun st p.y).1) (hx.of_le hgy.le)
  simp only [sealPointRun]
  exact ⟨Grants.fvar (hgy.le.trans hgx.le) hgx.fvar_scoped
      (by rw [hgx.fvar_val, CVar.val_of_le hgy.le hx]),
    Grants.fvar (hgy.le.trans hgx.le) (hgy.fvar_scoped.of_le hgx.le)
      (by rw [CVar.val_of_le hgx.le hgy.fvar_scoped, hgy.fvar_val])⟩

namespace AddFast

open WeierstrassCurve.Affine

/-- The tail's soundness, at the sealed operands: any satisfying valuation reads the
result as the group sum, via the verified gate's `sound`; the returned flag is the
`inf` argument itself (structural — how the `checkFinite` mode pins the finite
branch). Applied manually per mode — the curve parameters appear only in the promise,
so a registry application could not infer them. -/
private theorem addFastTail_spec {V : Valuation F} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0) (htwo : (2 : F) ≠ 0)
    (p1 p2 : AffinePoint (FVar F)) (sameX inf : BoolVar F) :
    ⦃⌜True⌝⦄
    addFastTail (c := Builder V (KimchiConstraint F)) p1 p2 sameX inf
    ⦃⇓ r _ => ⌜r.isInfinity = inf ∧
        ∀ (h1 : W.Nonsingular (p1.x.val V) (p1.y.val V))
          (h2 : W.Nonsingular (p2.x.val V) (p2.y.val V)),
          p1.y.val V ≠ 0 →
          ((r.isInfinity.toCVar.val V = 1 ∧
             Point.some _ _ h1 + Point.some _ _ h2 = 0) ∨
           (r.isInfinity.toCVar.val V = 0 ∧
             ∃ h3 : W.Nonsingular (r.p.x.val V) (r.p.y.val V),
               Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3))⌝⦄ := by
  simp only [addFastTail]
  mvcgen
  rename_i hpay
  refine ⟨by first | rfl | trivial, fun h1 h2 hy1ne => ?_⟩
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
theorem addFast_spec {V : Valuation F} [Field F] [DecidableEq F]
    (fin : Finiteness) (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0) (htwo : (2 : F) ≠ 0)
    (p1' p2' : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄
    addFast (c := Builder V (KimchiConstraint F)) fin p1' p2'
    ⦃⇓ r _ => ⌜∀ (h1 : W.Nonsingular (p1'.x.val V) (p1'.y.val V))
          (h2 : W.Nonsingular (p2'.x.val V) (p2'.y.val V)),
          p1'.y.val V ≠ 0 →
          ((r.isInfinity.toCVar.val V = 1 ∧
             Point.some _ _ h1 + Point.some _ _ h2 = 0) ∨
           (r.isInfinity.toCVar.val V = 0 ∧
             ∃ h3 : W.Nonsingular (r.p.x.val V) (r.p.y.val V),
               Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3))⌝⦄ := by
  have hglue : ∀ (p1 p2 : AffinePoint (FVar F)) (r : AddResult F),
      p1.x.val V = p1'.x.val V → p1.y.val V = p1'.y.val V →
      p2.x.val V = p2'.x.val V → p2.y.val V = p2'.y.val V →
      (∀ (h1 : W.Nonsingular (p1.x.val V) (p1.y.val V))
         (h2 : W.Nonsingular (p2.x.val V) (p2.y.val V)),
         p1.y.val V ≠ 0 →
         ((r.isInfinity.toCVar.val V = 1 ∧
            Point.some _ _ h1 + Point.some _ _ h2 = 0) ∨
          (r.isInfinity.toCVar.val V = 0 ∧
            ∃ h3 : W.Nonsingular (r.p.x.val V) (r.p.y.val V),
              Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3))) →
      ∀ (h1 : W.Nonsingular (p1'.x.val V) (p1'.y.val V))
        (h2 : W.Nonsingular (p2'.x.val V) (p2'.y.val V)),
        p1'.y.val V ≠ 0 →
        ((r.isInfinity.toCVar.val V = 1 ∧
           Point.some _ _ h1 + Point.some _ _ h2 = 0) ∨
         (r.isInfinity.toCVar.val V = 0 ∧
           ∃ h3 : W.Nonsingular (r.p.x.val V) (r.p.y.val V),
             Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3)) := by
    intro p1 p2 r hp1x hp1y hp2x hp2y hp h1 h2 hy1ne
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
  have htail := addFastTail_spec (V := V) W ha htwo
  cases fin with
  | checkFinite =>
    simp only [addFast]
    mvcgen [htail]
    rename_i p1 _ hp1 p2 _ hp2 _ _ _ r _
    exact fun _ hp => hglue p1 p2 r hp1.1 hp1.2 hp2.1 hp2.2 hp
  | dontCheckFinite =>
    simp only [addFast]
    mvcgen [htail]
    rename_i p1 _ hp1 p2 _ hp2 _ _ _ _ _ _ r _
    exact fun _ hp => hglue p1 p2 r hp1.1 hp1.2 hp2.1 hp2.2 hp

/-- `addFast` in `checkFinite` mode is sound with the infinity branch refuted: the
returned flag is the pinned constant `0` (it reads `0`, never `1`), so under any
satisfying valuation, for nonsingular operand points with the first finite (`y ≠ 0`),
the result reads as the finite EC group sum. The pinned-mode consumers (the `endoMul`
init chain) apply this form. -/
theorem addFast_checkFinite_spec {V : Valuation F} [Field F] [DecidableEq F] [d : HasCurve F]
    (p1' p2' : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄
    addFast (c := Builder V (KimchiConstraint F)) .checkFinite p1' p2'
    ⦃⇓ r _ => ⌜∀ (h1 : d.W.Nonsingular (p1'.x.val V) (p1'.y.val V))
          (h2 : d.W.Nonsingular (p2'.x.val V) (p2'.y.val V)),
          p1'.y.val V ≠ 0 →
          ∃ h3 : d.W.Nonsingular (r.p.x.val V) (r.p.y.val V),
            Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3⌝⦄ := by
  obtain ⟨W, ha, -, -, htwo⟩ := d
  have htail := addFastTail_spec (V := V) W ha htwo
  simp only [addFast]
  mvcgen [htail]
  rename_i p1 _ hp1 p2 _ hp2 _ _ _ r _
  obtain ⟨hp1x, hp1y⟩ := hp1
  obtain ⟨hp2x, hp2y⟩ := hp2
  intro hrinf hp h1 h2 hy1ne
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

/-! ## Completeness: the honest run -/

namespace AddFast

open WeierstrassCurve.Affine

/-- The `sameX` flag's typed read decodes to the coordinate comparison wherever the
flag reads as that comparison's bit. -/
private theorem sameX_decode [Field F] [DecidableEq F] {V : Valuation F} {sameX : BoolVar F}
    {x1 x2 : F} (h : (↑sameX : CVar F).val V = bit (decide (x1 = x2))) :
    (readVar (val := Bool) sameX).eval V = .ok (decide (x1 = x2)) := by
  rw [AsProver.eval_readVar_bool, h]
  cases decide (x1 = x2) <;> simp [bit]

/-- `infZWit` computes the canonical row's `infZ`. -/
private theorem infZWit_eval [Field F] [DecidableEq F] {V : Valuation F}
    {p1 p2 : AffinePoint (FVar F)} {sameX : BoolVar F} {x1 y1 x2 y2 : F}
    (hy1 : p1.y.val V = y1) (hy2 : p2.y.val V = y2)
    (hsx : (readVar (val := Bool) sameX).eval V = .ok (decide (x1 = x2))) :
    (infZWit p1 p2 sameX).eval V = .ok (Kimchi.Gate.AddComplete.build true x1 y1 x2 y2).infZ := by
  simp only [infZWit, AsProver.bind_eq, AsProver.eval_bind, AsProver.eval_readCVar, Except.bind,
    hy1, hy2]
  by_cases hy : y1 = y2
  · simp [hy, Kimchi.Gate.AddComplete.build]
  · simp only [hy, if_false, AsProver.eval_bind, hsx, Except.bind]
    by_cases hx : x1 = x2 <;> simp [hy, hx, Kimchi.Gate.AddComplete.build]

/-- `x21InvWit` computes the canonical row's `x21Inv`. -/
private theorem x21InvWit_eval [Field F] [DecidableEq F] {V : Valuation F}
    {p1 p2 : AffinePoint (FVar F)} {sameX : BoolVar F} {x1 y1 x2 y2 : F}
    (hx1 : p1.x.val V = x1) (hx2 : p2.x.val V = x2)
    (hsx : (readVar (val := Bool) sameX).eval V = .ok (decide (x1 = x2))) :
    (x21InvWit p1 p2 sameX).eval V
      = .ok (Kimchi.Gate.AddComplete.build true x1 y1 x2 y2).x21Inv := by
  simp only [x21InvWit, AsProver.bind_eq, AsProver.eval_bind, hsx, Except.bind]
  by_cases hx : x1 = x2 <;> simp [hx, AsProver.eval_readCVar, hx1, hx2, Except.bind,
    Kimchi.Gate.AddComplete.build]

/-- `slopeWit` computes the canonical row's slope. -/
private theorem slopeWit_eval [Field F] [DecidableEq F] {V : Valuation F}
    {p1 p2 : AffinePoint (FVar F)} {sameX : BoolVar F} {x1 y1 x2 y2 : F}
    (hx1 : p1.x.val V = x1) (hy1 : p1.y.val V = y1) (hx2 : p2.x.val V = x2)
    (hy2 : p2.y.val V = y2)
    (hsx : (readVar (val := Bool) sameX).eval V = .ok (decide (x1 = x2))) :
    (slopeWit p1 p2 sameX).eval V = .ok (Kimchi.Gate.AddComplete.build true x1 y1 x2 y2).s := by
  simp only [slopeWit, AsProver.bind_eq, AsProver.eval_bind, hsx, Except.bind]
  by_cases hx : x1 = x2 <;> simp [hx, AsProver.eval_readCVar, hx1, hy1, hx2, hy2, Except.bind,
    Kimchi.Gate.AddComplete.build]

/-- `x3Wit` computes the canonical row's `x3`, from its slope. -/
private theorem x3Wit_eval [Field F] [DecidableEq F] {V : Valuation F}
    {p1 p2 : AffinePoint (FVar F)} {s : FVar F} {x1 y1 x2 y2 : F}
    (hs : s.val V = (Kimchi.Gate.AddComplete.build true x1 y1 x2 y2).s)
    (hx1 : p1.x.val V = x1) (hx2 : p2.x.val V = x2) :
    (x3Wit p1 p2 s).eval V = .ok (Kimchi.Gate.AddComplete.build true x1 y1 x2 y2).x3 := by
  simp only [x3Wit, AsProver.bind_eq, AsProver.eval_bind, AsProver.eval_readCVar, Except.bind,
    hs, hx1, hx2, AsProver.pure_eq, AsProver.eval_pure]
  rfl

/-- `y3Wit` computes the canonical row's `y3`, from its slope and `x3`. -/
private theorem y3Wit_eval [Field F] [DecidableEq F] {V : Valuation F}
    {p1 : AffinePoint (FVar F)} {s x3 : FVar F} {x1 y1 x2 y2 : F}
    (hs : s.val V = (Kimchi.Gate.AddComplete.build true x1 y1 x2 y2).s)
    (hx3 : x3.val V = (Kimchi.Gate.AddComplete.build true x1 y1 x2 y2).x3)
    (hx1 : p1.x.val V = x1) (hy1 : p1.y.val V = y1) :
    (y3Wit p1 s x3).eval V = .ok (Kimchi.Gate.AddComplete.build true x1 y1 x2 y2).y3 := by
  simp only [y3Wit, AsProver.bind_eq, AsProver.eval_bind, AsProver.eval_readCVar, Except.bind,
    hs, hx3, hx1, hy1, AsProver.pure_eq, AsProver.eval_pure]
  rfl

/-- The state and result of `addFastTail`'s honest run: the five auxiliary columns
allocated in order — the verified gate's canonical row at the operand readings — and
the `addComplete` row (nothing allocated). -/
def addFastTailRun [Field F] [DecidableEq F] (st : ProverState F) (p1 p2 : AffinePoint (FVar F))
    (inf : BoolVar F) : ProverState F × AddResult F :=
  let w := Kimchi.Gate.AddComplete.build true (p1.x.val st.env.toValuation)
    (p1.y.val st.env.toValuation) (p2.x.val st.env.toValuation) (p2.y.val st.env.toValuation)
  (st.extendMany [w.infZ, w.x21Inv, w.s, w.x3, w.y3],
    ⟨⟨.var (st.nv + 3), .var (st.nv + 4)⟩, inf⟩)

/-- The tail's honest run, from in-scope operands whose `sameX` and `inf` read the
row's flags, the row they fill satisfying the verified gate: lands at
`addFastTailRun`. -/
private theorem addFastTail_run [Field F] [DecidableEq F] {p1 p2 : AffinePoint (FVar F)}
    {sameX inf : BoolVar F} {ib : Bool} (st : ProverState F)
    (h1x : p1.x.Scoped st) (h1y : p1.y.Scoped st) (h2x : p2.x.Scoped st) (h2y : p2.y.Scoped st)
    (hsx : (↑sameX : CVar F).Scoped st) (hinf : (↑inf : CVar F).Scoped st)
    (hsxv : (↑sameX : CVar F).val st.env.toValuation
      = bit (decide (p1.x.val st.env.toValuation = p2.x.val st.env.toValuation)))
    (hinfv : (↑inf : CVar F).val st.env.toValuation = bit ib)
    (hHolds : Kimchi.Gate.AddComplete.Holds
      { Kimchi.Gate.AddComplete.build true (p1.x.val st.env.toValuation)
          (p1.y.val st.env.toValuation) (p2.x.val st.env.toValuation)
          (p2.y.val st.env.toValuation) with inf := bit ib }) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (addFastTail (c := KimchiConstraint F) p1 p2 sameX inf) st.nv st.env
      = .ok ((addFastTailRun st p1 p2 inf).1.out (addFastTailRun st p1 p2 inf).2) := by
  simp only [addFastTailRun]
  generalize hx1 : p1.x.val st.env.toValuation = x1 at hsxv hHolds ⊢
  generalize hy1 : p1.y.val st.env.toValuation = y1 at hHolds ⊢
  generalize hx2 : p2.x.val st.env.toValuation = x2 at hsxv hHolds ⊢
  generalize hy2 : p2.y.val st.env.toValuation = y2 at hHolds ⊢
  set w := Kimchi.Gate.AddComplete.build true x1 y1 x2 y2 with hw
  -- the states along the tail, and the operands' readings there
  have hle₁ := st.le_extendMany [w.infZ]
  have hle₂ := st.le_extendMany [w.infZ, w.x21Inv]
  have hle₃ := st.le_extendMany [w.infZ, w.x21Inv, w.s]
  have hle₄ := st.le_extendMany [w.infZ, w.x21Inv, w.s, w.x3]
  have hle₅ := st.le_extendMany [w.infZ, w.x21Inv, w.s, w.x3, w.y3]
  have hsxd : ∀ st' : ProverState F, st.env.Le st'.env →
      (readVar (val := Bool) sameX).eval st'.env.toValuation = .ok (decide (x1 = x2)) :=
    fun st' hle => sameX_decode (by rw [CVar.val_of_le hle hsx, hsxv])
  -- the allocated names
  set v0 : FVar F := .var st.nv with hv0
  set v1 : FVar F := .var (st.extendMany [w.infZ]).nv with hv1
  set v2 : FVar F := .var (st.extendMany [w.infZ, w.x21Inv]).nv with hv2
  set v3 : FVar F := .var (st.extendMany [w.infZ, w.x21Inv, w.s]).nv with hv3
  set v4 : FVar F := .var (st.extendMany [w.infZ, w.x21Inv, w.s, w.x3]).nv with hv4
  have hs2₃ : v2.Scoped (st.extendMany [w.infZ, w.x21Inv, w.s]) :=
    st.new_mem_extendMany (i := 2) (by simp)
  have hs2₄ : v2.Scoped (st.extendMany [w.infZ, w.x21Inv, w.s, w.x3]) :=
    st.new_mem_extendMany (i := 2) (by simp)
  have hs3₄ : v3.Scoped (st.extendMany [w.infZ, w.x21Inv, w.s, w.x3]) :=
    st.new_mem_extendMany (i := 3) (by simp)
  have hv2₃ : v2.val (st.extendMany [w.infZ, w.x21Inv, w.s]).env.toValuation = w.s := by
    show (st.extendMany _).env.toValuation (st.nv + 2) = _
    rw [ProverState.get_extendMany_new st (by simp)]
    rfl
  have hv2₄ : v2.val (st.extendMany [w.infZ, w.x21Inv, w.s, w.x3]).env.toValuation = w.s := by
    show (st.extendMany _).env.toValuation (st.nv + 2) = _
    rw [ProverState.get_extendMany_new st (by simp)]
    rfl
  have hv3₄ : v3.val (st.extendMany [w.infZ, w.x21Inv, w.s, w.x3]).env.toValuation = w.x3 := by
    show (st.extendMany _).env.toValuation (st.nv + 3) = _
    rw [ProverState.get_extendMany_new st (by simp)]
    rfl
  simp only [addFastTail, prove_bind]
  rw [prove_witness_run (w := infZWit p1 p2 sameX) st
    (.bind (.readCVar h1y) fun _ => .bind (.readCVar h2y) fun _ => by
      split
      · trivial
      · exact .bind (.readVar_bool hsx) fun _ => by split <;> trivial)
    (v := w.infZ) (infZWit_eval hy1 hy2 (hsxd st (Assignments.Le.refl _)))]
  simp only [valueToFields_fvar_toList, fieldsToVar_fvar_alloc, Except.bind]
  rw [prove_witness_run (w := x21InvWit p1 p2 sameX) (st.extendMany [w.infZ])
    (.bind (.readVar_bool (hsx.of_le hle₁)) fun _ => by
      split
      · trivial
      · exact .bind (.readCVar (h1x.of_le hle₁)) fun _ => .bind (.readCVar (h2x.of_le hle₁))
          fun _ => trivial)
    (v := w.x21Inv) (x21InvWit_eval (y1 := y1) (y2 := y2)
      (by rw [CVar.val_of_le hle₁ h1x, hx1]) (by rw [CVar.val_of_le hle₁ h2x, hx2]) (hsxd _ hle₁))]
  simp only [valueToFields_fvar_toList, fieldsToVar_fvar_alloc, Except.bind,
    ProverState.extendMany_append, List.cons_append, List.nil_append]
  rw [prove_witness_run (w := slopeWit p1 p2 sameX) (st.extendMany [w.infZ, w.x21Inv])
    (.bind (.readVar_bool (hsx.of_le hle₂)) fun _ => by
      split
      · exact .bind (.readCVar (h1x.of_le hle₂)) fun _ => .bind (.readCVar (h1y.of_le hle₂))
          fun _ => trivial
      · exact .bind (.readCVar (h1y.of_le hle₂)) fun _ => .bind (.readCVar (h2y.of_le hle₂))
          fun _ => .bind (.readCVar (h1x.of_le hle₂)) fun _ => .bind (.readCVar (h2x.of_le hle₂))
          fun _ => trivial)
    (v := w.s) (slopeWit_eval (by rw [CVar.val_of_le hle₂ h1x, hx1])
      (by rw [CVar.val_of_le hle₂ h1y, hy1]) (by rw [CVar.val_of_le hle₂ h2x, hx2])
      (by rw [CVar.val_of_le hle₂ h2y, hy2]) (hsxd _ hle₂))]
  simp only [valueToFields_fvar_toList, fieldsToVar_fvar_alloc, Except.bind,
    ProverState.extendMany_append, List.cons_append, List.nil_append]
  rw [prove_witness_run (w := x3Wit p1 p2 v2) (st.extendMany [w.infZ, w.x21Inv, w.s])
    (.bind (.readCVar hs2₃) fun _ => .bind (.readCVar (h1x.of_le hle₃)) fun _ =>
      .bind (.readCVar (h2x.of_le hle₃)) fun _ => trivial)
    (v := w.x3) (x3Wit_eval (y1 := y1) (y2 := y2) hv2₃
      (by rw [CVar.val_of_le hle₃ h1x, hx1]) (by rw [CVar.val_of_le hle₃ h2x, hx2]))]
  simp only [valueToFields_fvar_toList, fieldsToVar_fvar_alloc, Except.bind,
    ProverState.extendMany_append, List.cons_append, List.nil_append]
  rw [prove_witness_run (w := y3Wit p1 v2 v3) (st.extendMany [w.infZ, w.x21Inv, w.s, w.x3])
    (.bind (.readCVar hs2₄) fun _ => .bind (.readCVar (h1x.of_le hle₄)) fun _ =>
      .bind (.readCVar hs3₄) fun _ => .bind (.readCVar (h1y.of_le hle₄)) fun _ => trivial)
    (v := w.y3) (y3Wit_eval (x2 := x2) (y2 := y2) hv2₄ hv3₄
      (by rw [CVar.val_of_le hle₄ h1x, hx1]) (by rw [CVar.val_of_le hle₄ h1y, hy1]))]
  simp only [valueToFields_fvar_toList, fieldsToVar_fvar_alloc, Except.bind,
    ProverState.extendMany_append, List.cons_append, List.nil_append]
  -- the row
  have hget : ∀ (i : ℕ) (hi : i < 5), (CVar.var (st.nv + i)).val
      (st.extendMany [w.infZ, w.x21Inv, w.s, w.x3, w.y3]).env.toValuation
      = [w.infZ, w.x21Inv, w.s, w.x3, w.y3][i] := by
    intro i hi
    show (st.extendMany _).env.toValuation (st.nv + i) = _
    rw [ProverState.get_extendMany_new st (by simpa using hi)]
  have hmem : ∀ (i : ℕ), i < 5 →
      (CVar.var (st.nv + i)).Scoped (st.extendMany [w.infZ, w.x21Inv, w.s, w.x3, w.y3]) :=
    fun i hi => st.new_mem_extendMany (by simpa using hi)
  have hcheck : Checker.holds (F := F) (c := KimchiConstraint F)
      (KimchiSystem.addComplete ⟨p1, p2, ⟨v3, v4⟩, inf.toCVar, sameX.toCVar, v2, v0, v1⟩)
      (st.extendMany [w.infZ, w.x21Inv, w.s, w.x3, w.y3]).env = true := by
    show KimchiConstraint.check (.addComplete _) _ = true
    have heval : AddComplete.eval (st.extendMany [w.infZ, w.x21Inv, w.s, w.x3, w.y3]).env
        ⟨p1, p2, ⟨v3, v4⟩, inf.toCVar, sameX.toCVar, v2, v0, v1⟩ = .ok { w with inf := bit ib } := by
      have e0 := CVar.eval_eq_val (hmem 0 (by omega))
      have e1 := CVar.eval_eq_val (hmem 1 (by omega))
      have e2 := CVar.eval_eq_val (hmem 2 (by omega))
      have e3 := CVar.eval_eq_val (hmem 3 (by omega))
      have e4 := CVar.eval_eq_val (hmem 4 (by omega))
      rw [hget 0 (by omega)] at e0
      rw [hget 1 (by omega)] at e1
      rw [hget 2 (by omega)] at e2
      rw [hget 3 (by omega)] at e3
      rw [hget 4 (by omega)] at e4
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2 e3 e4
      simp only [AddComplete.eval, Bind.bind, Except.bind,
        CVar.eval_eq_val (h1x.of_le hle₅), CVar.eval_eq_val (h1y.of_le hle₅),
        CVar.eval_eq_val (h2x.of_le hle₅), CVar.eval_eq_val (h2y.of_le hle₅),
        CVar.eval_eq_val (hinf.of_le hle₅), CVar.eval_eq_val (hsx.of_le hle₅),
        CVar.val_of_le hle₅ h1x, CVar.val_of_le hle₅ h1y, CVar.val_of_le hle₅ h2x,
        CVar.val_of_le hle₅ h2y, CVar.val_of_le hle₅ hinf, CVar.val_of_le hle₅ hsx,
        hx1, hy1, hx2, hy2, hinfv, hsxv, Pure.pure, Except.pure]
      rw [show v3 = CVar.var (st.nv + 3) from rfl, show v4 = CVar.var (st.nv + 4) from rfl,
        show v2 = CVar.var (st.nv + 2) from rfl, show v0 = CVar.var (st.nv + 0) from rfl,
        show v1 = CVar.var (st.nv + 1) from rfl, e0, e1, e2, e3, e4]
      simp only [Except.bind, Except.ok.injEq, hw, Kimchi.Gate.AddComplete.build, bit]
    simp only [KimchiConstraint.check, heval]
    exact (Kimchi.Gate.AddComplete.ok_iff _).mpr hHolds
  rw [prove_addConstraint _ hcheck]
  rfl

/-- The state and result of `addFast`'s honest run: the seals, the `sameX` bit, the
mode's `inf` (the constant `false` under `checkFinite`, a witnessed bit otherwise), the
tail. -/
def addFastCoreRun [Field F] [DecidableEq F] (st₂ : ProverState F) (fin : Finiteness)
    (q1 q2 : AffinePoint (FVar F)) : ProverState F × AddResult F :=
  let st₃ := st₂.extendMany
    [bit (decide (q1.x.val st₂.env.toValuation = q2.x.val st₂.env.toValuation))]
  match fin with
  | .checkFinite => addFastTailRun st₃ q1 q2 false_
  | .dontCheckFinite =>
    let st₄ := st₃.extendMany
      [bit (decide (q1.x.val st₃.env.toValuation = q2.x.val st₃.env.toValuation)
        && !decide (q1.y.val st₃.env.toValuation = q2.y.val st₃.env.toValuation))]
    addFastTailRun st₄ q1 q2 (BoolVar.unchecked (.var st₃.nv))

/-- `addFast`'s run: both operands sealed, then `addFastCoreRun` at the sealed points. -/
def addFastRun [Field F] [DecidableEq F] (st : ProverState F) (fin : Finiteness)
    (p1' p2' : AffinePoint (FVar F)) : ProverState F × AddResult F :=
  let r1 := sealPointRun st p1'
  let r2 := sealPointRun r1.1 p2'
  addFastCoreRun r2.1 fin r1.2 r2.2

/-- The operand conditions of the honest `addFast` run: both operands nonsingular on
the curve, the first finite (`y ≠ 0`), and — under `checkFinite` — the group sum
nonzero. -/
def Operands [Field F] [DecidableEq F] (d : HasCurve F) (fin : Finiteness)
    (x1 y1 x2 y2 : F) : Prop :=
  ∃ (h1 : d.W.Nonsingular x1 y1) (h2 : d.W.Nonsingular x2 y2),
    y1 ≠ 0 ∧ (fin = .checkFinite → Point.some _ _ h1 + Point.some _ _ h2 ≠ 0)

/-- `addFast`'s honest run on in-scope operands satisfying `Operands` lands at
`addFastRun`: the checking interpreter accepts every row the gadget emits. -/
theorem addFast_run [Field F] [DecidableEq F] [d : HasCurve F] (fin : Finiteness)
    {p1' p2' : AffinePoint (FVar F)} (st : ProverState F)
    (h1x : p1'.x.Scoped st) (h1y : p1'.y.Scoped st) (h2x : p2'.x.Scoped st) (h2y : p2'.y.Scoped st)
    (hops : Operands d fin (p1'.x.val st.env.toValuation) (p1'.y.val st.env.toValuation)
      (p2'.x.val st.env.toValuation) (p2'.y.val st.env.toValuation)) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (addFast (c := KimchiConstraint F) fin p1' p2') st.nv st.env
      = .ok ((addFastRun st fin p1' p2').1.out (addFastRun st fin p1' p2').2) := by
  revert hops
  obtain ⟨W, ha, -, -, htwo⟩ := d
  intro hops
  unfold Operands at hops
  dsimp only at hops
  obtain ⟨h1n, h2n, hy1ne, hsumne⟩ := hops
  have hon1 := h1n.1
  have hon2 := h2n.1
  have hfin : fin = .checkFinite → ¬(p1'.x.val st.env.toValuation = p2'.x.val st.env.toValuation
      ∧ p1'.y.val st.env.toValuation
        = W.negY (p2'.x.val st.env.toValuation) (p2'.y.val st.env.toValuation)) := by
    intro hf
    rintro ⟨hxeq, hyeq⟩
    apply hsumne hf
    generalize p1'.x.val st.env.toValuation = x1v at h1n hxeq ⊢
    generalize p1'.y.val st.env.toValuation = y1v at h1n hyeq ⊢
    subst hxeq hyeq
    rw [show Point.some (p2'.x.val st.env.toValuation)
        (W.negY (p2'.x.val st.env.toValuation) (p2'.y.val st.env.toValuation)) h1n
        = -Point.some (p2'.x.val st.env.toValuation) (p2'.y.val st.env.toValuation) h2n from by
      rw [WeierstrassCurve.Affine.Point.neg_some]]
    exact neg_add_cancel _
  have hg1 := sealPointRun_grants (st := st) h1x h1y
  have hg2 := sealPointRun_grants (st := (sealPointRun st p1').1) (h2x.of_le hg1.1.le)
    (h2y.of_le hg1.1.le)
  simp only [addFast, addFastRun, addFastCoreRun, prove_bind, sealPoint_run st h1x h1y,
    Except.bind,
    sealPoint_run _ (h2x.of_le hg1.1.le) (h2y.of_le hg1.1.le)]
  generalize hr1 : sealPointRun st p1' = r1 at hg1 hg2 ⊢
  generalize hr2 : sealPointRun r1.1 p2' = r2 at hg2 ⊢
  have hr1x : r1.2.x.val r2.1.env.toValuation = p1'.x.val st.env.toValuation := by
    rw [CVar.val_of_le hg2.1.le hg1.1.fvar_scoped, hg1.1.fvar_val]
  have hr1y : r1.2.y.val r2.1.env.toValuation = p1'.y.val st.env.toValuation := by
    rw [CVar.val_of_le hg2.1.le hg1.2.fvar_scoped, hg1.2.fvar_val]
  have hr2x : r2.2.x.val r2.1.env.toValuation = p2'.x.val st.env.toValuation := by
    rw [hg2.1.fvar_val, CVar.val_of_le hg1.1.le h2x]
  have hr2y : r2.2.y.val r2.1.env.toValuation = p2'.y.val st.env.toValuation := by
    rw [hg2.2.fvar_val, CVar.val_of_le hg1.1.le h2y]
  have hs1x : r1.2.x.Scoped r2.1 := hg1.1.fvar_scoped.of_le hg2.1.le
  have hs1y : r1.2.y.Scoped r2.1 := hg1.2.fvar_scoped.of_le hg2.1.le
  have hs2x : r2.2.x.Scoped r2.1 := hg2.1.fvar_scoped
  have hs2y : r2.2.y.Scoped r2.1 := hg2.2.fvar_scoped
  rw [prove_witness_run (w := UnChecked.mk <$> sameXWit r1.2 r2.2) r2.1
    (.bind (.bind (.readCVar hs1x) fun _ => .bind (.readCVar hs2x) fun _ => trivial) fun _ =>
      trivial)
    (v := ⟨decide (r1.2.x.val r2.1.env.toValuation = r2.2.x.val r2.1.env.toValuation)⟩)
    (by simp [sameXWit, Except.bind])]
  simp only [valueToFields_uncheckedBool_toList, fieldsToVar_uncheckedBool_alloc, Except.bind]
  generalize hb : decide (r1.2.x.val r2.1.env.toValuation = r2.2.x.val r2.1.env.toValuation) = sb
  have hle₃ := r2.1.le_extendMany [bit sb]
  have hsx₃ : (CVar.var r2.1.nv).val (r2.1.extendMany [bit sb]).env.toValuation = bit sb :=
    ProverState.get_extendMany_head ..
  have hsxv₃ : (CVar.var r2.1.nv).val (r2.1.extendMany [bit sb]).env.toValuation
      = bit (decide (r1.2.x.val (r2.1.extendMany [bit sb]).env.toValuation
        = r2.2.x.val (r2.1.extendMany [bit sb]).env.toValuation)) := by
    rw [hsx₃, CVar.val_of_le hle₃ hs1x, CVar.val_of_le hle₃ hs2x, hb]
  cases fin with
  | checkFinite =>
    dsimp only
    simp only [prove_bind, prove_pure, Except.bind]
    have hHolds := Kimchi.Gate.AddComplete.complete_build (checkFinite := true) W ha
      hon1 hon2 hy1ne htwo (fun _ => hfin rfl)
    rw [addFastTail_run (sameX := BoolVar.unchecked (.var r2.1.nv)) (inf := false_) _
      (hs1x.of_le hle₃) (hs1y.of_le hle₃) (hs2x.of_le hle₃) (hs2y.of_le hle₃)
      (ProverState.mem_extendMany_head ..) trivial
      (by rw [BoolVar.toCVar_unchecked]; exact hsxv₃) (ib := false) rfl
      (by rw [CVar.val_of_le hle₃ hs1x, CVar.val_of_le hle₃ hs1y, CVar.val_of_le hle₃ hs2x,
        CVar.val_of_le hle₃ hs2y, hr1x, hr1y, hr2x, hr2y]; exact hHolds)]
  | dontCheckFinite =>
    dsimp only
    simp only [prove_bind, prove_pure, Except.bind]
    have hHolds := Kimchi.Gate.AddComplete.complete_build (checkFinite := false) W ha
      hon1 hon2 hy1ne htwo (fun h => Bool.noConfusion h)
    rw [prove_witness_run (w := UnChecked.mk <$> infWit r1.2 r2.2 (BoolVar.unchecked (.var r2.1.nv)))
      (r2.1.extendMany [bit sb])
      (.bind (.bind (.readVar_bool (ProverState.mem_extendMany_head ..)) fun _ =>
        .bind (.readCVar (hs1y.of_le hle₃)) fun _ => .bind (.readCVar (hs2y.of_le hle₃)) fun _ =>
          trivial) fun _ => trivial)
      (v := ⟨sb && !decide (r1.2.y.val (r2.1.extendMany [bit sb]).env.toValuation
        = r2.2.y.val (r2.1.extendMany [bit sb]).env.toValuation)⟩)
      (by
        simp only [infWit, AsProver.map_eq, AsProver.bind_eq, AsProver.eval_bind,
          AsProver.eval_readVar_bool, AsProver.eval_readCVar, Except.bind, AsProver.pure_eq,
          AsProver.eval_pure, BoolVar.toCVar_unchecked, hsx₃]
        cases sb <;> simp [bit])]
    simp only [valueToFields_uncheckedBool_toList, fieldsToVar_uncheckedBool_alloc, Except.bind]
    rw [CVar.val_of_le hle₃ hs1x, CVar.val_of_le hle₃ hs2x, hb]
    generalize hib : (sb && !decide (r1.2.y.val (r2.1.extendMany [bit sb]).env.toValuation
      = r2.2.y.val (r2.1.extendMany [bit sb]).env.toValuation)) = ib
    have hle₄ := (r2.1.extendMany [bit sb]).le_extendMany [bit ib]
    have hsx₃s : (CVar.var r2.1.nv).Scoped (r2.1.extendMany [bit sb]) :=
      ProverState.mem_extendMany_head ..
    have hinf₄ : (CVar.var (r2.1.extendMany [bit sb]).nv).Scoped
        ((r2.1.extendMany [bit sb]).extendMany [bit ib]) :=
      ProverState.mem_extendMany_head ..
    rw [addFastTail_run (sameX := BoolVar.unchecked (.var r2.1.nv))
      (inf := BoolVar.unchecked (.var (r2.1.extendMany [bit sb]).nv)) _
      (hs1x.of_le (hle₃.trans hle₄)) (hs1y.of_le (hle₃.trans hle₄))
      (hs2x.of_le (hle₃.trans hle₄)) (hs2y.of_le (hle₃.trans hle₄)) (hsx₃s.of_le hle₄) hinf₄
      (by rw [BoolVar.toCVar_unchecked, CVar.val_of_le hle₄ hsx₃s, hsxv₃,
        CVar.val_of_le hle₄ (hs1x.of_le hle₃), CVar.val_of_le hle₄ (hs2x.of_le hle₃)])
      (ib := ib) (by rw [BoolVar.toCVar_unchecked]; exact ProverState.get_extendMany_head ..)
      (by
        rw [CVar.val_of_le (hle₃.trans hle₄) hs1x, CVar.val_of_le (hle₃.trans hle₄) hs1y,
          CVar.val_of_le (hle₃.trans hle₄) hs2x, CVar.val_of_le (hle₃.trans hle₄) hs2y,
          hr1x, hr1y, hr2x, hr2y]
        rw [← hib, CVar.val_of_le hle₃ hs1y, CVar.val_of_le hle₃ hs2y, ← hb, hr1x, hr1y, hr2x,
          hr2y]
        exact hHolds)]

/-- What `addFastTailRun` grants: the table grew, the output point and flag are in
scope, the point reads as the canonical row's output at the operand readings and the
flag as it read before. -/
private theorem addFastTailRun_scope [Field F] [DecidableEq F] (st : ProverState F)
    (p1 p2 : AffinePoint (FVar F)) {inf : BoolVar F} (hinf : (↑inf : CVar F).Scoped st) :
    st.env.Le (addFastTailRun st p1 p2 inf).1.env ∧
      (addFastTailRun st p1 p2 inf).2.p.x.Scoped (addFastTailRun st p1 p2 inf).1 ∧
      (addFastTailRun st p1 p2 inf).2.p.y.Scoped (addFastTailRun st p1 p2 inf).1 ∧
      (↑(addFastTailRun st p1 p2 inf).2.isInfinity : CVar F).Scoped (addFastTailRun st p1 p2 inf).1 ∧
      (addFastTailRun st p1 p2 inf).2.p.x.val (addFastTailRun st p1 p2 inf).1.env.toValuation
        = (Kimchi.Gate.AddComplete.build true (p1.x.val st.env.toValuation)
          (p1.y.val st.env.toValuation) (p2.x.val st.env.toValuation)
          (p2.y.val st.env.toValuation)).x3 ∧
      (addFastTailRun st p1 p2 inf).2.p.y.val (addFastTailRun st p1 p2 inf).1.env.toValuation
        = (Kimchi.Gate.AddComplete.build true (p1.x.val st.env.toValuation)
          (p1.y.val st.env.toValuation) (p2.x.val st.env.toValuation)
          (p2.y.val st.env.toValuation)).y3 ∧
      (↑(addFastTailRun st p1 p2 inf).2.isInfinity : CVar F).val
          (addFastTailRun st p1 p2 inf).1.env.toValuation
        = (↑inf : CVar F).val st.env.toValuation := by
  simp only [addFastTailRun]
  set w := Kimchi.Gate.AddComplete.build true (p1.x.val st.env.toValuation)
    (p1.y.val st.env.toValuation) (p2.x.val st.env.toValuation) (p2.y.val st.env.toValuation)
    with hw
  have hle := st.le_extendMany [w.infZ, w.x21Inv, w.s, w.x3, w.y3]
  refine ⟨hle, st.new_mem_extendMany (i := 3) (by simp), st.new_mem_extendMany (i := 4) (by simp),
    hinf.of_le hle, ?_, ?_, CVar.val_of_le hle hinf⟩
  · show (st.extendMany _).env.toValuation (st.nv + 3) = _
    rw [ProverState.get_extendMany_new st (by simp)]
    rfl
  · show (st.extendMany _).env.toValuation (st.nv + 4) = _
    rw [ProverState.get_extendMany_new st (by simp)]
    rfl

/-- What `addFastCoreRun` grants at sealed operands in scope: the table grew, the output
point and flag are in scope, and at nonsingular operands they read as the group sum —
either the flag reads `1` and the sum is zero, or it reads `0` and the coordinates are a
nonsingular point equal to the sum (the filled row is the gate's canonical one, whose
`sound` characterizes what it computed). -/
private theorem addFastCoreRun_grants [Field F] [DecidableEq F] [d : HasCurve F]
    (fin : Finiteness) {q1 q2 : AffinePoint (FVar F)} (st₂ : ProverState F)
    (hs1x : q1.x.Scoped st₂) (hs1y : q1.y.Scoped st₂) (hs2x : q2.x.Scoped st₂)
    (hs2y : q2.y.Scoped st₂)
    (hops : Operands d fin (q1.x.val st₂.env.toValuation) (q1.y.val st₂.env.toValuation)
      (q2.x.val st₂.env.toValuation) (q2.y.val st₂.env.toValuation)) :
    st₂.env.Le (addFastCoreRun st₂ fin q1 q2).1.env ∧
      (addFastCoreRun st₂ fin q1 q2).2.p.x.Scoped (addFastCoreRun st₂ fin q1 q2).1 ∧
      (addFastCoreRun st₂ fin q1 q2).2.p.y.Scoped (addFastCoreRun st₂ fin q1 q2).1 ∧
      (↑(addFastCoreRun st₂ fin q1 q2).2.isInfinity : CVar F).Scoped
        (addFastCoreRun st₂ fin q1 q2).1 ∧
      ∀ (h1 : d.W.Nonsingular (q1.x.val st₂.env.toValuation) (q1.y.val st₂.env.toValuation))
        (h2 : d.W.Nonsingular (q2.x.val st₂.env.toValuation) (q2.y.val st₂.env.toValuation)),
        ((↑(addFastCoreRun st₂ fin q1 q2).2.isInfinity : CVar F).val
            (addFastCoreRun st₂ fin q1 q2).1.env.toValuation = 1 ∧
          Point.some _ _ h1 + Point.some _ _ h2 = 0) ∨
        (∃ h3 : d.W.Nonsingular
            ((addFastCoreRun st₂ fin q1 q2).2.p.x.val
              (addFastCoreRun st₂ fin q1 q2).1.env.toValuation)
            ((addFastCoreRun st₂ fin q1 q2).2.p.y.val
              (addFastCoreRun st₂ fin q1 q2).1.env.toValuation),
          (↑(addFastCoreRun st₂ fin q1 q2).2.isInfinity : CVar F).val
              (addFastCoreRun st₂ fin q1 q2).1.env.toValuation = 0 ∧
            Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3) := by
  revert hops
  obtain ⟨W, ha, -, -, htwo⟩ := d
  intro hops
  unfold Operands at hops
  dsimp only at hops
  obtain ⟨h1n, h2n, hy1ne, hsumne⟩ := hops
  have hon1 := h1n.1
  have hon2 := h2n.1
  have hfin : fin = .checkFinite → ¬(q1.x.val st₂.env.toValuation = q2.x.val st₂.env.toValuation
      ∧ q1.y.val st₂.env.toValuation
        = W.negY (q2.x.val st₂.env.toValuation) (q2.y.val st₂.env.toValuation)) := by
    intro hf
    rintro ⟨hxeq, hyeq⟩
    apply hsumne hf
    generalize q1.x.val st₂.env.toValuation = x1v at h1n hxeq ⊢
    generalize q1.y.val st₂.env.toValuation = y1v at h1n hyeq ⊢
    subst hxeq hyeq
    rw [show Point.some (q2.x.val st₂.env.toValuation)
        (W.negY (q2.x.val st₂.env.toValuation) (q2.y.val st₂.env.toValuation)) h1n
        = -Point.some (q2.x.val st₂.env.toValuation) (q2.y.val st₂.env.toValuation) h2n from by
      rw [WeierstrassCurve.Affine.Point.neg_some]]
    exact neg_add_cancel _
  cases fin with
  | checkFinite =>
    set sb := decide (q1.x.val st₂.env.toValuation = q2.x.val st₂.env.toValuation) with hb
    rw [show addFastCoreRun st₂ .checkFinite q1 q2
      = addFastTailRun (st₂.extendMany [bit sb]) q1 q2 false_ from rfl]
    have hle₃ := st₂.le_extendMany [bit sb]
    have hHolds := Kimchi.Gate.AddComplete.complete_build (checkFinite := true) W ha
      hon1 hon2 hy1ne htwo (fun _ => hfin rfl)
    have ht := addFastTailRun_scope (st₂.extendMany [bit sb]) q1 q2 (inf := false_) trivial
    rw [CVar.val_of_le hle₃ hs1x, CVar.val_of_le hle₃ hs1y, CVar.val_of_le hle₃ hs2x,
      CVar.val_of_le hle₃ hs2y] at ht
    obtain ⟨htle, hsx3, hsy3, hsinf, hx3, hy3, hinfv⟩ := ht
    refine ⟨hle₃.trans htle, hsx3, hsy3, hsinf, fun h1 h2 => ?_⟩
    rw [hx3, hy3, hinfv]
    rcases Kimchi.Gate.AddComplete.sound W ha _ h1 h2 hHolds hy1ne htwo with
      ⟨hinf1, _⟩ | ⟨_, h3, hsum⟩
    · exact absurd (hinf1 : (0 : F) = 1) zero_ne_one
    · exact Or.inr ⟨h3, rfl, hsum⟩
  | dontCheckFinite =>
    set sb := decide (q1.x.val st₂.env.toValuation = q2.x.val st₂.env.toValuation) with hb
    rw [show addFastCoreRun st₂ .dontCheckFinite q1 q2 = addFastTailRun
        ((st₂.extendMany [bit sb]).extendMany
          [bit (decide (q1.x.val (st₂.extendMany [bit sb]).env.toValuation
              = q2.x.val (st₂.extendMany [bit sb]).env.toValuation)
            && !decide (q1.y.val (st₂.extendMany [bit sb]).env.toValuation
              = q2.y.val (st₂.extendMany [bit sb]).env.toValuation))])
        q1 q2 (BoolVar.unchecked (.var (st₂.extendMany [bit sb]).nv)) from rfl]
    have hle₃ := st₂.le_extendMany [bit sb]
    rw [CVar.val_of_le hle₃ hs1x, CVar.val_of_le hle₃ hs2x, ← hb]
    set ib := (sb && !decide (q1.y.val (st₂.extendMany [bit sb]).env.toValuation
      = q2.y.val (st₂.extendMany [bit sb]).env.toValuation)) with hib
    have hle₄ := (st₂.extendMany [bit sb]).le_extendMany [bit ib]
    have hHolds := Kimchi.Gate.AddComplete.complete_build (checkFinite := false) W ha
      hon1 hon2 hy1ne htwo (fun h => Bool.noConfusion h)
    have hinf₄ : (CVar.var (st₂.extendMany [bit sb]).nv).Scoped
        ((st₂.extendMany [bit sb]).extendMany [bit ib]) :=
      ProverState.mem_extendMany_head ..
    have ht := addFastTailRun_scope ((st₂.extendMany [bit sb]).extendMany [bit ib]) q1 q2
      (inf := BoolVar.unchecked (.var (st₂.extendMany [bit sb]).nv)) hinf₄
    rw [CVar.val_of_le (hle₃.trans hle₄) hs1x, CVar.val_of_le (hle₃.trans hle₄) hs1y,
      CVar.val_of_le (hle₃.trans hle₄) hs2x, CVar.val_of_le (hle₃.trans hle₄) hs2y,
      BoolVar.toCVar_unchecked,
      show (CVar.var (st₂.extendMany [bit sb]).nv).val
          ((st₂.extendMany [bit sb]).extendMany [bit ib]).env.toValuation = bit ib from
        ProverState.get_extendMany_head ..] at ht
    obtain ⟨htle, hsx3, hsy3, hsinf, hx3, hy3, hinfv⟩ := ht
    refine ⟨hle₃.trans (hle₄.trans htle), hsx3, hsy3, hsinf, fun h1 h2 => ?_⟩
    rw [hx3, hy3, hinfv]
    have hHolds' : Kimchi.Gate.AddComplete.Holds
        ({ Kimchi.Gate.AddComplete.build true (q1.x.val st₂.env.toValuation)
          (q1.y.val st₂.env.toValuation) (q2.x.val st₂.env.toValuation)
          (q2.y.val st₂.env.toValuation) with inf := bit ib } :
            Kimchi.Gate.AddComplete.Witness F) := by
      rw [hib, CVar.val_of_le hle₃ hs1y, CVar.val_of_le hle₃ hs2y, hb]
      exact hHolds
    rcases Kimchi.Gate.AddComplete.sound W ha _ h1 h2 hHolds' hy1ne htwo with
      ⟨hinf1, hsum⟩ | ⟨hinf0, h3, hsum⟩
    · exact Or.inl ⟨hinf1, hsum⟩
    · exact Or.inr ⟨h3, hinf0, hsum⟩

/-- What `addFastRun` grants: `addFastCoreRun_grants` at the sealed operands, whose
readings are the operands'. -/
theorem addFastRun_grants [Field F] [DecidableEq F] [d : HasCurve F] (fin : Finiteness)
    {p1' p2' : AffinePoint (FVar F)} (st : ProverState F)
    (h1x : p1'.x.Scoped st) (h1y : p1'.y.Scoped st) (h2x : p2'.x.Scoped st) (h2y : p2'.y.Scoped st)
    (hops : Operands d fin (p1'.x.val st.env.toValuation) (p1'.y.val st.env.toValuation)
      (p2'.x.val st.env.toValuation) (p2'.y.val st.env.toValuation)) :
    st.env.Le (addFastRun st fin p1' p2').1.env ∧
      (addFastRun st fin p1' p2').2.p.x.Scoped (addFastRun st fin p1' p2').1 ∧
      (addFastRun st fin p1' p2').2.p.y.Scoped (addFastRun st fin p1' p2').1 ∧
      (↑(addFastRun st fin p1' p2').2.isInfinity : CVar F).Scoped (addFastRun st fin p1' p2').1 ∧
      ∀ (h1 : d.W.Nonsingular (p1'.x.val st.env.toValuation) (p1'.y.val st.env.toValuation))
        (h2 : d.W.Nonsingular (p2'.x.val st.env.toValuation) (p2'.y.val st.env.toValuation)),
        ((↑(addFastRun st fin p1' p2').2.isInfinity : CVar F).val
            (addFastRun st fin p1' p2').1.env.toValuation = 1 ∧
          Point.some _ _ h1 + Point.some _ _ h2 = 0) ∨
        (∃ h3 : d.W.Nonsingular
            ((addFastRun st fin p1' p2').2.p.x.val (addFastRun st fin p1' p2').1.env.toValuation)
            ((addFastRun st fin p1' p2').2.p.y.val (addFastRun st fin p1' p2').1.env.toValuation),
          (↑(addFastRun st fin p1' p2').2.isInfinity : CVar F).val
              (addFastRun st fin p1' p2').1.env.toValuation = 0 ∧
            Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3) := by
  have hg1 := sealPointRun_grants (st := st) h1x h1y
  have hg2 := sealPointRun_grants (st := (sealPointRun st p1').1) (h2x.of_le hg1.1.le)
    (h2y.of_le hg1.1.le)
  have hr1x : (sealPointRun st p1').2.x.val
      (sealPointRun (sealPointRun st p1').1 p2').1.env.toValuation = p1'.x.val st.env.toValuation := by
    rw [CVar.val_of_le hg2.1.le hg1.1.fvar_scoped, hg1.1.fvar_val]
  have hr1y : (sealPointRun st p1').2.y.val
      (sealPointRun (sealPointRun st p1').1 p2').1.env.toValuation = p1'.y.val st.env.toValuation := by
    rw [CVar.val_of_le hg2.1.le hg1.2.fvar_scoped, hg1.2.fvar_val]
  have hr2x : (sealPointRun (sealPointRun st p1').1 p2').2.x.val
      (sealPointRun (sealPointRun st p1').1 p2').1.env.toValuation = p2'.x.val st.env.toValuation := by
    rw [hg2.1.fvar_val, CVar.val_of_le hg1.1.le h2x]
  have hr2y : (sealPointRun (sealPointRun st p1').1 p2').2.y.val
      (sealPointRun (sealPointRun st p1').1 p2').1.env.toValuation = p2'.y.val st.env.toValuation := by
    rw [hg2.2.fvar_val, CVar.val_of_le hg1.1.le h2y]
  have hcore := addFastCoreRun_grants fin (sealPointRun (sealPointRun st p1').1 p2').1
    (hg1.1.fvar_scoped.of_le hg2.1.le) (hg1.2.fvar_scoped.of_le hg2.1.le) hg2.1.fvar_scoped
    hg2.2.fvar_scoped (by rw [hr1x, hr1y, hr2x, hr2y]; exact hops)
  rw [hr1x, hr1y, hr2x, hr2y] at hcore
  exact ⟨hg1.1.le.trans (hg2.1.le.trans hcore.1), hcore.2⟩

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

end Snarky.Kimchi
