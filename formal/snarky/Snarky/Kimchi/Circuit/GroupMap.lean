import Snarky.DSL.Field
import Snarky.Tactic
import Snarky.DSL.Assert
import Snarky.DSL.Boolean
import Snarky.Kimchi.Semantics
import Poseidon.GroupMap

/-!
# The BW19 hash-to-curve gadget

Port of `Snarky.Circuit.Kimchi.GroupMap`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/GroupMap.purs; mina
`group_map/bw19.ml`; Wahby–Boneh 2019, https://eprint.iacr.org/2019/403): map a
field element onto a curve `y² = x³ + b`. Three candidate abscissae are computed
from the `setup()` parameters; per candidate, `sqrtFlagged` witnesses a
residuosity flag and a root of either the candidate ordinate square or its
non-residue twist; at least one flag is asserted set, and the point is the
first-flagged candidate, selected by mutually exclusive boolean products.

The value level (`potentialXs`, `groupMapPure`) is identified with the wire verifier's
fixture-validated map: `groupMapPure_toGroup` proves it computes
`Poseidon.GroupMap.toGroup` — the `U`-base derivation the kimchi verifier runs — at any
wire `Spec`. The generic laws quote the module's own pure model; the wire section
restates them with the wire map itself as the spec.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS `groupMapParams` builds the parameter record from the `HasBW19` FFI and a
  non-residue search; the port takes `GroupMapParams` as data — the deployed
  values live with their curves (the poseidon package's `setup()` constants).
- PS's advice consults the `HasSqrt` class; the port threads an explicit
  `sqrtF : F → Option F` — like `endoInv`'s advice parameters, soundness never
  consults it, and completeness states the coherence it needs.
- PS's advice throws on an impossible root (`unsafeThrow`); the port is total
  (`Option.getD 0`, the pure map falling back to `(0, 0)`) — unreachable for
  honest inputs, where a flagged candidate always has its root.
-/

namespace Snarky.Kimchi

open Snarky Std.Do

variable {F c : Type}

/-- The BW19 `setup()` parameters (PS `GroupMapParams`): the seed `u`, its curve
image `f(u) = u³ + b`, the square-root and inverse constants, the curve constant,
and a known quadratic non-residue for the flagged-root trick. -/
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

/-- The three candidate abscissae (PS `potentialXs`): one of them is the abscissa
of a curve point — Shallue–van de Woestijne's theorem, which the laws take as a
hypothesis rather than prove. Division is the field's total one (`0⁻¹ = 0`),
matching the gadget's `div`. -/
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

/-- The curve's ordinate square `x³ + b` (PS's local `ySquared`): the per-candidate
test value — `groupMapPure`'s branch scrutinee and the completeness law's SvdW
vocabulary. -/
def ySquared [Field F] (params : GroupMapParams F) (x : F) : F :=
  x * x * x + params.b

/-- The pure map (PS `groupMap`): the first candidate whose ordinate square has a
root under `sqrtF`, as a coordinate pair. The no-candidate branch returns `(0, 0)`
(PS throws) — unreachable when some candidate is a square and `sqrtF` is total on
squares. -/
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

/-- In-circuit square root with a residuosity flag (PS `sqrtFlagged`): witness the
flag, select the operand or its non-residue twist, witness a root, and pin it with
one `square` row — `y² = if isQR then x else nonResidue·x`. -/
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

/-- The in-circuit BW19 map (PS `groupMapCircuit`): the candidate abscissae from
seven `mul`s and one `div`, a flagged root per candidate, at least one flag
asserted set, and the first-flagged candidate selected by mutually exclusive
boolean products. -/
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
(`y² = x³ + b`) whose abscissa is one of the three `potentialXs` candidates at the
operand: the constraints force a set flag, the first-flag selectors are mutually
exclusive boolean products, and the selected branch's `sqrtFlagged` root is the
ordinate. The advice is universally quantified — soundness never consults it. -/
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

/-! ## Completeness

The honest run, step by step in the DSL's reading currency: each gate's law takes its
operands' readings and gives the result's, and `CircuitType.ReadsAs.mono` carries a
reading past the gates that follow. -/

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
  refine Complete.bind
    (Complete.imp (fun _ h => ⟨⟨h, h⟩, h⟩) (fun _ _ h => h)
      (Complete.frame Mono.readsAs (mul_complete (c := c) x x xv xv)))
    fun xSq => Complete.bind (mul_complete (c := c) xSq x (xv * xv) xv)
      fun xCu => Complete.pure_of fun st h =>
        ⟨CircuitType.scoped_fvar.mpr
            (CVar.Scoped.add_ (CircuitType.scoped_fvar.mp h.1) trivial),
          CircuitType.reads_fvar.mpr (by
            rw [CVar.val_add_, CircuitType.reads_fvar.mp h.2]; rfl)⟩

/-- **The flagged root's honest run.** With genuine roots, and a rootless operand's
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
      (Complete.frame Mono.readsAs
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
      (Complete.frame Mono.readsAs
        (selectField_complete (c := c) isQR x (CVar.scale_ nonResidue x)
          (sqrtF xv).isSome xv (nonResidue * xv))))
    fun xOrMx => ?_
  -- the root
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?rrun, h⟩) (fun _ _ h => h)
      (Complete.frame (Mono.and Mono.readsAs Mono.readsAs)
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
      (Complete.frame (Mono.and Mono.readsAs Mono.readsAs)
        (assertSquare_complete (c := c) sqrtVal xOrMx _ _ hsq)))
    fun _ => Complete.pure_of fun _ h => ⟨h.2.2, h.2.1⟩

/-- At least one flag set makes the asserted flag sum nonzero — where the characteristic
is neither `2` nor `3`, which is what prices the sums `2` and `3`. -/
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
The hypotheses: the operand reads a value whose `alphaInv` product is nonzero (the `div`
divisor); some candidate's ordinate square has a root — Shallue–van de Woestijne, taken
as a hypothesis; `sqrtF`'s roots are genuine; a rootless value's non-residue twist has a
root; and `2, 3 ≠ 0` price the flag-sum assertion. -/
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
  -- the raw↔spec identifications: the arithmetic residue of the deferred style,
  -- hoisted above the walk so the leaked VCs capture them too
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

`Poseidon.GroupMap.toGroup` is the map the kimchi verifier actually runs: the executable
IPA wire verifier derives the per-proof `U` base with it (`Bulletproof/Wire.lean`), and
the knowledge-soundness capstones quote it. This section takes it as the circuit's
specification, in the canonical `ZMod q` world (`Fact q.Prime`) the deployed Pasta specs
live in: `GroupMapParams.ofSpec` reads a wire `Spec` as this module's parameter record,
`groupMapPure_toGroup` identifies the module's pure model with the wire map, and the two
laws below restate soundness against the wire curve predicate (`OnCurve`) and
completeness against `toGroup` itself, the advice instantiated with the spec's own
Tonelli–Shanks root and its coherence hypotheses discharged. -/

section Wire

open CompElliptic.Fields CompElliptic.CurveForms.ShortWeierstrass

variable {q : ℕ} [Fact q.Prime]

/-- This module's parameters, read off a wire `Poseidon.GroupMap.Spec` — plus the
non-residue the in-circuit flagged-root trick needs, which the wire map has no
counterpart for (it retries candidates instead of certifying failures). -/
def GroupMapParams.ofSpec (spec : _root_.Poseidon.GroupMap.Spec q) (nonResidue : ZMod q) :
    GroupMapParams (ZMod q) where
  u := spec.u
  fu := spec.fu
  sqrtNeg3U2MinusUOver2 := spec.sqrtNegThreeUSquaredMinusUOver2
  sqrtNeg3U2 := spec.sqrtNegThreeUSquared
  inv3U2 := spec.invThreeUSquared
  b := spec.E.B
  nonResidue := nonResidue

/-- The candidate abscissae agree with the wire map's: `potentialXs` at `ofSpec` is
`Poseidon.GroupMap.potentialXs`. -/
theorem potentialXs_ofSpec (spec : _root_.Poseidon.GroupMap.Spec q)
    (nonResidue t : ZMod q) :
    potentialXs (.ofSpec spec nonResidue) t
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
theorem ySquared_ofSpec (spec : _root_.Poseidon.GroupMap.Spec q)
    (nonResidue x : ZMod q) :
    ySquared (.ofSpec spec nonResidue) x = _root_.Poseidon.GroupMap.curveEqn spec x := by
  simp only [ySquared, _root_.Poseidon.GroupMap.curveEqn, GroupMapParams.ofSpec]
  ring

/-- **The wire identification**: at a wire `Spec`, with the spec's own Tonelli–Shanks
root as advice, the module's pure model computes the wire map's point — coordinate for
coordinate, first-flagged candidate for first-flagged candidate. -/
theorem groupMapPure_toGroup (spec : _root_.Poseidon.GroupMap.Spec q)
    (nonResidue t : ZMod q) :
    groupMapPure spec.sqrt.sqrt? (.ofSpec spec nonResidue) t
      = ((_root_.Poseidon.GroupMap.toGroup spec t).x,
          (_root_.Poseidon.GroupMap.toGroup spec t).y) := by
  have hys : ∀ x : ZMod q,
      spec.sqrt.sqrt? (ySquared (GroupMapParams.ofSpec spec nonResidue) x)
        = _root_.Poseidon.GroupMap.getY spec x := fun x => by
    rw [ySquared_ofSpec, _root_.Poseidon.GroupMap.getY]
  rcases hg : _root_.Poseidon.GroupMap.toGroup spec t with ⟨px, py, hval⟩
  simp only [_root_.Poseidon.GroupMap.toGroup] at hg
  split at hg <;> [skip; split at hg <;> [skip; split at hg]] <;>
    obtain ⟨rfl, rfl⟩ : _ ∧ _ := ⟨congrArg SWPoint.x hg, congrArg SWPoint.y hg⟩ <;>
    simp [groupMapPure, potentialXs_ofSpec, *]

/-- A rootless value's non-residue twist has a root: two non-squares multiply to a
square (`FiniteField.pow_dichotomy`), and `sqrt?` is complete on squares. The discharge
of `groupMapCircuit_complete_spec`'s twist hypothesis at a genuine Tonelli–Shanks
root. -/
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
/-- **Wire-level soundness**: any satisfying valuation reads the result as a point of the
wire spec's curve — `OnCurve`, the verifier's own predicate — at one of the SvdW candidate
abscissae. The advice is universally quantified: soundness never consults it. -/
theorem groupMapCircuit_onCurve_spec {V : Valuation (ZMod q)} {c : Type}
    [BasicSystem (ZMod q) c] [ConstraintHolds (ZMod q) c] [LawfulBasicSystem (ZMod q) c]
    (spec : _root_.Poseidon.GroupMap.Spec q) (nonResidue : ZMod q)
    (sqrtF : ZMod q → Option (ZMod q)) (t : FVar (ZMod q)) :
    ⦃⌜True⌝⦄
    groupMapCircuit (c := Builder V c) sqrtF (.ofSpec spec nonResidue) t
    ⦃⇓ r _ => ⌜(r.x.val V = (potentialXs (.ofSpec spec nonResidue) (t.val V)).1 ∨
        r.x.val V = (potentialXs (.ofSpec spec nonResidue) (t.val V)).2.1 ∨
        r.x.val V = (potentialXs (.ofSpec spec nonResidue) (t.val V)).2.2) ∧
      OnCurve spec.E.A spec.E.B (r.x.val V, r.y.val V)⌝⦄ := by
  intro nv h hsat
  obtain ⟨hx, hy⟩ := groupMapCircuit_spec (c := c) (V := V) sqrtF
    (.ofSpec spec nonResidue) t nv h hsat
  refine ⟨hx, ?_⟩
  show _ ^ 2 = _ ^ 3 + spec.E.A * _ + spec.E.B
  rw [spec.hA]
  simp only [ySquared] at hy
  rw [show ((GroupMapParams.ofSpec spec nonResidue).b : ZMod q) = spec.E.B from rfl] at hy
  linear_combination hy

open WeierstrassCurve.Affine in
/-- **Wire-level completeness**: the honest run lands on the wire map itself — the result
reads `Poseidon.GroupMap.toGroup`, the map the verifier runs to derive the per-proof `U`
base. `groupMapCircuit_complete` at a wire `Spec`: the advice is the spec's own
Tonelli–Shanks root, root-genuineness is `sqrt?_mul_self`, twist-totality is `sqrt?_twist`
at a genuine non-residue, `2 ≠ 0` comes from `q ≠ 2`, and the pure model is rewritten by
`groupMapPure_toGroup`. The SvdW disjunction (as `IsSquare`) and the operand's
nondegeneracy remain, with `q ≠ 3` pricing the flag-sum assertion. -/
theorem groupMapCircuit_toGroup_complete {c : Type} [BasicSystem (ZMod q) c]
    [ConstraintHolds (ZMod q) c] [LawfulBasicSystem (ZMod q) c]
    (spec : _root_.Poseidon.GroupMap.Spec q) (nonResidue : ZMod q) (t : FVar (ZMod q))
    (tv : ZMod q) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hnr0 : nonResidue ≠ 0)
    (hnr : ¬IsSquare nonResidue)
    (hne : (tv * tv + spec.fu) * (tv * tv) ≠ 0)
    (hsq : IsSquare (ySquared (.ofSpec spec nonResidue)
          (potentialXs (.ofSpec spec nonResidue) tv).1) ∨
        IsSquare (ySquared (.ofSpec spec nonResidue)
          (potentialXs (.ofSpec spec nonResidue) tv).2.1) ∨
        IsSquare (ySquared (.ofSpec spec nonResidue)
          (potentialXs (.ofSpec spec nonResidue) tv).2.2)) :
    Complete (F := ZMod q) (c := c)
      (fun st => CircuitType.ReadsAs (val := ZMod q) st t tv)
      (groupMapCircuit (c := c) spec.sqrt.sqrt? (.ofSpec spec nonResidue) t)
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
    groupMapCircuit_complete (c := c) spec.sqrt.sqrt? (.ofSpec spec nonResidue) t tv
      (Ring.two_ne_zero hchar) hthree hne
      (fun a y h => TonelliShanks.sqrt?_mul_self spec.sqrt h)
      (sqrt?_twist spec.sqrt hchar hnr0 hnr)
      (hsq.imp (hsome _) (Or.imp (hsome _) (hsome _))) st ht
  rw [groupMapPure_toGroup] at hx hy
  exact ⟨r, st', hrun, hsat, hx, hy⟩

end Wire

end Snarky.Kimchi
