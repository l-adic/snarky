import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.Assert
import Snarky.Circuit.DSL.Boolean
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

/-! ## The laws

Soundness quotes the module's own pure model: any satisfying valuation reads the
result as an on-curve pair whose abscissa is one of `potentialXs`' three
candidates. Completeness lands on `groupMapPure` — the first-flagged candidate —
under the advice coherence the honest run needs. -/

open Std.Do in
/-- `sqrtFlagged` is sound: the flag reads as a genuine bit and the returned value
squares to the flag-selected operand — `y² = if isQR then x else nonResidue·x`. -/
@[spec] private theorem sqrtFlagged_spec {V : Valuation F} [Field F] [DecidableEq F] {c : Type}
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (sqrtF : F → Option F) (nonResidue : F) (x : FVar F) :
    ⦃⌜True⌝⦄
    (sqrtFlagged (c := Builder V c) sqrtF nonResidue x)
    ⦃⇓ r _ => ⌜∃ bb : Bool, (↑r.2 : CVar F).val V = bit bb ∧
          r.1.val V * r.1.val V
            = (if bb then x.val V else nonResidue * x.val V)⌝⦄ := by
  simp only [sqrtFlagged]
  mvcgen
  rename_i isQR _ hbool xOrMx _ hsel sqrtVal _ _ _ _ hsq
  rcases hbool with h0 | h1
  · refine ⟨false, by simpa [bit] using h0, ?_⟩
    rw [hsq, hsel false (by simpa [bit] using h0)]
    simp [selectPure, CVar.val_scale_]
  · refine ⟨true, by simpa [bit] using h1, ?_⟩
    rw [hsq, hsel true (by simpa [bit] using h1)]
    simp [selectPure]

/-- The state and result of `sqrtFlagged`'s honest run: the flag witnessed at the
counter, the `select` run, the root witnessed at the selected operand. -/
private def sqrtFlaggedRun [Field F] [DecidableEq F] (sqrtF : F → Option F) (nonResidue : F)
    (st : ProverState F) (x : FVar F) : ProverState F × (FVar F × BoolVar F) :=
  let st₁ := st.extendMany [bit (sqrtF (x.val st.env.toValuation)).isSome]
  let isQR : BoolVar F := .unchecked (.var st.nv)
  let r := selectRun st₁ isQR x (CVar.scale_ nonResidue x)
  let st₂ := r.1.extendMany [(sqrtF (r.2.val r.1.env.toValuation)).getD 0]
  (st₂, (.var r.1.nv, isQR))

/-- `sqrtFlagged`'s honest run on an in-scope operand lands at `sqrtFlaggedRun`, when
`sqrtF`'s roots are genuine and a rootless operand's non-residue twist has a root. -/
private theorem sqrtFlagged_run [Field F] [DecidableEq F] {c : Type}
    [BasicSystem F c] [Checker F c] [LawfulChecker F c]
    (sqrtF : F → Option F) (nonResidue : F) {x : FVar F} (st : ProverState F) (hx : x.Scoped st)
    (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : sqrtF (x.val st.env.toValuation) = none →
      (sqrtF (nonResidue * x.val st.env.toValuation)).isSome) :
    prove (Checker.holds (F := F) (c := c)) (sqrtFlagged (c := c) sqrtF nonResidue x) st.nv st.env
      = .ok ((sqrtFlaggedRun sqrtF nonResidue st x).1.out
          (sqrtFlaggedRun sqrtF nonResidue st x).2) := by
  generalize hG : sqrtFlaggedRun sqrtF nonResidue st x = G
  unfold sqrtFlaggedRun at hG
  extract_lets +lift st₁ isQR r st₂ at hG
  subst hG
  simp only [sqrtFlagged, prove_bind]
  rw [prove_witness_run (w := isQRWit sqrtF x) st (.bind (.readCVar hx) fun _ => trivial)
    (v := (sqrtF (x.val st.env.toValuation)).isSome) (by simp [isQRWit, Except.bind])]
  simp only [valueToFields_bool_toList, fieldsToVar_bool_alloc, Except.bind]
  have hle₁ : st.env.Le st₁.env := st.le_extendMany _
  have hb₁ : (↑isQR : CVar F).Scoped st₁ := ProverState.mem_extendMany_head ..
  have hbv₁ : (↑isQR : CVar F).val st₁.env.toValuation
      = bit (sqrtF (x.val st.env.toValuation)).isSome := ProverState.get_extendMany_head ..
  have hx₁ : x.Scoped st₁ := hx.of_le hle₁
  rw [select_run (bb := (sqrtF (x.val st.env.toValuation)).isSome) st₁ hb₁ hx₁ (hx₁.scale_ _) hbv₁,
    show selectRun st₁ isQR x (CVar.scale_ nonResidue x) = r from rfl]
  simp only [Except.bind]
  have hr : Grants F st₁ r (selectPure (sqrtF (x.val st.env.toValuation)).isSome
      (x.val st₁.env.toValuation) ((CVar.scale_ nonResidue x).val st₁.env.toValuation)) :=
    selectRun_grants (bb := (sqrtF (x.val st.env.toValuation)).isSome) hb₁ hx₁
      (hx₁.scale_ nonResidue) hbv₁
  have hrv : r.2.val r.1.env.toValuation
      = selectPure (sqrtF (x.val st.env.toValuation)).isSome (x.val st.env.toValuation)
        (nonResidue * x.val st.env.toValuation) := by
    rw [hr.fvar_val, CVar.val_of_le hle₁ hx, CVar.val_scale_, CVar.val_of_le hle₁ hx]
  clear_value r
  rw [prove_witness_run (w := sqrtWit sqrtF r.2) r.1 (.bind (.readCVar hr.fvar_scoped) fun _ => trivial)
    (v := (sqrtF (r.2.val r.1.env.toValuation)).getD 0) (by simp [sqrtWit, Except.bind])]
  simp only [valueToFields_fvar_toList, fieldsToVar_fvar_alloc, Except.bind]
  have hle₂ : r.1.env.Le st₂.env := r.1.le_extendMany _
  rw [assertSquare_run st₂ (show (CVar.var r.1.nv).Scoped st₂ from ProverState.mem_extendMany_head ..)
    (hr.fvar_scoped.of_le hle₂) ?_]
  · rfl
  · rw [CVar.val_of_le hle₂ hr.fvar_scoped, hrv]
    show (st₂.env.toValuation r.1.nv) * (st₂.env.toValuation r.1.nv) = _
    rw [show st₂.env.toValuation r.1.nv = (sqrtF (r.2.val r.1.env.toValuation)).getD 0 from
      ProverState.get_extendMany_head .., hrv]
    rcases hc : sqrtF (x.val st.env.toValuation) with _ | y
    · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (htwist hc)
      simp [selectPure, hz, hroot _ z hz]
    · simp [selectPure, hc, hroot _ y hc]

/-- `sqrtFlaggedRun` grows the table; the root and the flag are in scope at the state
after; the flag reads the operand's residuosity and the root reads the advice's root of
the flag-selected operand. -/
private theorem sqrtFlaggedRun_grants [Field F] [DecidableEq F] (sqrtF : F → Option F)
    (nonResidue : F) {st : ProverState F} {x : FVar F} (hx : x.Scoped st) :
    st.env.Le (sqrtFlaggedRun sqrtF nonResidue st x).1.env ∧
      (sqrtFlaggedRun sqrtF nonResidue st x).2.1.Scoped (sqrtFlaggedRun sqrtF nonResidue st x).1 ∧
      (↑(sqrtFlaggedRun sqrtF nonResidue st x).2.2 : CVar F).Scoped
        (sqrtFlaggedRun sqrtF nonResidue st x).1 ∧
      (↑(sqrtFlaggedRun sqrtF nonResidue st x).2.2 : CVar F).val
          (sqrtFlaggedRun sqrtF nonResidue st x).1.env.toValuation
        = bit (sqrtF (x.val st.env.toValuation)).isSome ∧
      (sqrtFlaggedRun sqrtF nonResidue st x).2.1.val
          (sqrtFlaggedRun sqrtF nonResidue st x).1.env.toValuation
        = (sqrtF (if (sqrtF (x.val st.env.toValuation)).isSome then x.val st.env.toValuation
            else nonResidue * x.val st.env.toValuation)).getD 0 := by
  generalize hG : sqrtFlaggedRun sqrtF nonResidue st x = G
  unfold sqrtFlaggedRun at hG
  extract_lets +lift st₁ isQR r st₂ at hG
  subst hG
  have hle₁ : st.env.Le st₁.env := st.le_extendMany _
  have hb₁ : (↑isQR : CVar F).Scoped st₁ := ProverState.mem_extendMany_head ..
  have hbv₁ : (↑isQR : CVar F).val st₁.env.toValuation
      = bit (sqrtF (x.val st.env.toValuation)).isSome := ProverState.get_extendMany_head ..
  have hx₁ : x.Scoped st₁ := hx.of_le hle₁
  have hr : Grants F st₁ r (selectPure (sqrtF (x.val st.env.toValuation)).isSome
      (x.val st₁.env.toValuation) ((CVar.scale_ nonResidue x).val st₁.env.toValuation)) :=
    selectRun_grants (bb := (sqrtF (x.val st.env.toValuation)).isSome) hb₁ hx₁
      (hx₁.scale_ nonResidue) hbv₁
  have hrv : r.2.val r.1.env.toValuation
      = selectPure (sqrtF (x.val st.env.toValuation)).isSome (x.val st.env.toValuation)
        (nonResidue * x.val st.env.toValuation) := by
    rw [hr.fvar_val, CVar.val_of_le hle₁ hx, CVar.val_scale_, CVar.val_of_le hle₁ hx]
  clear_value r
  have hle₂ : r.1.env.Le st₂.env := r.1.le_extendMany _
  refine ⟨hle₁.trans (hr.le.trans hle₂), ProverState.mem_extendMany_head ..,
    hb₁.of_le (hr.le.trans hle₂), ?_, ?_⟩
  · rw [CVar.val_of_le (hr.le.trans hle₂) hb₁, hbv₁]
  · show st₂.env.toValuation r.1.nv = _
    rw [show st₂.env.toValuation r.1.nv = (sqrtF (r.2.val r.1.env.toValuation)).getD 0 from
      ProverState.get_extendMany_head .., hrv, selectPure]

open Std.Do in
/-- `groupMapCircuit` is sound: any satisfying valuation reads the result as an
on-curve pair (`y² = x³ + b`) whose abscissa is one of the three `potentialXs`
candidates at the operand — the constraints force a set flag, the first-flag
selectors are mutually exclusive boolean products, and the selected branch's
`sqrtFlagged` root is the ordinate. The advice `sqrtF` is universally quantified:
soundness never consults it. -/
theorem groupMapCircuit_spec {V : Valuation F} [Field F] [DecidableEq F]
    (sqrtF : F → Option F) (params : GroupMapParams F) (t : FVar F) :
    ⦃⌜True⌝⦄
    (groupMapCircuit (c := Builder V (KimchiConstraint F)) sqrtF params t)
    ⦃⇓ r _ => ⌜(r.x.val V = (potentialXs params (t.val V)).1
          ∨ r.x.val V = (potentialXs params (t.val V)).2.1
          ∨ r.x.val V = (potentialXs params (t.val V)).2.2) ∧
        r.y.val V * r.y.val V
          = r.x.val V * r.x.val V * r.x.val V + params.b⌝⦄ := by
  simp only [groupMapCircuit]
  mvcgen
  rename_i t2 _ ht2 alphaInv _ halphaInv alpha _ halpha t4 _ ht4 t4Alpha _ ht4Alpha temp1 _
    htemp1 t2Inv _ ht2Inv t2PlusFuSq _ ht2PlusFuSq temp2a _ htemp2a temp2 _ htemp2 xSq1 _ hxSq1
    xCu1 _ hxCu1 sf1 _ hsf1 xSq2 _ hxSq2 xCu2 _ hxCu2 sf2 _ hsf2 xSq3 _ hxSq3 xCu3 _ hxCu3 sf3 _
    hsf3 _ _ hnz x2First _ hx2First nb2AndB3 _ hnb2AndB3 x3First _ hx3First t3y _ ht3y t2y _
    ht2y t1y _ ht1y t3x _ ht3x t2x _ ht2x t1x _ ht1x
  obtain ⟨bb1, hb1, hy1⟩ := hsf1
  obtain ⟨bb2, hb2, hy2⟩ := hsf2
  obtain ⟨bb3, hb3, hy3⟩ := hsf3
  -- the candidate values, from the arithmetic grants
  have hval : ∀ (a : F), (CVar.const a : CVar F).val V = a := fun _ => rfl
  have hx1v : (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) temp1).val V
      = (potentialXs params (t.val V)).1 := by
    simp only [potentialXs, CVar.val_sub_, hval, htemp1, ht4Alpha, ht4, halpha,
      halphaInv, ht2, CVar.val_add_]
  have hx2v : (CVar.sub_ (.const (-params.u))
        (CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) temp1)).val V
      = (potentialXs params (t.val V)).2.1 := by
    simp only [potentialXs, CVar.val_sub_, hval, htemp1, ht4Alpha, ht4, halpha,
      halphaInv, ht2, CVar.val_add_]
  have hx3v : (CVar.sub_ (.const params.u) temp2).val V
      = (potentialXs params (t.val V)).2.2 := by
    simp only [potentialXs, CVar.val_sub_, hval, htemp2, htemp2a, ht2PlusFuSq,
      ht2Inv, halpha, halphaInv, ht2, CVar.val_add_]
  -- the flag bits force exactly one first-flag selector
  have hnb1 : (↑(Snarky.not sf1.2) : CVar F).val V = bit (!bb1) := by
    rcases bb1 <;> simp [Snarky.not, circuitVal, CVar.val, hb1, bit]
  have hnb2 : (↑(Snarky.not sf2.2) : CVar F).val V = bit (!bb2) := by
    rcases bb2 <;> simp [Snarky.not, circuitVal, CVar.val, hb2, bit]
  have hs2 := hx2First (!bb1) bb2 hnb1 hb2
  have hs3 := hx3First (!bb1) (!bb2 && bb3) hnb1 (hnb2AndB3 (!bb2) bb3 hnb2 hb3)
  -- select the branch: the sums collapse under the selector bits
  rcases bb1 with _ | _
  · rcases bb2 with _ | _
    · rcases bb3 with _ | _
      · -- all flags clear: the asserted flag sum is zero
        exact absurd (by simp [circuitVal, hb1, hb2, hb3, bit]) hnz
      · -- third candidate
        refine ⟨Or.inr (Or.inr ?_), ?_⟩
        · rw [← hx3v]
          simp [circuitVal, CVar.val, ht1x, ht2x, ht3x, hb1, hs2, hs3, bit]
        · simpa [circuitVal, CVar.val, ht1x, ht2x, ht3x, ht1y, ht2y, ht3y, hb1,
            hs2, hs3, bit, hxCu3, hxSq3] using hy3
    · -- second candidate
      refine ⟨Or.inr (Or.inl ?_), ?_⟩
      · rw [← hx2v]
        simp [circuitVal, CVar.val, ht1x, ht2x, ht3x, hb1, hs2, hs3, bit]
      · simpa [circuitVal, CVar.val, ht1x, ht2x, ht3x, ht1y, ht2y, ht3y, hb1,
          hs2, hs3, bit, hxCu2, hxSq2] using hy2
  · -- first candidate, whatever the later flags
    refine ⟨Or.inl ?_, ?_⟩
    · rw [← hx1v]
      simp [circuitVal, CVar.val, ht1x, ht2x, ht3x, hb1, hs2, hs3, bit]
    · simpa [circuitVal, CVar.val, ht1x, ht2x, ht3x, ht1y, ht2y, ht3y, hb1,
        hs2, hs3, bit, hxCu1, hxSq1] using hy1

/-- The state and result of `groupMapCircuit`'s honest run: the candidate abscissae's
seven `mul`s and one `div`, the three flagged roots, the flag sum's `inv`, the three
selector `and`s, and the six selection `mul`s — each at the state the previous left. -/
def groupMapCircuitRun [Field F] [DecidableEq F] (sqrtF : F → Option F)
    (params : GroupMapParams F) (st : ProverState F) (t : FVar F) :
    ProverState F × AffinePoint (FVar F) :=
  let r1 := mulRun st t t
  let tpf := CVar.add_ r1.2 (.const params.fu)
  let r2 := mulRun r1.1 tpf r1.2
  let r3 := divRun r2.1 (.const 1) r2.2
  let r4 := mulRun r3.1 r1.2 r1.2
  let r5 := mulRun r4.1 r4.2 r3.2
  let r6 := mulRun r5.1 r5.2 (.const params.sqrtNeg3U2)
  let x1 := CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) r6.2
  let x2 := CVar.sub_ (.const (-params.u)) x1
  let r7 := mulRun r6.1 r3.2 tpf
  let r8 := mulRun r7.1 tpf tpf
  let r9 := mulRun r8.1 r8.2 r7.2
  let r10 := mulRun r9.1 r9.2 (.const params.inv3U2)
  let x3 := CVar.sub_ (.const params.u) r10.2
  let r11 := mulRun r10.1 x1 x1
  let r12 := mulRun r11.1 r11.2 x1
  let s1 := sqrtFlaggedRun sqrtF params.nonResidue r12.1 (CVar.add_ r12.2 (.const params.b))
  let r13 := mulRun s1.1 x2 x2
  let r14 := mulRun r13.1 r13.2 x2
  let s2 := sqrtFlaggedRun sqrtF params.nonResidue r14.1 (CVar.add_ r14.2 (.const params.b))
  let r15 := mulRun s2.1 x3 x3
  let r16 := mulRun r15.1 r15.2 x3
  let s3 := sqrtFlaggedRun sqrtF params.nonResidue r16.1 (CVar.add_ r16.2 (.const params.b))
  let rNZ := invRun s3.1 (CVar.add_ (CVar.add_ ↑s1.2.2 ↑s2.2.2) ↑s3.2.2)
  let nb1 := Snarky.not s1.2.2
  let a1 := andRun rNZ.1 nb1 s2.2.2
  let a2 := andRun a1.1 (Snarky.not s2.2.2) s3.2.2
  let a3 := andRun a2.1 nb1 a2.2
  let m1 := mulRun a3.1 ↑a3.2 s3.2.1
  let m2 := mulRun m1.1 ↑a1.2 s2.2.1
  let m3 := mulRun m2.1 ↑s1.2.2 s1.2.1
  let m4 := mulRun m3.1 ↑a3.2 x3
  let m5 := mulRun m4.1 ↑a1.2 x2
  let m6 := mulRun m5.1 ↑s1.2.2 x1
  (m6.1, ⟨CVar.add_ (CVar.add_ m6.2 m5.2) m4.2, CVar.add_ (CVar.add_ m3.2 m2.2) m1.2⟩)

/-- `groupMapPure`, branch by branch: the first candidate whose ordinate square has a
root under `sqrtF`, with that root. -/
private theorem groupMapPure_eq [Field F] (sqrtF : F → Option F) (params : GroupMapParams F)
    (t : F) :
    groupMapPure sqrtF params t =
      if (sqrtF (ySquared params (potentialXs params t).1)).isSome then
        ((potentialXs params t).1, (sqrtF (ySquared params (potentialXs params t).1)).getD 0)
      else if (sqrtF (ySquared params (potentialXs params t).2.1)).isSome then
        ((potentialXs params t).2.1, (sqrtF (ySquared params (potentialXs params t).2.1)).getD 0)
      else if (sqrtF (ySquared params (potentialXs params t).2.2)).isSome then
        ((potentialXs params t).2.2, (sqrtF (ySquared params (potentialXs params t).2.2)).getD 0)
      else (0, 0) := by
  rcases h : potentialXs params t with ⟨x1, x2, x3⟩
  simp only [groupMapPure, h]
  rcases hc1 : sqrtF (ySquared params x1) with _ | y1 <;>
    rcases hc2 : sqrtF (ySquared params x2) with _ | y2 <;>
    rcases hc3 : sqrtF (ySquared params x3) with _ | y3 <;>
    simp [hc1, hc2, hc3]

/-- `groupMapCircuitRun`, step by step: each run named, its operands in scope at its
state, and its grant in closed form — the candidate values, the three flags and roots, the
selector bits, the selection products — plus the flag sum's reading. -/
private theorem run_facts [Field F] [DecidableEq F] (sqrtF : F → Option F)
    (params : GroupMapParams F) {st : ProverState F} {t : FVar F} (ht : t.Scoped st) :
    ∃ (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ProverState F × FVar F)
      (s1 : ProverState F × (FVar F × BoolVar F)) (r13 r14 : ProverState F × FVar F)
      (s2 : ProverState F × (FVar F × BoolVar F)) (r15 r16 : ProverState F × FVar F)
      (s3 : ProverState F × (FVar F × BoolVar F)) (rNZ : ProverState F × FVar F)
      (a1 a2 a3 : ProverState F × BoolVar F) (m1 m2 m3 m4 m5 m6 : ProverState F × FVar F),
      groupMapCircuitRun sqrtF params st t = (m6.1, ⟨CVar.add_ (CVar.add_ m6.2 m5.2) m4.2, CVar.add_ (CVar.add_ m3.2 m2.2) m1.2⟩) ∧
      (mulRun st t t = r1 ∧ (t).Scoped st ∧ (t).Scoped st ∧
        Grants F st r1 (t.val st.env.toValuation * t.val st.env.toValuation)) ∧
      (mulRun r1.1 (CVar.add_ r1.2 (CVar.const params.fu)) r1.2 = r2 ∧ (CVar.add_ r1.2 (CVar.const params.fu)).Scoped r1.1 ∧ (r1.2).Scoped r1.1 ∧
        Grants F r1.1 r2 ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation))) ∧
      (divRun r2.1 (CVar.const 1) r2.2 = r3 ∧ ((CVar.const 1 : CVar F)).Scoped r2.1 ∧ (r2.2).Scoped r2.1 ∧
        Grants F r2.1 r3 (1 / ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation)))) ∧
      (mulRun r3.1 r1.2 r1.2 = r4 ∧ (r1.2).Scoped r3.1 ∧ (r1.2).Scoped r3.1 ∧
        Grants F r3.1 r4 ((t.val st.env.toValuation * t.val st.env.toValuation) * (t.val st.env.toValuation * t.val st.env.toValuation))) ∧
      (mulRun r4.1 r4.2 r3.2 = r5 ∧ (r4.2).Scoped r4.1 ∧ (r3.2).Scoped r4.1 ∧
        Grants F r4.1 r5 ((t.val st.env.toValuation * t.val st.env.toValuation) * (t.val st.env.toValuation * t.val st.env.toValuation) * (1 / ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation))))) ∧
      (mulRun r5.1 r5.2 (CVar.const params.sqrtNeg3U2) = r6 ∧ (r5.2).Scoped r5.1 ∧ ((CVar.const params.sqrtNeg3U2 : CVar F)).Scoped r5.1 ∧
        Grants F r5.1 r6 ((t.val st.env.toValuation * t.val st.env.toValuation) * (t.val st.env.toValuation * t.val st.env.toValuation) * (1 / ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation))) * params.sqrtNeg3U2)) ∧
      (mulRun r6.1 r3.2 (CVar.add_ r1.2 (CVar.const params.fu)) = r7 ∧ (r3.2).Scoped r6.1 ∧ (CVar.add_ r1.2 (CVar.const params.fu)).Scoped r6.1 ∧
        Grants F r6.1 r7 ((1 / ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation))) * (t.val st.env.toValuation * t.val st.env.toValuation + params.fu))) ∧
      (mulRun r7.1 (CVar.add_ r1.2 (CVar.const params.fu)) (CVar.add_ r1.2 (CVar.const params.fu)) = r8 ∧ (CVar.add_ r1.2 (CVar.const params.fu)).Scoped r7.1 ∧ (CVar.add_ r1.2 (CVar.const params.fu)).Scoped r7.1 ∧
        Grants F r7.1 r8 ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation + params.fu))) ∧
      (mulRun r8.1 r8.2 r7.2 = r9 ∧ (r8.2).Scoped r8.1 ∧ (r7.2).Scoped r8.1 ∧
        Grants F r8.1 r9 ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * ((1 / ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation))) * (t.val st.env.toValuation * t.val st.env.toValuation + params.fu)))) ∧
      (mulRun r9.1 r9.2 (CVar.const params.inv3U2) = r10 ∧ (r9.2).Scoped r9.1 ∧ ((CVar.const params.inv3U2 : CVar F)).Scoped r9.1 ∧
        Grants F r9.1 r10 ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * ((1 / ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation))) * (t.val st.env.toValuation * t.val st.env.toValuation + params.fu)) * params.inv3U2)) ∧
      (mulRun r10.1 (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2) = r11 ∧ (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).Scoped r10.1 ∧ (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).Scoped r10.1 ∧
        Grants F r10.1 r11 ((potentialXs params (t.val st.env.toValuation)).1 * (potentialXs params (t.val st.env.toValuation)).1)) ∧
      (mulRun r11.1 r11.2 (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2) = r12 ∧ (r11.2).Scoped r11.1 ∧ (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).Scoped r11.1 ∧
        Grants F r11.1 r12 ((potentialXs params (t.val st.env.toValuation)).1 * (potentialXs params (t.val st.env.toValuation)).1 * (potentialXs params (t.val st.env.toValuation)).1)) ∧
      (sqrtFlaggedRun sqrtF params.nonResidue r12.1 (CVar.add_ r12.2 (CVar.const params.b)) = s1 ∧ (CVar.add_ r12.2 (CVar.const params.b)).Scoped r12.1 ∧
        (r12.1.env.Le s1.1.env ∧ s1.2.1.Scoped s1.1 ∧ (↑s1.2.2 : CVar F).Scoped s1.1 ∧
          (↑s1.2.2 : CVar F).val s1.1.env.toValuation = bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome ∧
          s1.2.1.val s1.1.env.toValuation = (sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).1 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).1)).getD 0)) ∧
      (mulRun s1.1 (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)) (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)) = r13 ∧ (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)).Scoped s1.1 ∧ (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)).Scoped s1.1 ∧
        Grants F s1.1 r13 ((potentialXs params (t.val st.env.toValuation)).2.1 * (potentialXs params (t.val st.env.toValuation)).2.1)) ∧
      (mulRun r13.1 r13.2 (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)) = r14 ∧ (r13.2).Scoped r13.1 ∧ (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)).Scoped r13.1 ∧
        Grants F r13.1 r14 ((potentialXs params (t.val st.env.toValuation)).2.1 * (potentialXs params (t.val st.env.toValuation)).2.1 * (potentialXs params (t.val st.env.toValuation)).2.1)) ∧
      (sqrtFlaggedRun sqrtF params.nonResidue r14.1 (CVar.add_ r14.2 (CVar.const params.b)) = s2 ∧ (CVar.add_ r14.2 (CVar.const params.b)).Scoped r14.1 ∧
        (r14.1.env.Le s2.1.env ∧ s2.2.1.Scoped s2.1 ∧ (↑s2.2.2 : CVar F).Scoped s2.1 ∧
          (↑s2.2.2 : CVar F).val s2.1.env.toValuation = bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome ∧
          s2.2.1.val s2.1.env.toValuation = (sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).2.1 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).getD 0)) ∧
      (mulRun s2.1 (CVar.sub_ (CVar.const params.u) r10.2) (CVar.sub_ (CVar.const params.u) r10.2) = r15 ∧ (CVar.sub_ (CVar.const params.u) r10.2).Scoped s2.1 ∧ (CVar.sub_ (CVar.const params.u) r10.2).Scoped s2.1 ∧
        Grants F s2.1 r15 ((potentialXs params (t.val st.env.toValuation)).2.2 * (potentialXs params (t.val st.env.toValuation)).2.2)) ∧
      (mulRun r15.1 r15.2 (CVar.sub_ (CVar.const params.u) r10.2) = r16 ∧ (r15.2).Scoped r15.1 ∧ (CVar.sub_ (CVar.const params.u) r10.2).Scoped r15.1 ∧
        Grants F r15.1 r16 ((potentialXs params (t.val st.env.toValuation)).2.2 * (potentialXs params (t.val st.env.toValuation)).2.2 * (potentialXs params (t.val st.env.toValuation)).2.2)) ∧
      (sqrtFlaggedRun sqrtF params.nonResidue r16.1 (CVar.add_ r16.2 (CVar.const params.b)) = s3 ∧ (CVar.add_ r16.2 (CVar.const params.b)).Scoped r16.1 ∧
        (r16.1.env.Le s3.1.env ∧ s3.2.1.Scoped s3.1 ∧ (↑s3.2.2 : CVar F).Scoped s3.1 ∧
          (↑s3.2.2 : CVar F).val s3.1.env.toValuation = bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome ∧
          s3.2.1.val s3.1.env.toValuation = (sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).2.2 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).getD 0)) ∧
      (invRun s3.1 (CVar.add_ (CVar.add_ (↑s1.2.2 : CVar F) (↑s2.2.2 : CVar F)) (↑s3.2.2 : CVar F)) = rNZ ∧ (CVar.add_ (CVar.add_ (↑s1.2.2 : CVar F) (↑s2.2.2 : CVar F)) (↑s3.2.2 : CVar F)).Scoped s3.1 ∧
        Grants F s3.1 rNZ ((bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome)⁻¹)) ∧
      (andRun rNZ.1 (Snarky.not s1.2.2) s2.2.2 = a1 ∧ ((↑(Snarky.not s1.2.2) : CVar F)).Scoped rNZ.1 ∧ ((↑s2.2.2 : CVar F)).Scoped rNZ.1 ∧
        Grants F rNZ.1 (a1.1, (↑a1.2 : CVar F)) (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome))) ∧
      (andRun a1.1 (Snarky.not s2.2.2) s3.2.2 = a2 ∧ ((↑(Snarky.not s2.2.2) : CVar F)).Scoped a1.1 ∧ ((↑s3.2.2 : CVar F)).Scoped a1.1 ∧
        Grants F a1.1 (a2.1, (↑a2.2 : CVar F)) (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome))) ∧
      (andRun a2.1 (Snarky.not s1.2.2) a2.2 = a3 ∧ ((↑(Snarky.not s1.2.2) : CVar F)).Scoped a2.1 ∧ ((↑a2.2 : CVar F)).Scoped a2.1 ∧
        Grants F a2.1 (a3.1, (↑a3.2 : CVar F)) (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome)))) ∧
      (mulRun a3.1 ↑a3.2 s3.2.1 = m1 ∧ ((↑a3.2 : CVar F)).Scoped a3.1 ∧ (s3.2.1).Scoped a3.1 ∧
        Grants F a3.1 m1 (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome)) * ((sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).2.2 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).getD 0))) ∧
      (mulRun m1.1 ↑a1.2 s2.2.1 = m2 ∧ ((↑a1.2 : CVar F)).Scoped m1.1 ∧ (s2.2.1).Scoped m1.1 ∧
        Grants F m1.1 m2 (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome) * ((sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).2.1 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).getD 0))) ∧
      (mulRun m2.1 ↑s1.2.2 s1.2.1 = m3 ∧ ((↑s1.2.2 : CVar F)).Scoped m2.1 ∧ (s1.2.1).Scoped m2.1 ∧
        Grants F m2.1 m3 (bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome * ((sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).1 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).1)).getD 0))) ∧
      (mulRun m3.1 ↑a3.2 (CVar.sub_ (CVar.const params.u) r10.2) = m4 ∧ ((↑a3.2 : CVar F)).Scoped m3.1 ∧ (CVar.sub_ (CVar.const params.u) r10.2).Scoped m3.1 ∧
        Grants F m3.1 m4 (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome)) * (potentialXs params (t.val st.env.toValuation)).2.2)) ∧
      (mulRun m4.1 ↑a1.2 (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)) = m5 ∧ ((↑a1.2 : CVar F)).Scoped m4.1 ∧ (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)).Scoped m4.1 ∧
        Grants F m4.1 m5 (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome) * (potentialXs params (t.val st.env.toValuation)).2.1)) ∧
      (mulRun m5.1 ↑s1.2.2 (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2) = m6 ∧ ((↑s1.2.2 : CVar F)).Scoped m5.1 ∧ (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).Scoped m5.1 ∧
        Grants F m5.1 m6 (bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome * (potentialXs params (t.val st.env.toValuation)).1)) ∧
      (CVar.add_ (CVar.add_ (↑s1.2.2 : CVar F) (↑s2.2.2 : CVar F)) (↑s3.2.2 : CVar F)).val s3.1.env.toValuation = bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome := by
  generalize hG : groupMapCircuitRun sqrtF params st t = G
  unfold groupMapCircuitRun at hG
  extract_lets +lift r1 tpf r2 r3 r4 r5 r6 x1 x2 r7 r8 r9 r10 x3 r11 r12 s1 r13 r14 s2 r15 r16 s3
    rNZ nb1 a1 a2 a3 m1 m2 m3 m4 m5 m6 at hG
  subst hG
  have hr1o1 : (t).Scoped st := ht
  have hr1o2 : (t).Scoped st := ht
  have gr1 : Grants F st r1 (t.val st.env.toValuation * t.val st.env.toValuation) := by
    exact mulRun_grants hr1o1 hr1o2
  have l1 : st.env.Le r1.1.env := gr1.le
  have hr2o1 : (CVar.add_ r1.2 (CVar.const params.fu)).Scoped r1.1 := (gr1.fvar_scoped.add_ (CVar.scoped_const _ _))
  have hr2o2 : (r1.2).Scoped r1.1 := gr1.fvar_scoped
  have gr2 : Grants F r1.1 r2 ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation)) := by
    have h := mulRun_grants hr2o1 hr2o2
    rwa [(by rw [CVar.val_add_, gr1.fvar_val]; rfl : (CVar.add_ r1.2 (CVar.const params.fu)).val r1.1.env.toValuation = (t.val st.env.toValuation * t.val st.env.toValuation + params.fu)), gr1.fvar_val] at h
  have l2 : r1.1.env.Le r2.1.env := gr2.le
  have hr3o1 : ((CVar.const 1 : CVar F)).Scoped r2.1 := (CVar.scoped_const _ _)
  have hr3o2 : (r2.2).Scoped r2.1 := gr2.fvar_scoped
  have gr3 : Grants F r2.1 r3 (1 / ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation))) := by
    have h := divRun_grants hr3o1 hr3o2
    rwa [(show (CVar.const 1 : CVar F).val r2.1.env.toValuation = 1 from rfl), gr2.fvar_val] at h
  have l3 : r2.1.env.Le r3.1.env := gr3.le
  have L1_3 : r1.1.env.Le r3.1.env := l2.trans (l3)
  have hr4o1 : (r1.2).Scoped r3.1 := (gr1.fvar_scoped.of_le L1_3)
  have hr4o2 : (r1.2).Scoped r3.1 := (gr1.fvar_scoped.of_le L1_3)
  have gr4 : Grants F r3.1 r4 ((t.val st.env.toValuation * t.val st.env.toValuation) * (t.val st.env.toValuation * t.val st.env.toValuation)) := by
    have h := mulRun_grants hr4o1 hr4o2
    rwa [((CVar.val_of_le L1_3 gr1.fvar_scoped).trans gr1.fvar_val)] at h
  have l4 : r3.1.env.Le r4.1.env := gr4.le
  have hr5o1 : (r4.2).Scoped r4.1 := gr4.fvar_scoped
  have hr5o2 : (r3.2).Scoped r4.1 := (gr3.fvar_scoped.of_le l4)
  have gr5 : Grants F r4.1 r5 ((t.val st.env.toValuation * t.val st.env.toValuation) * (t.val st.env.toValuation * t.val st.env.toValuation) * (1 / ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation)))) := by
    have h := mulRun_grants hr5o1 hr5o2
    rwa [gr4.fvar_val, ((CVar.val_of_le l4 gr3.fvar_scoped).trans gr3.fvar_val)] at h
  have l5 : r4.1.env.Le r5.1.env := gr5.le
  have hr6o1 : (r5.2).Scoped r5.1 := gr5.fvar_scoped
  have hr6o2 : ((CVar.const params.sqrtNeg3U2 : CVar F)).Scoped r5.1 := (CVar.scoped_const _ _)
  have gr6 : Grants F r5.1 r6 ((t.val st.env.toValuation * t.val st.env.toValuation) * (t.val st.env.toValuation * t.val st.env.toValuation) * (1 / ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation))) * params.sqrtNeg3U2) := by
    have h := mulRun_grants hr6o1 hr6o2
    rwa [gr5.fvar_val, (show (CVar.const params.sqrtNeg3U2 : CVar F).val r5.1.env.toValuation = params.sqrtNeg3U2 from rfl)] at h
  have l6 : r5.1.env.Le r6.1.env := gr6.le
  have L3_6 : r3.1.env.Le r6.1.env := l4.trans (l5.trans (l6))
  have L1_6 : r1.1.env.Le r6.1.env := l2.trans (l3.trans (l4.trans (l5.trans (l6))))
  have hr7o1 : (r3.2).Scoped r6.1 := (gr3.fvar_scoped.of_le L3_6)
  have hr7o2 : (CVar.add_ r1.2 (CVar.const params.fu)).Scoped r6.1 := ((gr1.fvar_scoped.add_ (CVar.scoped_const _ _)).of_le L1_6)
  have gr7 : Grants F r6.1 r7 ((1 / ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation))) * (t.val st.env.toValuation * t.val st.env.toValuation + params.fu)) := by
    have h := mulRun_grants hr7o1 hr7o2
    rwa [((CVar.val_of_le L3_6 gr3.fvar_scoped).trans gr3.fvar_val), ((CVar.val_of_le L1_6 (gr1.fvar_scoped.add_ (CVar.scoped_const _ _))).trans (by rw [CVar.val_add_, gr1.fvar_val]; rfl : (CVar.add_ r1.2 (CVar.const params.fu)).val r1.1.env.toValuation = (t.val st.env.toValuation * t.val st.env.toValuation + params.fu)))] at h
  have l7 : r6.1.env.Le r7.1.env := gr7.le
  have L1_7 : r1.1.env.Le r7.1.env := l2.trans (l3.trans (l4.trans (l5.trans (l6.trans (l7)))))
  have hr8o1 : (CVar.add_ r1.2 (CVar.const params.fu)).Scoped r7.1 := ((gr1.fvar_scoped.add_ (CVar.scoped_const _ _)).of_le L1_7)
  have hr8o2 : (CVar.add_ r1.2 (CVar.const params.fu)).Scoped r7.1 := ((gr1.fvar_scoped.add_ (CVar.scoped_const _ _)).of_le L1_7)
  have gr8 : Grants F r7.1 r8 ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation + params.fu)) := by
    have h := mulRun_grants hr8o1 hr8o2
    rwa [((CVar.val_of_le L1_7 (gr1.fvar_scoped.add_ (CVar.scoped_const _ _))).trans (by rw [CVar.val_add_, gr1.fvar_val]; rfl : (CVar.add_ r1.2 (CVar.const params.fu)).val r1.1.env.toValuation = (t.val st.env.toValuation * t.val st.env.toValuation + params.fu)))] at h
  have l8 : r7.1.env.Le r8.1.env := gr8.le
  have hr9o1 : (r8.2).Scoped r8.1 := gr8.fvar_scoped
  have hr9o2 : (r7.2).Scoped r8.1 := (gr7.fvar_scoped.of_le l8)
  have gr9 : Grants F r8.1 r9 ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * ((1 / ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation))) * (t.val st.env.toValuation * t.val st.env.toValuation + params.fu))) := by
    have h := mulRun_grants hr9o1 hr9o2
    rwa [gr8.fvar_val, ((CVar.val_of_le l8 gr7.fvar_scoped).trans gr7.fvar_val)] at h
  have l9 : r8.1.env.Le r9.1.env := gr9.le
  have hr10o1 : (r9.2).Scoped r9.1 := gr9.fvar_scoped
  have hr10o2 : ((CVar.const params.inv3U2 : CVar F)).Scoped r9.1 := (CVar.scoped_const _ _)
  have gr10 : Grants F r9.1 r10 ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * ((1 / ((t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation))) * (t.val st.env.toValuation * t.val st.env.toValuation + params.fu)) * params.inv3U2) := by
    have h := mulRun_grants hr10o1 hr10o2
    rwa [gr9.fvar_val, (show (CVar.const params.inv3U2 : CVar F).val r9.1.env.toValuation = params.inv3U2 from rfl)] at h
  have l10 : r9.1.env.Le r10.1.env := gr10.le
  have L6_10 : r6.1.env.Le r10.1.env := l7.trans (l8.trans (l9.trans (l10)))
  have hr11o1 : (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).Scoped r10.1 := ((CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped).of_le L6_10)
  have hr11o2 : (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).Scoped r10.1 := ((CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped).of_le L6_10)
  have gr11 : Grants F r10.1 r11 ((potentialXs params (t.val st.env.toValuation)).1 * (potentialXs params (t.val st.env.toValuation)).1) := by
    have h := mulRun_grants hr11o1 hr11o2
    rwa [((CVar.val_of_le L6_10 (CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped)).trans (by rw [CVar.val_sub_, gr6.fvar_val]; rfl : (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).val r6.1.env.toValuation = (potentialXs params (t.val st.env.toValuation)).1))] at h
  have l11 : r10.1.env.Le r11.1.env := gr11.le
  have L6_11 : r6.1.env.Le r11.1.env := l7.trans (l8.trans (l9.trans (l10.trans (l11))))
  have hr12o1 : (r11.2).Scoped r11.1 := gr11.fvar_scoped
  have hr12o2 : (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).Scoped r11.1 := ((CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped).of_le L6_11)
  have gr12 : Grants F r11.1 r12 ((potentialXs params (t.val st.env.toValuation)).1 * (potentialXs params (t.val st.env.toValuation)).1 * (potentialXs params (t.val st.env.toValuation)).1) := by
    have h := mulRun_grants hr12o1 hr12o2
    rwa [gr11.fvar_val, ((CVar.val_of_le L6_11 (CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped)).trans (by rw [CVar.val_sub_, gr6.fvar_val]; rfl : (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).val r6.1.env.toValuation = (potentialXs params (t.val st.env.toValuation)).1))] at h
  have l12 : r11.1.env.Le r12.1.env := gr12.le
  have hs1o1 : (CVar.add_ r12.2 (CVar.const params.b)).Scoped r12.1 := (gr12.fvar_scoped.add_ (CVar.scoped_const _ _))
  have gs1 : (r12.1.env.Le s1.1.env ∧ s1.2.1.Scoped s1.1 ∧ (↑s1.2.2 : CVar F).Scoped s1.1 ∧
          (↑s1.2.2 : CVar F).val s1.1.env.toValuation = bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome ∧
          s1.2.1.val s1.1.env.toValuation = (sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).1 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).1)).getD 0) := by
    have h := sqrtFlaggedRun_grants sqrtF params.nonResidue hs1o1
    rwa [(by rw [CVar.val_add_, gr12.fvar_val]; rfl : (CVar.add_ r12.2 (CVar.const params.b)).val r12.1.env.toValuation = ySquared params (potentialXs params (t.val st.env.toValuation)).1)] at h
  have l13 : r12.1.env.Le s1.1.env := gs1.1
  have L6_13 : r6.1.env.Le s1.1.env := l7.trans (l8.trans (l9.trans (l10.trans (l11.trans (l12.trans (l13))))))
  have hr13o1 : (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)).Scoped s1.1 := ((CVar.Scoped.sub_ (CVar.scoped_const _ _) (CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped)).of_le L6_13)
  have hr13o2 : (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)).Scoped s1.1 := ((CVar.Scoped.sub_ (CVar.scoped_const _ _) (CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped)).of_le L6_13)
  have gr13 : Grants F s1.1 r13 ((potentialXs params (t.val st.env.toValuation)).2.1 * (potentialXs params (t.val st.env.toValuation)).2.1) := by
    have h := mulRun_grants hr13o1 hr13o2
    rwa [((CVar.val_of_le L6_13 (CVar.Scoped.sub_ (CVar.scoped_const _ _) (CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped))).trans (by rw [CVar.val_sub_, (by rw [CVar.val_sub_, gr6.fvar_val]; rfl : (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).val r6.1.env.toValuation = (potentialXs params (t.val st.env.toValuation)).1)]; rfl : (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)).val r6.1.env.toValuation = (potentialXs params (t.val st.env.toValuation)).2.1))] at h
  have l14 : s1.1.env.Le r13.1.env := gr13.le
  have L6_14 : r6.1.env.Le r13.1.env := l7.trans (l8.trans (l9.trans (l10.trans (l11.trans (l12.trans (l13.trans (l14)))))))
  have hr14o1 : (r13.2).Scoped r13.1 := gr13.fvar_scoped
  have hr14o2 : (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)).Scoped r13.1 := ((CVar.Scoped.sub_ (CVar.scoped_const _ _) (CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped)).of_le L6_14)
  have gr14 : Grants F r13.1 r14 ((potentialXs params (t.val st.env.toValuation)).2.1 * (potentialXs params (t.val st.env.toValuation)).2.1 * (potentialXs params (t.val st.env.toValuation)).2.1) := by
    have h := mulRun_grants hr14o1 hr14o2
    rwa [gr13.fvar_val, ((CVar.val_of_le L6_14 (CVar.Scoped.sub_ (CVar.scoped_const _ _) (CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped))).trans (by rw [CVar.val_sub_, (by rw [CVar.val_sub_, gr6.fvar_val]; rfl : (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).val r6.1.env.toValuation = (potentialXs params (t.val st.env.toValuation)).1)]; rfl : (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)).val r6.1.env.toValuation = (potentialXs params (t.val st.env.toValuation)).2.1))] at h
  have l15 : r13.1.env.Le r14.1.env := gr14.le
  have hs2o1 : (CVar.add_ r14.2 (CVar.const params.b)).Scoped r14.1 := (gr14.fvar_scoped.add_ (CVar.scoped_const _ _))
  have gs2 : (r14.1.env.Le s2.1.env ∧ s2.2.1.Scoped s2.1 ∧ (↑s2.2.2 : CVar F).Scoped s2.1 ∧
          (↑s2.2.2 : CVar F).val s2.1.env.toValuation = bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome ∧
          s2.2.1.val s2.1.env.toValuation = (sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).2.1 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).getD 0) := by
    have h := sqrtFlaggedRun_grants sqrtF params.nonResidue hs2o1
    rwa [(by rw [CVar.val_add_, gr14.fvar_val]; rfl : (CVar.add_ r14.2 (CVar.const params.b)).val r14.1.env.toValuation = ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)] at h
  have l16 : r14.1.env.Le s2.1.env := gs2.1
  have L10_16 : r10.1.env.Le s2.1.env := l11.trans (l12.trans (l13.trans (l14.trans (l15.trans (l16)))))
  have hr15o1 : (CVar.sub_ (CVar.const params.u) r10.2).Scoped s2.1 := ((CVar.Scoped.sub_ (CVar.scoped_const _ _) gr10.fvar_scoped).of_le L10_16)
  have hr15o2 : (CVar.sub_ (CVar.const params.u) r10.2).Scoped s2.1 := ((CVar.Scoped.sub_ (CVar.scoped_const _ _) gr10.fvar_scoped).of_le L10_16)
  have gr15 : Grants F s2.1 r15 ((potentialXs params (t.val st.env.toValuation)).2.2 * (potentialXs params (t.val st.env.toValuation)).2.2) := by
    have h := mulRun_grants hr15o1 hr15o2
    rwa [((CVar.val_of_le L10_16 (CVar.Scoped.sub_ (CVar.scoped_const _ _) gr10.fvar_scoped)).trans (by rw [CVar.val_sub_, gr10.fvar_val]; rfl : (CVar.sub_ (CVar.const params.u) r10.2).val r10.1.env.toValuation = (potentialXs params (t.val st.env.toValuation)).2.2))] at h
  have l17 : s2.1.env.Le r15.1.env := gr15.le
  have L10_17 : r10.1.env.Le r15.1.env := l11.trans (l12.trans (l13.trans (l14.trans (l15.trans (l16.trans (l17))))))
  have hr16o1 : (r15.2).Scoped r15.1 := gr15.fvar_scoped
  have hr16o2 : (CVar.sub_ (CVar.const params.u) r10.2).Scoped r15.1 := ((CVar.Scoped.sub_ (CVar.scoped_const _ _) gr10.fvar_scoped).of_le L10_17)
  have gr16 : Grants F r15.1 r16 ((potentialXs params (t.val st.env.toValuation)).2.2 * (potentialXs params (t.val st.env.toValuation)).2.2 * (potentialXs params (t.val st.env.toValuation)).2.2) := by
    have h := mulRun_grants hr16o1 hr16o2
    rwa [gr15.fvar_val, ((CVar.val_of_le L10_17 (CVar.Scoped.sub_ (CVar.scoped_const _ _) gr10.fvar_scoped)).trans (by rw [CVar.val_sub_, gr10.fvar_val]; rfl : (CVar.sub_ (CVar.const params.u) r10.2).val r10.1.env.toValuation = (potentialXs params (t.val st.env.toValuation)).2.2))] at h
  have l18 : r15.1.env.Le r16.1.env := gr16.le
  have hs3o1 : (CVar.add_ r16.2 (CVar.const params.b)).Scoped r16.1 := (gr16.fvar_scoped.add_ (CVar.scoped_const _ _))
  have gs3 : (r16.1.env.Le s3.1.env ∧ s3.2.1.Scoped s3.1 ∧ (↑s3.2.2 : CVar F).Scoped s3.1 ∧
          (↑s3.2.2 : CVar F).val s3.1.env.toValuation = bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome ∧
          s3.2.1.val s3.1.env.toValuation = (sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).2.2 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).getD 0) := by
    have h := sqrtFlaggedRun_grants sqrtF params.nonResidue hs3o1
    rwa [(by rw [CVar.val_add_, gr16.fvar_val]; rfl : (CVar.add_ r16.2 (CVar.const params.b)).val r16.1.env.toValuation = ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)] at h
  have l19 : r16.1.env.Le s3.1.env := gs3.1
  have L13_19 : s1.1.env.Le s3.1.env := l14.trans (l15.trans (l16.trans (l17.trans (l18.trans (l19)))))
  have L16_19 : s2.1.env.Le s3.1.env := l17.trans (l18.trans (l19))
  have hrNZo1 : (CVar.add_ (CVar.add_ (↑s1.2.2 : CVar F) (↑s2.2.2 : CVar F)) (↑s3.2.2 : CVar F)).Scoped s3.1 := (CVar.Scoped.add_ (CVar.Scoped.add_ (gs1.2.2.1.of_le L13_19) (gs2.2.2.1.of_le L16_19)) gs3.2.2.1)
  have grNZ : Grants F s3.1 rNZ ((bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome)⁻¹) := by
    have h := invRun_grants hrNZo1
    rwa [(by rw [CVar.val_add_, CVar.val_add_, ((CVar.val_of_le L13_19 gs1.2.2.1).trans gs1.2.2.2.1), ((CVar.val_of_le L16_19 gs2.2.2.1).trans gs2.2.2.2.1), gs3.2.2.2.1] : (CVar.add_ (CVar.add_ (↑s1.2.2 : CVar F) (↑s2.2.2 : CVar F)) (↑s3.2.2 : CVar F)).val s3.1.env.toValuation = bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome)] at h
  have l20 : s3.1.env.Le rNZ.1.env := grNZ.le
  have hsumv : (CVar.add_ (CVar.add_ (↑s1.2.2 : CVar F) (↑s2.2.2 : CVar F)) (↑s3.2.2 : CVar F)).val s3.1.env.toValuation = bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome := (by rw [CVar.val_add_, CVar.val_add_, ((CVar.val_of_le L13_19 gs1.2.2.1).trans gs1.2.2.2.1), ((CVar.val_of_le L16_19 gs2.2.2.1).trans gs2.2.2.2.1), gs3.2.2.2.1] : (CVar.add_ (CVar.add_ (↑s1.2.2 : CVar F) (↑s2.2.2 : CVar F)) (↑s3.2.2 : CVar F)).val s3.1.env.toValuation = bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome)
  have L13_20 : s1.1.env.Le rNZ.1.env := l14.trans (l15.trans (l16.trans (l17.trans (l18.trans (l19.trans (l20))))))
  have L16_20 : s2.1.env.Le rNZ.1.env := l17.trans (l18.trans (l19.trans (l20)))
  have ha1o1 : ((↑(Snarky.not s1.2.2) : CVar F)).Scoped rNZ.1 := ((not_scoped gs1.2.2.1).of_le L13_20)
  have ha1o2 : ((↑s2.2.2 : CVar F)).Scoped rNZ.1 := (gs2.2.2.1.of_le L16_20)
  have ga1 : Grants F rNZ.1 (a1.1, (↑a1.2 : CVar F)) (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome)) :=
    andRun_grants ha1o1 ha1o2 ((CVar.val_of_le L13_20 (not_scoped gs1.2.2.1)).trans (not_val gs1.2.2.2.1)) ((CVar.val_of_le L16_20 gs2.2.2.1).trans gs2.2.2.2.1)
  have l21 : rNZ.1.env.Le a1.1.env := ga1.le
  have L16_21 : s2.1.env.Le a1.1.env := l17.trans (l18.trans (l19.trans (l20.trans (l21))))
  have L19_21 : s3.1.env.Le a1.1.env := l20.trans (l21)
  have ha2o1 : ((↑(Snarky.not s2.2.2) : CVar F)).Scoped a1.1 := ((not_scoped gs2.2.2.1).of_le L16_21)
  have ha2o2 : ((↑s3.2.2 : CVar F)).Scoped a1.1 := (gs3.2.2.1.of_le L19_21)
  have ga2 : Grants F a1.1 (a2.1, (↑a2.2 : CVar F)) (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome)) :=
    andRun_grants ha2o1 ha2o2 ((CVar.val_of_le L16_21 (not_scoped gs2.2.2.1)).trans (not_val gs2.2.2.2.1)) ((CVar.val_of_le L19_21 gs3.2.2.1).trans gs3.2.2.2.1)
  have l22 : a1.1.env.Le a2.1.env := ga2.le
  have L13_22 : s1.1.env.Le a2.1.env := l14.trans (l15.trans (l16.trans (l17.trans (l18.trans (l19.trans (l20.trans (l21.trans (l22))))))))
  have ha3o1 : ((↑(Snarky.not s1.2.2) : CVar F)).Scoped a2.1 := ((not_scoped gs1.2.2.1).of_le L13_22)
  have ha3o2 : ((↑a2.2 : CVar F)).Scoped a2.1 := ga2.fvar_scoped
  have ga3 : Grants F a2.1 (a3.1, (↑a3.2 : CVar F)) (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome))) :=
    andRun_grants ha3o1 ha3o2 ((CVar.val_of_le L13_22 (not_scoped gs1.2.2.1)).trans (not_val gs1.2.2.2.1)) ga2.fvar_val
  have l23 : a2.1.env.Le a3.1.env := ga3.le
  have L19_23 : s3.1.env.Le a3.1.env := l20.trans (l21.trans (l22.trans (l23)))
  have hm1o1 : ((↑a3.2 : CVar F)).Scoped a3.1 := ga3.fvar_scoped
  have hm1o2 : (s3.2.1).Scoped a3.1 := (gs3.2.1.of_le L19_23)
  have gm1 : Grants F a3.1 m1 (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome)) * ((sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).2.2 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).getD 0)) := by
    have h := mulRun_grants hm1o1 hm1o2
    rwa [ga3.fvar_val, ((CVar.val_of_le L19_23 gs3.2.1).trans gs3.2.2.2.2)] at h
  have l24 : a3.1.env.Le m1.1.env := gm1.le
  have L21_24 : a1.1.env.Le m1.1.env := l22.trans (l23.trans (l24))
  have L16_24 : s2.1.env.Le m1.1.env := l17.trans (l18.trans (l19.trans (l20.trans (l21.trans (l22.trans (l23.trans (l24)))))))
  have hm2o1 : ((↑a1.2 : CVar F)).Scoped m1.1 := (ga1.fvar_scoped.of_le L21_24)
  have hm2o2 : (s2.2.1).Scoped m1.1 := (gs2.2.1.of_le L16_24)
  have gm2 : Grants F m1.1 m2 (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome) * ((sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).2.1 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).getD 0)) := by
    have h := mulRun_grants hm2o1 hm2o2
    rwa [((CVar.val_of_le L21_24 ga1.fvar_scoped).trans ga1.fvar_val), ((CVar.val_of_le L16_24 gs2.2.1).trans gs2.2.2.2.2)] at h
  have l25 : m1.1.env.Le m2.1.env := gm2.le
  have L13_25 : s1.1.env.Le m2.1.env := l14.trans (l15.trans (l16.trans (l17.trans (l18.trans (l19.trans (l20.trans (l21.trans (l22.trans (l23.trans (l24.trans (l25)))))))))))
  have hm3o1 : ((↑s1.2.2 : CVar F)).Scoped m2.1 := (gs1.2.2.1.of_le L13_25)
  have hm3o2 : (s1.2.1).Scoped m2.1 := (gs1.2.1.of_le L13_25)
  have gm3 : Grants F m2.1 m3 (bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome * ((sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).1 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).1)).getD 0)) := by
    have h := mulRun_grants hm3o1 hm3o2
    rwa [((CVar.val_of_le L13_25 gs1.2.2.1).trans gs1.2.2.2.1), ((CVar.val_of_le L13_25 gs1.2.1).trans gs1.2.2.2.2)] at h
  have l26 : m2.1.env.Le m3.1.env := gm3.le
  have L23_26 : a3.1.env.Le m3.1.env := l24.trans (l25.trans (l26))
  have L10_26 : r10.1.env.Le m3.1.env := l11.trans (l12.trans (l13.trans (l14.trans (l15.trans (l16.trans (l17.trans (l18.trans (l19.trans (l20.trans (l21.trans (l22.trans (l23.trans (l24.trans (l25.trans (l26)))))))))))))))
  have hm4o1 : ((↑a3.2 : CVar F)).Scoped m3.1 := (ga3.fvar_scoped.of_le L23_26)
  have hm4o2 : (CVar.sub_ (CVar.const params.u) r10.2).Scoped m3.1 := ((CVar.Scoped.sub_ (CVar.scoped_const _ _) gr10.fvar_scoped).of_le L10_26)
  have gm4 : Grants F m3.1 m4 (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome)) * (potentialXs params (t.val st.env.toValuation)).2.2) := by
    have h := mulRun_grants hm4o1 hm4o2
    rwa [((CVar.val_of_le L23_26 ga3.fvar_scoped).trans ga3.fvar_val), ((CVar.val_of_le L10_26 (CVar.Scoped.sub_ (CVar.scoped_const _ _) gr10.fvar_scoped)).trans (by rw [CVar.val_sub_, gr10.fvar_val]; rfl : (CVar.sub_ (CVar.const params.u) r10.2).val r10.1.env.toValuation = (potentialXs params (t.val st.env.toValuation)).2.2))] at h
  have l27 : m3.1.env.Le m4.1.env := gm4.le
  have L21_27 : a1.1.env.Le m4.1.env := l22.trans (l23.trans (l24.trans (l25.trans (l26.trans (l27)))))
  have L6_27 : r6.1.env.Le m4.1.env := l7.trans (l8.trans (l9.trans (l10.trans (l11.trans (l12.trans (l13.trans (l14.trans (l15.trans (l16.trans (l17.trans (l18.trans (l19.trans (l20.trans (l21.trans (l22.trans (l23.trans (l24.trans (l25.trans (l26.trans (l27))))))))))))))))))))
  have hm5o1 : ((↑a1.2 : CVar F)).Scoped m4.1 := (ga1.fvar_scoped.of_le L21_27)
  have hm5o2 : (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)).Scoped m4.1 := ((CVar.Scoped.sub_ (CVar.scoped_const _ _) (CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped)).of_le L6_27)
  have gm5 : Grants F m4.1 m5 (bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome) * (potentialXs params (t.val st.env.toValuation)).2.1) := by
    have h := mulRun_grants hm5o1 hm5o2
    rwa [((CVar.val_of_le L21_27 ga1.fvar_scoped).trans ga1.fvar_val), ((CVar.val_of_le L6_27 (CVar.Scoped.sub_ (CVar.scoped_const _ _) (CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped))).trans (by rw [CVar.val_sub_, (by rw [CVar.val_sub_, gr6.fvar_val]; rfl : (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).val r6.1.env.toValuation = (potentialXs params (t.val st.env.toValuation)).1)]; rfl : (CVar.sub_ (CVar.const (-params.u)) (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2)).val r6.1.env.toValuation = (potentialXs params (t.val st.env.toValuation)).2.1))] at h
  have l28 : m4.1.env.Le m5.1.env := gm5.le
  have L13_28 : s1.1.env.Le m5.1.env := l14.trans (l15.trans (l16.trans (l17.trans (l18.trans (l19.trans (l20.trans (l21.trans (l22.trans (l23.trans (l24.trans (l25.trans (l26.trans (l27.trans (l28))))))))))))))
  have L6_28 : r6.1.env.Le m5.1.env := l7.trans (l8.trans (l9.trans (l10.trans (l11.trans (l12.trans (l13.trans (l14.trans (l15.trans (l16.trans (l17.trans (l18.trans (l19.trans (l20.trans (l21.trans (l22.trans (l23.trans (l24.trans (l25.trans (l26.trans (l27.trans (l28)))))))))))))))))))))
  have hm6o1 : ((↑s1.2.2 : CVar F)).Scoped m5.1 := (gs1.2.2.1.of_le L13_28)
  have hm6o2 : (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).Scoped m5.1 := ((CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped).of_le L6_28)
  have gm6 : Grants F m5.1 m6 (bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome * (potentialXs params (t.val st.env.toValuation)).1) := by
    have h := mulRun_grants hm6o1 hm6o2
    rwa [((CVar.val_of_le L13_28 gs1.2.2.1).trans gs1.2.2.2.1), ((CVar.val_of_le L6_28 (CVar.Scoped.sub_ (CVar.scoped_const _ _) gr6.fvar_scoped)).trans (by rw [CVar.val_sub_, gr6.fvar_val]; rfl : (CVar.sub_ (CVar.const params.sqrtNeg3U2MinusUOver2) r6.2).val r6.1.env.toValuation = (potentialXs params (t.val st.env.toValuation)).1))] at h
  have l29 : m5.1.env.Le m6.1.env := gm6.le
  exact ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, s1, r13, r14, s2, r15, r16, s3, rNZ, a1, a2, a3, m1, m2, m3, m4, m5, m6, rfl, ⟨rfl, hr1o1, hr1o2, gr1⟩, ⟨rfl, hr2o1, hr2o2, gr2⟩, ⟨rfl, hr3o1, hr3o2, gr3⟩, ⟨rfl, hr4o1, hr4o2, gr4⟩, ⟨rfl, hr5o1, hr5o2, gr5⟩, ⟨rfl, hr6o1, hr6o2, gr6⟩, ⟨rfl, hr7o1, hr7o2, gr7⟩, ⟨rfl, hr8o1, hr8o2, gr8⟩, ⟨rfl, hr9o1, hr9o2, gr9⟩, ⟨rfl, hr10o1, hr10o2, gr10⟩, ⟨rfl, hr11o1, hr11o2, gr11⟩, ⟨rfl, hr12o1, hr12o2, gr12⟩, ⟨rfl, hs1o1, gs1⟩, ⟨rfl, hr13o1, hr13o2, gr13⟩, ⟨rfl, hr14o1, hr14o2, gr14⟩, ⟨rfl, hs2o1, gs2⟩, ⟨rfl, hr15o1, hr15o2, gr15⟩, ⟨rfl, hr16o1, hr16o2, gr16⟩, ⟨rfl, hs3o1, gs3⟩, ⟨rfl, hrNZo1, grNZ⟩, ⟨rfl, ha1o1, ha1o2, ga1⟩, ⟨rfl, ha2o1, ha2o2, ga2⟩, ⟨rfl, ha3o1, ha3o2, ga3⟩, ⟨rfl, hm1o1, hm1o2, gm1⟩, ⟨rfl, hm2o1, hm2o2, gm2⟩, ⟨rfl, hm3o1, hm3o2, gm3⟩, ⟨rfl, hm4o1, hm4o2, gm4⟩, ⟨rfl, hm5o1, hm5o2, gm5⟩, ⟨rfl, hm6o1, hm6o2, gm6⟩, hsumv⟩

/-- `groupMapCircuit`'s honest run on an in-scope operand lands at `groupMapCircuitRun`.
Hypotheses: `sqrtF`'s roots are genuine; a rootless value's non-residue twist has a root;
`2, 3 ≠ 0` price the flag-sum assertion; the `div` divisor is nonzero; and some candidate
ordinate square has a root — Shallue–van de Woestijne, taken as a hypothesis. -/
theorem groupMapCircuit_run [Field F] [DecidableEq F] {c : Type}
    [BasicSystem F c] [Checker F c] [LawfulChecker F c]
    (sqrtF : F → Option F) (params : GroupMapParams F) {t : FVar F} (st : ProverState F)
    (ht : t.Scoped st)
    (hroot : ∀ a y, sqrtF a = some y → y * y = a)
    (htwist : ∀ a, sqrtF a = none → (sqrtF (params.nonResidue * a)).isSome)
    (htwo : (2 : F) ≠ 0) (hthree : (3 : F) ≠ 0)
    (hne : (t.val st.env.toValuation * t.val st.env.toValuation + params.fu) * (t.val st.env.toValuation * t.val st.env.toValuation) ≠ 0)
    (hdisj : (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome ∨ (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome ∨ (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome) :
    prove (Checker.holds (F := F) (c := c)) (groupMapCircuit (c := c) sqrtF params t) st.nv st.env
      = .ok ((groupMapCircuitRun sqrtF params st t).1.out
          (groupMapCircuitRun sqrtF params st t).2) := by
  have hsumne : (bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome + bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome : F) ≠ 0 := by
    generalize (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome = b1 at hdisj ⊢
    generalize (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome = b2 at hdisj ⊢
    generalize (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome = b3 at hdisj ⊢
    cases b1 <;> cases b2 <;> cases b3 <;> simp [bit] at hdisj ⊢ <;>
      first
      | exact one_ne_zero
      | (rw [one_add_one_eq_two]; exact htwo)
      | (rw [one_add_one_eq_two, two_add_one_eq_three]; exact hthree)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, s1, r13, r14, s2, r15, r16, s3, rNZ, a1, a2, a3, m1, m2, m3, m4, m5, m6, hR, ⟨hr1, hr1o1, hr1o2, gr1⟩, ⟨hr2, hr2o1, hr2o2, gr2⟩, ⟨hr3, hr3o1, hr3o2, gr3⟩, ⟨hr4, hr4o1, hr4o2, gr4⟩, ⟨hr5, hr5o1, hr5o2, gr5⟩, ⟨hr6, hr6o1, hr6o2, gr6⟩, ⟨hr7, hr7o1, hr7o2, gr7⟩, ⟨hr8, hr8o1, hr8o2, gr8⟩, ⟨hr9, hr9o1, hr9o2, gr9⟩, ⟨hr10, hr10o1, hr10o2, gr10⟩, ⟨hr11, hr11o1, hr11o2, gr11⟩, ⟨hr12, hr12o1, hr12o2, gr12⟩, ⟨hs1, hs1o1, gs1⟩, ⟨hr13, hr13o1, hr13o2, gr13⟩, ⟨hr14, hr14o1, hr14o2, gr14⟩, ⟨hs2, hs2o1, gs2⟩, ⟨hr15, hr15o1, hr15o2, gr15⟩, ⟨hr16, hr16o1, hr16o2, gr16⟩, ⟨hs3, hs3o1, gs3⟩, ⟨hrNZ, hrNZo1, grNZ⟩, ⟨ha1, ha1o1, ha1o2, ga1⟩, ⟨ha2, ha2o1, ha2o2, ga2⟩, ⟨ha3, ha3o1, ha3o2, ga3⟩, ⟨hm1, hm1o1, hm1o2, gm1⟩, ⟨hm2, hm2o1, hm2o2, gm2⟩, ⟨hm3, hm3o1, hm3o2, gm3⟩, ⟨hm4, hm4o1, hm4o2, gm4⟩, ⟨hm5, hm5o1, hm5o2, gm5⟩, ⟨hm6, hm6o1, hm6o2, gm6⟩, hsumv⟩ :=
    run_facts sqrtF params ht
  rw [hR]
  simp only [groupMapCircuit, prove_bind]
  rw [mul_run st hr1o1 hr1o2, hr1]
  simp only [Except.bind]
  rw [mul_run r1.1 hr2o1 hr2o2, hr2]
  simp only [Except.bind]
  rw [div_run r2.1 hr3o1 hr3o2 (by rw [gr2.fvar_val]; exact hne), hr3]
  simp only [Except.bind]
  rw [mul_run r3.1 hr4o1 hr4o2, hr4]
  simp only [Except.bind]
  rw [mul_run r4.1 hr5o1 hr5o2, hr5]
  simp only [Except.bind]
  rw [mul_run r5.1 hr6o1 hr6o2, hr6]
  simp only [Except.bind]
  rw [mul_run r6.1 hr7o1 hr7o2, hr7]
  simp only [Except.bind]
  rw [mul_run r7.1 hr8o1 hr8o2, hr8]
  simp only [Except.bind]
  rw [mul_run r8.1 hr9o1 hr9o2, hr9]
  simp only [Except.bind]
  rw [mul_run r9.1 hr10o1 hr10o2, hr10]
  simp only [Except.bind]
  rw [mul_run r10.1 hr11o1 hr11o2, hr11]
  simp only [Except.bind]
  rw [mul_run r11.1 hr12o1 hr12o2, hr12]
  simp only [Except.bind, prove_pure]
  rw [sqrtFlagged_run sqrtF params.nonResidue r12.1 hs1o1 hroot (htwist _), hs1]
  simp only [Except.bind]
  rw [mul_run s1.1 hr13o1 hr13o2, hr13]
  simp only [Except.bind]
  rw [mul_run r13.1 hr14o1 hr14o2, hr14]
  simp only [Except.bind, prove_pure]
  rw [sqrtFlagged_run sqrtF params.nonResidue r14.1 hs2o1 hroot (htwist _), hs2]
  simp only [Except.bind]
  rw [mul_run s2.1 hr15o1 hr15o2, hr15]
  simp only [Except.bind]
  rw [mul_run r15.1 hr16o1 hr16o2, hr16]
  simp only [Except.bind, prove_pure]
  rw [sqrtFlagged_run sqrtF params.nonResidue r16.1 hs3o1 hroot (htwist _), hs3]
  simp only [Except.bind]
  rw [assertNonZero_run s3.1 hrNZo1 (by rw [hsumv]; exact hsumne), hrNZ]
  simp only [Except.bind]
  rw [and_run rNZ.1 ha1o1 ha1o2, ha1]
  simp only [Except.bind]
  rw [and_run a1.1 ha2o1 ha2o2, ha2]
  simp only [Except.bind]
  rw [and_run a2.1 ha3o1 ha3o2, ha3]
  simp only [Except.bind]
  rw [mul_run a3.1 hm1o1 hm1o2, hm1]
  simp only [Except.bind]
  rw [mul_run m1.1 hm2o1 hm2o2, hm2]
  simp only [Except.bind]
  rw [mul_run m2.1 hm3o1 hm3o2, hm3]
  simp only [Except.bind]
  rw [mul_run m3.1 hm4o1 hm4o2, hm4]
  simp only [Except.bind]
  rw [mul_run m4.1 hm5o1 hm5o2, hm5]
  simp only [Except.bind]
  rw [mul_run m5.1 hm6o1 hm6o2, hm6]

/-- `groupMapCircuitRun` grows the table; the point is in scope at the state after and
reads the pure map's point, `groupMapPure` — the first-flagged candidate. No hypothesis
beyond the operand's scope: the run's readings are the pure model's whether or not a
candidate is a square (both read `(0, 0)` when none is). -/
theorem groupMapCircuitRun_grants [Field F] [DecidableEq F] (sqrtF : F → Option F)
    (params : GroupMapParams F) {st : ProverState F} {t : FVar F} (ht : t.Scoped st) :
    st.env.Le (groupMapCircuitRun sqrtF params st t).1.env ∧
      (groupMapCircuitRun sqrtF params st t).2.x.Scoped (groupMapCircuitRun sqrtF params st t).1 ∧
      (groupMapCircuitRun sqrtF params st t).2.y.Scoped (groupMapCircuitRun sqrtF params st t).1 ∧
      (groupMapCircuitRun sqrtF params st t).2.x.val
          (groupMapCircuitRun sqrtF params st t).1.env.toValuation
        = (groupMapPure sqrtF params (t.val st.env.toValuation)).1 ∧
      (groupMapCircuitRun sqrtF params st t).2.y.val
          (groupMapCircuitRun sqrtF params st t).1.env.toValuation
        = (groupMapPure sqrtF params (t.val st.env.toValuation)).2 := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, s1, r13, r14, s2, r15, r16, s3, rNZ, a1, a2, a3, m1, m2, m3, m4, m5, m6, hR, ⟨hr1, hr1o1, hr1o2, gr1⟩, ⟨hr2, hr2o1, hr2o2, gr2⟩, ⟨hr3, hr3o1, hr3o2, gr3⟩, ⟨hr4, hr4o1, hr4o2, gr4⟩, ⟨hr5, hr5o1, hr5o2, gr5⟩, ⟨hr6, hr6o1, hr6o2, gr6⟩, ⟨hr7, hr7o1, hr7o2, gr7⟩, ⟨hr8, hr8o1, hr8o2, gr8⟩, ⟨hr9, hr9o1, hr9o2, gr9⟩, ⟨hr10, hr10o1, hr10o2, gr10⟩, ⟨hr11, hr11o1, hr11o2, gr11⟩, ⟨hr12, hr12o1, hr12o2, gr12⟩, ⟨hs1, hs1o1, gs1⟩, ⟨hr13, hr13o1, hr13o2, gr13⟩, ⟨hr14, hr14o1, hr14o2, gr14⟩, ⟨hs2, hs2o1, gs2⟩, ⟨hr15, hr15o1, hr15o2, gr15⟩, ⟨hr16, hr16o1, hr16o2, gr16⟩, ⟨hs3, hs3o1, gs3⟩, ⟨hrNZ, hrNZo1, grNZ⟩, ⟨ha1, ha1o1, ha1o2, ga1⟩, ⟨ha2, ha2o1, ha2o2, ga2⟩, ⟨ha3, ha3o1, ha3o2, ga3⟩, ⟨hm1, hm1o1, hm1o2, gm1⟩, ⟨hm2, hm2o1, hm2o2, gm2⟩, ⟨hm3, hm3o1, hm3o2, gm3⟩, ⟨hm4, hm4o1, hm4o2, gm4⟩, ⟨hm5, hm5o1, hm5o2, gm5⟩, ⟨hm6, hm6o1, hm6o2, gm6⟩, hsumv⟩ :=
    run_facts sqrtF params ht
  rw [hR]
  have hL : st.env.Le m6.1.env := gr1.le.trans (gr2.le.trans (gr3.le.trans (gr4.le.trans (gr5.le.trans (gr6.le.trans (gr7.le.trans (gr8.le.trans (gr9.le.trans (gr10.le.trans (gr11.le.trans (gr12.le.trans (gs1.1.trans (gr13.le.trans (gr14.le.trans (gs2.1.trans (gr15.le.trans (gr16.le.trans (gs3.1.trans (grNZ.le.trans (ga1.le.trans (ga2.le.trans (ga3.le.trans (gm1.le.trans (gm2.le.trans (gm3.le.trans (gm4.le.trans (gm5.le.trans (gm6.le))))))))))))))))))))))))))))
  have l5 : m5.1.env.Le m6.1.env := gm6.le
  have l4 : m4.1.env.Le m6.1.env := gm5.le.trans gm6.le
  have l3 : m3.1.env.Le m6.1.env := gm4.le.trans (gm5.le.trans gm6.le)
  have l2 : m2.1.env.Le m6.1.env := gm3.le.trans (gm4.le.trans (gm5.le.trans gm6.le))
  have l1 : m1.1.env.Le m6.1.env := gm2.le.trans (gm3.le.trans (gm4.le.trans (gm5.le.trans gm6.le)))
  have hx : (CVar.add_ (CVar.add_ m6.2 m5.2) m4.2).val m6.1.env.toValuation
      = bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome * (potentialXs params (t.val st.env.toValuation)).1 + bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome) * (potentialXs params (t.val st.env.toValuation)).2.1 + bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome)) * (potentialXs params (t.val st.env.toValuation)).2.2 := by
    rw [CVar.val_add_, CVar.val_add_, gm6.fvar_val, CVar.val_of_le l5 gm5.fvar_scoped, gm5.fvar_val,
      CVar.val_of_le l4 gm4.fvar_scoped, gm4.fvar_val]
  have hy : (CVar.add_ (CVar.add_ m3.2 m2.2) m1.2).val m6.1.env.toValuation
      = bit (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome * ((sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).1 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).1)).getD 0) + bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome) * ((sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).2.1 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).getD 0) + bit (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome && (!(sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome && (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome)) * ((sqrtF (if (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome then ySquared params (potentialXs params (t.val st.env.toValuation)).2.2 else params.nonResidue * ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).getD 0) := by
    rw [CVar.val_add_, CVar.val_add_, CVar.val_of_le l3 gm3.fvar_scoped, gm3.fvar_val,
      CVar.val_of_le l2 gm2.fvar_scoped, gm2.fvar_val, CVar.val_of_le l1 gm1.fvar_scoped, gm1.fvar_val]
  refine ⟨hL, CVar.Scoped.add_ (CVar.Scoped.add_ gm6.fvar_scoped (gm5.fvar_scoped.of_le l5))
      (gm4.fvar_scoped.of_le l4),
    CVar.Scoped.add_ (CVar.Scoped.add_ (gm3.fvar_scoped.of_le l3) (gm2.fvar_scoped.of_le l2))
      (gm1.fvar_scoped.of_le l1), ?_, ?_⟩
  · rw [hx, groupMapPure_eq]
    generalize (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome = b1
    generalize (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome = b2
    generalize (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome = b3
    cases b1 <;> cases b2 <;> cases b3 <;> simp [bit]
  · rw [hy, groupMapPure_eq]
    generalize (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).1)).isSome = b1
    generalize (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.1)).isSome = b2
    generalize (sqrtF (ySquared params (potentialXs params (t.val st.env.toValuation)).2.2)).isSome = b3
    cases b1 <;> cases b2 <;> cases b3 <;> simp [bit]

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
def GroupMapParams.ofSpec (spec : Poseidon.GroupMap.Spec q) (nonResidue : ZMod q) :
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
theorem potentialXs_ofSpec (spec : Poseidon.GroupMap.Spec q)
    (nonResidue t : ZMod q) :
    potentialXs (.ofSpec spec nonResidue) t
      = Poseidon.GroupMap.potentialXs spec t := by
  have hinv : (1 : ZMod q) / ((t * t + spec.fu) * (t * t))
      = (t ^ 2 * (t ^ 2 + spec.fu))⁻¹ := by
    rw [one_div,
      show (t * t + spec.fu) * (t * t) = t ^ 2 * (t ^ 2 + spec.fu) from by ring]
  simp only [potentialXs, Poseidon.GroupMap.potentialXs, GroupMapParams.ofSpec,
    hinv, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- The candidate test values agree with the wire map's: `ySquared` at `ofSpec` is
`Poseidon.GroupMap.curveEqn`. -/
theorem ySquared_ofSpec (spec : Poseidon.GroupMap.Spec q)
    (nonResidue x : ZMod q) :
    ySquared (.ofSpec spec nonResidue) x = Poseidon.GroupMap.curveEqn spec x := by
  simp only [ySquared, Poseidon.GroupMap.curveEqn, GroupMapParams.ofSpec]
  ring

/-- **The wire identification**: at a wire `Spec`, with the spec's own Tonelli–Shanks
root as advice, the module's pure model computes the wire map's point — coordinate for
coordinate, first-flagged candidate for first-flagged candidate. -/
theorem groupMapPure_toGroup (spec : Poseidon.GroupMap.Spec q)
    (nonResidue t : ZMod q) :
    groupMapPure spec.sqrt.sqrt? (.ofSpec spec nonResidue) t
      = ((Poseidon.GroupMap.toGroup spec t).x,
          (Poseidon.GroupMap.toGroup spec t).y) := by
  have hys : ∀ x : ZMod q,
      spec.sqrt.sqrt? (ySquared (GroupMapParams.ofSpec spec nonResidue) x)
        = Poseidon.GroupMap.getY spec x := fun x => by
    rw [ySquared_ofSpec, Poseidon.GroupMap.getY]
  rcases hg : Poseidon.GroupMap.toGroup spec t with ⟨px, py, hval⟩
  simp only [Poseidon.GroupMap.toGroup] at hg
  split at hg <;> [skip; split at hg <;> [skip; split at hg]] <;>
    obtain ⟨rfl, rfl⟩ : _ ∧ _ := ⟨congrArg SWPoint.x hg, congrArg SWPoint.y hg⟩ <;>
    simp [groupMapPure, potentialXs_ofSpec, *]

/-- A rootless value's non-residue twist has a root: two non-squares multiply to a
square (`FiniteField.pow_dichotomy`), and `sqrt?` is complete on squares. The discharge
of `groupMapCircuit_run`'s twist hypothesis at a genuine Tonelli–Shanks root. -/
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
/-- Wire-level soundness: any satisfying valuation reads the result as a point of the
wire spec's curve — `OnCurve`, the verifier's own predicate — at one of the SvdW
candidate abscissae. The advice is universally quantified: soundness never consults
it. -/
theorem groupMapCircuit_onCurve_spec {V : Valuation (ZMod q)} (spec : Poseidon.GroupMap.Spec q)
    (nonResidue : ZMod q) (sqrtF : ZMod q → Option (ZMod q)) (t : FVar (ZMod q)) :
    ⦃⌜True⌝⦄
    (groupMapCircuit (c := Builder V (KimchiConstraint (ZMod q))) sqrtF (.ofSpec spec nonResidue) t)
    ⦃⇓ r _ => ⌜(r.x.val V = (potentialXs (.ofSpec spec nonResidue) (t.val V)).1
          ∨ r.x.val V = (potentialXs (.ofSpec spec nonResidue) (t.val V)).2.1
          ∨ r.x.val V = (potentialXs (.ofSpec spec nonResidue) (t.val V)).2.2) ∧
        OnCurve spec.E.A spec.E.B (r.x.val V, r.y.val V)⌝⦄ := by
  have hg := groupMapCircuit_spec (V := V) sqrtF (.ofSpec spec nonResidue) t
  mvcgen [hg]
  rename_i r _
  intro h1 h2
  refine ⟨h1, ?_⟩
  show r.y.val V ^ 2 = r.x.val V ^ 3 + spec.E.A * r.x.val V + spec.E.B
  rw [spec.hA]
  have hb := h2
  simp only [GroupMapParams.ofSpec] at hb
  linear_combination hb

/-- Wire-level run law: the honest run accepts at a wire `Spec`. `groupMapCircuit_run` with
the advice the spec's own Tonelli–Shanks root: root-genuineness is `sqrt?_mul_self`,
twist-totality is `sqrt?_twist` at a genuine non-residue, `2 ≠ 0` comes from `q ≠ 2`, and
`q ≠ 3` prices the flag-sum assertion. The SvdW disjunction (as `IsSquare`) and the
operand nondegeneracy remain. -/
theorem groupMapCircuit_toGroup_run {c : Type} [BasicSystem (ZMod q) c]
    [Checker (ZMod q) c] [LawfulChecker (ZMod q) c]
    (spec : Poseidon.GroupMap.Spec q) (nonResidue : ZMod q) {t : FVar (ZMod q)}
    (st : ProverState (ZMod q)) (ht : t.Scoped st)
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hnr0 : nonResidue ≠ 0) (hnr : ¬IsSquare nonResidue)
    (hne : (t.val st.env.toValuation * t.val st.env.toValuation + spec.fu) * (t.val st.env.toValuation * t.val st.env.toValuation) ≠ 0)
    (hdisj : IsSquare (ySquared (.ofSpec spec nonResidue)
        (potentialXs (.ofSpec spec nonResidue) (t.val st.env.toValuation)).1) ∨
      IsSquare (ySquared (.ofSpec spec nonResidue)
        (potentialXs (.ofSpec spec nonResidue) (t.val st.env.toValuation)).2.1) ∨
      IsSquare (ySquared (.ofSpec spec nonResidue)
        (potentialXs (.ofSpec spec nonResidue) (t.val st.env.toValuation)).2.2)) :
    prove (Checker.holds (F := ZMod q) (c := c))
      (groupMapCircuit (c := c) spec.sqrt.sqrt? (.ofSpec spec nonResidue) t) st.nv st.env
      = .ok ((groupMapCircuitRun spec.sqrt.sqrt? (.ofSpec spec nonResidue) st t).1.out
          (groupMapCircuitRun spec.sqrt.sqrt? (.ofSpec spec nonResidue) st t).2) := by
  have hchar : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hq2
  have hthree : (3 : ZMod q) ≠ 0 := by
    intro h
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp
      ((CharP.cast_eq_zero_iff (ZMod q) q 3).mp (by exact_mod_cast h)))
  have hsome : ∀ v : ZMod q, IsSquare v → (spec.sqrt.sqrt? v).isSome := fun v hv => by
    obtain ⟨r, hr⟩ := spec.sqrt.sqrt?_isSome_of_isSquare hv
    rw [hr]
    rfl
  exact groupMapCircuit_run spec.sqrt.sqrt? (.ofSpec spec nonResidue) st ht
    (fun a y h => TonelliShanks.sqrt?_mul_self spec.sqrt h)
    (sqrt?_twist spec.sqrt hchar hnr0 hnr) (Ring.two_ne_zero hchar) hthree hne
    (hdisj.imp (hsome _) (Or.imp (hsome _) (hsome _)))

/-- Wire-level reading: the run's point reads the wire map itself — `Poseidon.GroupMap.toGroup`,
the map the verifier runs to derive the per-proof `U` base. `groupMapCircuitRun_grants` at a
wire `Spec`, the pure model rewritten by `groupMapPure_toGroup`. -/
theorem groupMapCircuitRun_toGroup_grants (spec : Poseidon.GroupMap.Spec q)
    (nonResidue : ZMod q) {st : ProverState (ZMod q)} {t : FVar (ZMod q)} (ht : t.Scoped st) :
    st.env.Le (groupMapCircuitRun spec.sqrt.sqrt? (.ofSpec spec nonResidue) st t).1.env ∧
      (groupMapCircuitRun spec.sqrt.sqrt? (.ofSpec spec nonResidue) st t).2.x.Scoped
        (groupMapCircuitRun spec.sqrt.sqrt? (.ofSpec spec nonResidue) st t).1 ∧
      (groupMapCircuitRun spec.sqrt.sqrt? (.ofSpec spec nonResidue) st t).2.y.Scoped
        (groupMapCircuitRun spec.sqrt.sqrt? (.ofSpec spec nonResidue) st t).1 ∧
      (groupMapCircuitRun spec.sqrt.sqrt? (.ofSpec spec nonResidue) st t).2.x.val
          (groupMapCircuitRun spec.sqrt.sqrt? (.ofSpec spec nonResidue) st t).1.env.toValuation
        = (Poseidon.GroupMap.toGroup spec (t.val st.env.toValuation)).x ∧
      (groupMapCircuitRun spec.sqrt.sqrt? (.ofSpec spec nonResidue) st t).2.y.val
          (groupMapCircuitRun spec.sqrt.sqrt? (.ofSpec spec nonResidue) st t).1.env.toValuation
        = (Poseidon.GroupMap.toGroup spec (t.val st.env.toValuation)).y := by
  have h := groupMapCircuitRun_grants spec.sqrt.sqrt? (.ofSpec spec nonResidue) ht
  rw [groupMapPure_toGroup] at h
  exact h

end Wire

end Snarky.Kimchi
