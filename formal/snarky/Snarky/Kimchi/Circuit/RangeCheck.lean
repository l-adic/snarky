import Snarky.Kimchi.Circuit.EndoScalar
import Snarky.Circuit.DSL.SizedF

/-!
# Range checks built on the EndoScalar gate

Port of `Snarky.Circuit.Kimchi.RangeCheck`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/RangeCheck.purs): `toField` at 8
rows decomposes a 128-bit value across 16-bit rows, which doubles as a 128-bit range
check — cheaper than bit unpacking. `rangeCheck128` asserts the fit and discards the
decomposition; `lowest128Bits'` splits a field element into 128-bit halves,
range-checks the high half and — under `constrainLowBits` — the low one (OCaml
`squeeze_challenge` vs `squeeze_scalar`), pins the recombination, and returns the
low half.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS's type-level `FieldSizeInBits f 255` constraint renders as no hypothesis: the
  gadget emits the same ops at any field, and the laws carry the width facts they
  need (`nReconstruct_lt`'s `4^64 = 2^128` budget, the split's faithfulness).
- PS's `SizedF.fromField` advice partiality (`unsafePartial fromJust`) is total
  here: the split representatives are casts of reduced naturals, in range by
  construction.
-/

namespace Snarky.Kimchi

open Snarky Std.Do

variable {F c : Type}

/-- 128-bit range assert (PS `rangeCheck128`): the `toField` decomposition at 8 rows
IS the check; the reconstruction result is discarded. -/
def rangeCheck128 [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (endo : FVar F) (v : SizedF 128 (FVar F)) :
    CircuitM F c PUnit := do
  let _ ← EndoScalar.toField (c := c) 8 v.val endo
  pure ⟨⟩

/-- The split advice (PS's `exists` body): the value's canonical representative,
split at `2^128` — low half first, matching OCaml's `Typ.(field * field)`. -/
private def lowestWit [Field F] [ToNat F] (x : FVar F) : AsProver F (F × F) := do
  let xv ← AsProver.readCVar x
  pure (((ToNat.toNat xv % 2 ^ 128 : ℕ) : F), ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F))

/-- Extract the lowest 128 bits (PS `lowest128Bits'`; OCaml `lowest_128_bits`):
witness the split `x = lo + hi·2^128`, range-check `hi` and — under
`constrainLowBits` — `lo` via the `EndoScalar` decomposition, pin the
recombination, and return the low half. -/
def lowest128Bits' [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (constrainLowBits : Bool) (endo x : FVar F) :
    CircuitM F c (SizedF 128 (FVar F)) := do
  let lohi ← witness (val := UnChecked (F × F)) (.mk <$> lowestWit x)
  let _ ← EndoScalar.toField (c := c) 8 lohi.val.2 endo
  if constrainLowBits then
    let _ ← EndoScalar.toField (c := c) 8 lohi.val.1 endo
    pure ⟨⟩
  assertEqual x (CVar.add_ lohi.val.1 (CVar.scale_ ((2 : F) ^ 128) lohi.val.2))
  pure ⟨lohi.val.1⟩

/-- OCaml `squeeze_challenge`'s flavor: both halves checked (PS `lowest128Bits`). -/
def lowest128Bits [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (endo x : FVar F) : CircuitM F c (SizedF 128 (FVar F)) :=
  lowest128Bits' true endo x

/-- The pure split (PS `lowest128BitsPure`): the low half of the canonical
representative. -/
def lowest128BitsPure [Field F] [ToNat F] (x : F) : SizedF 128 F :=
  ⟨((ToNat.toNat x % 2 ^ 128 : ℕ) : F)⟩

/-! ## The laws

The `EndoScalar` gate's register is the base-4 fold of 64 checked crumbs, so a
satisfying valuation reads the operand as the cast of a natural below
`4^64 = 2^128` (`nReconstruct_lt`) — the range fact, extracted with no fresh
constraint content. Completeness is `toField`'s at the honest decomposition. -/

open Kimchi.Gate.EndoScalar (nReconstruct_lt) in
/-- `rangeCheck128` is sound: any satisfying valuation reads the operand as a
natural below `2^128` — the val-level `SizedF` contract. -/
theorem rangeCheck128_spec [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo : FVar F) (v : SizedF 128 (FVar F))
    (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) =>
        ∃ n : ℕ, n < 2 ^ 128 ∧ v.val.val V = (n : F)) Q⦄
    (rangeCheck128 (c := KimchiConstraint F) endo v)
    ⦃Q⦄ := by
  simp only [rangeCheck128]
  mvcgen
  rename_i s hpre
  refine EndoScalar.toField_spec h2 h3 8 v.val endo _ _ ?_
  intro r nv hr
  mvcgen
  refine hpre ⟨⟩ _ ?_
  obtain ⟨crumbs, hvalid, hlen, -, hval⟩ := hr
  obtain ⟨n, hlt, hcast⟩ := nReconstruct_lt h2 h3 crumbs hvalid
  refine ⟨n, ?_, by rw [hval, hcast]⟩
  calc n < 4 ^ crumbs.length := hlt
    _ = 2 ^ 128 := by rw [hlen]; norm_num

/-- `rangeCheck128` is complete: the honest run accepts on a readable in-range
operand (`SizedF.Fits` — the width the tag promises is the width the gate checks). -/
theorem rangeCheck128_complete_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (endo : FVar F) (v : SizedF 128 (FVar F))
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (v.val.eval env).isOk ∧ (endo.eval env).isOk ∧ v.Fits env)
        (fun _ _ _ => True) Q⦄
    (rangeCheck128 (c := KimchiProverC F) endo v)
    ⦃Q⦄ := by
  simp only [rangeCheck128]
  mvcgen [EndoScalar.toField_complete_spec]
  rename_i st hpre
  obtain ⟨⟨hok, hoke, hfits⟩, hk⟩ := hpre
  refine ⟨⟨hok, hoke, fun vv hv => ?_⟩, fun r st' hr hle => ?_⟩
  · have hlt := hfits vv hv
    calc ToNat.toNat vv < 2 ^ 128 := hlt
      _ = 4 ^ (8 * 8) := by norm_num
  mvcgen
  exact hk ⟨⟩ st' hle

open Kimchi.Gate.EndoScalar (nReconstruct_lt) in
/-- `lowest128Bits'` is sound: the operand reads as `lo + 2^128·hi` for the returned
low half and SOME high half below `2^128`; the low half is below `2^128` exactly
when `constrainLowBits` asked for it — OCaml's `squeeze_challenge` /
`squeeze_scalar` split. -/
theorem lowest128Bits'_spec [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (constrainLowBits : Bool) (endo x : FVar F)
    (Q : PostCond (SizedF 128 (FVar F)) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : SizedF 128 (FVar F)) =>
        ∃ hi : F,
          x.val V = r.val.val V + 2 ^ 128 * hi ∧
          (∃ n : ℕ, n < 2 ^ 128 ∧ hi = (n : F)) ∧
          (constrainLowBits = true →
            ∃ n : ℕ, n < 2 ^ 128 ∧ r.val.val V = (n : F))) Q⦄
    (lowest128Bits' (c := KimchiConstraint F) constrainLowBits endo x)
    ⦃Q⦄ := by
  simp only [lowest128Bits']
  mvcgen
  rename_i s hpre
  intro lohi _
  mvcgen
  refine EndoScalar.toField_spec h2 h3 8 lohi.val.2 endo _ _ ?_
  intro rhi nv2 hrhi
  mvcgen
  · refine EndoScalar.toField_spec h2 h3 8 lohi.val.1 endo _ _ ?_
    intro rlo nv3 hrlo
    mvcgen
    intro _ nv4 heq
    mvcgen
    refine hpre ⟨lohi.val.1⟩ _ ?_
    obtain ⟨cH, hHv, hHl, -, hHval⟩ := hrhi
    obtain ⟨nH, hnHlt, hnHcast⟩ := nReconstruct_lt h2 h3 cH hHv
    obtain ⟨cL, hLv, hLl, -, hLval⟩ := hrlo
    obtain ⟨nL, hnLlt, hnLcast⟩ := nReconstruct_lt h2 h3 cL hLv
    refine ⟨(lohi.val.2 : FVar F).val s.V,
      by rw [heq]; simp [CVar.val_add_, CVar.val_scale_],
      ⟨nH, by calc nH < 4 ^ cH.length := hnHlt
          _ = 2 ^ 128 := by rw [hHl]; norm_num,
        by rw [hHval, hnHcast]⟩,
      fun _ => ⟨nL, by calc nL < 4 ^ cL.length := hnLlt
          _ = 2 ^ 128 := by rw [hLl]; norm_num,
        by rw [hLval, hnLcast]⟩⟩
  · rename_i hcb
    intro _ nv4 heq
    mvcgen
    refine hpre ⟨lohi.val.1⟩ _ ?_
    obtain ⟨cH, hHv, hHl, -, hHval⟩ := hrhi
    obtain ⟨nH, hnHlt, hnHcast⟩ := nReconstruct_lt h2 h3 cH hHv
    refine ⟨(lohi.val.2 : FVar F).val s.V,
      by rw [heq]; simp [CVar.val_add_, CVar.val_scale_],
      ⟨nH, by calc nH < 4 ^ cH.length := hnHlt
          _ = 2 ^ 128 := by rw [hHl]; norm_num,
        by rw [hHval, hnHcast]⟩,
      fun hcb' => absurd hcb' hcb⟩

/-- `lowest128Bits'` is complete — the honest side of OCaml's `lowest_128_bits`:
on a readable operand whose split representatives are themselves faithful
(free at the deployed 255-bit fields), the honest run accepts and the result reads
as the pure split `lowest128BitsPure`. -/
theorem lowest128Bits'_complete_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (constrainLowBits : Bool) (endo x : FVar F)
    (Q : PostCond (SizedF 128 (FVar F))
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env =>
          (x.eval env).isOk ∧ (endo.eval env).isOk ∧
          (∀ vv, x.eval env = .ok vv →
            ToNat.toNat vv / 2 ^ 128 < 2 ^ 128 ∧
            ToNat.toNat ((ToNat.toNat vv % 2 ^ 128 : ℕ) : F)
              = ToNat.toNat vv % 2 ^ 128 ∧
            ToNat.toNat ((ToNat.toNat vv / 2 ^ 128 : ℕ) : F)
              = ToNat.toNat vv / 2 ^ 128))
        (fun env r env' => ∀ vv, x.eval env = .ok vv →
          r.val.eval env' = .ok (lowest128BitsPure vv).val)
        Q⦄
    (lowest128Bits' (c := KimchiProverC F) constrainLowBits endo x)
    ⦃Q⦄ := by
  simp only [lowest128Bits']
  mvcgen [EndoScalar.toField_complete_spec]
  rename_i st hpre
  obtain ⟨⟨hok, hoke, hsec⟩, hk⟩ := hpre
  obtain ⟨vv, hv⟩ := CVar.evalOk hok
  obtain ⟨ev, he⟩ := CVar.evalOk hoke
  obtain ⟨hhilt, hlosec, hhisec⟩ := hsec vv hv
  have hfaith := LawfulToNat.cast_toNat vv
  have hrecomb : ((ToNat.toNat vv % 2 ^ 128 : ℕ) : F)
      + (2 : F) ^ 128 * ((ToNat.toNat vv / 2 ^ 128 : ℕ) : F) = vv := by
    have h1 : (ToNat.toNat vv % 2 ^ 128) + 2 ^ 128 * (ToNat.toNat vv / 2 ^ 128)
        = ToNat.toNat vv := Nat.mod_add_div _ _
    calc ((ToNat.toNat vv % 2 ^ 128 : ℕ) : F)
        + (2 : F) ^ 128 * ((ToNat.toNat vv / 2 ^ 128 : ℕ) : F)
        = ((ToNat.toNat vv % 2 ^ 128 + 2 ^ 128 * (ToNat.toNat vv / 2 ^ 128) : ℕ)
            : F) := by push_cast; ring
      _ = ((ToNat.toNat vv : ℕ) : F) := by rw [h1]
      _ = vv := hfaith
  have hwit : (UnChecked.mk <$> lowestWit x) st.env
      = .ok ⟨(((ToNat.toNat vv % 2 ^ 128 : ℕ) : F),
          ((ToNat.toNat vv / 2 ^ 128 : ℕ) : F))⟩ := by
    simp [lowestWit, AsProver.readCVar, hv, Functor.map, Bind.bind, ReaderT.bind,
      Except.bind, Except.map, Pure.pure, ReaderT.pure, Except.pure]
  refine ⟨by rw [hwit]; rfl, fun lohi st₁ hgrant hle₁ => ?_⟩
  obtain ⟨hlo, hhi⟩ := hgrant _ hwit
  mvcgen [EndoScalar.toField_complete_spec]
  refine ⟨⟨by rw [hhi]; rfl, by rw [CVar.eval_le hle₁ he]; rfl,
    fun hv' hhv' => ?_⟩, fun rhi st₂ hrhi hle₂ => ?_⟩
  · rw [hhi] at hhv'
    injection hhv' with hhv'
    subst hhv'
    rw [hhisec]
    calc ToNat.toNat vv / 2 ^ 128 < 2 ^ 128 := hhilt
      _ = 4 ^ (8 * 8) := by norm_num
  mvcgen [EndoScalar.toField_complete_spec]
  · refine ⟨⟨by rw [CVar.eval_le hle₂ hlo]; rfl,
      by rw [CVar.eval_le (hle₁.trans hle₂) he]; rfl, fun lv hlv => ?_⟩,
      fun rlo st₃ hrlo hle₃ => ?_⟩
    · rw [CVar.eval_le hle₂ hlo] at hlv
      injection hlv with hlv
      subst hlv
      rw [hlosec]
      calc ToNat.toNat vv % 2 ^ 128 < 2 ^ 128 := Nat.mod_lt _ (by positivity)
        _ = 4 ^ (8 * 8) := by norm_num
    mvcgen
    have hsum := CVar.eval_add_ (CVar.eval_le (hle₂.trans hle₃) hlo)
      (CVar.eval_scale_ (CVar.eval_le (hle₂.trans hle₃) hhi) ((2 : F) ^ 128))
    refine ⟨⟨by rw [CVar.eval_le ((hle₁.trans hle₂).trans hle₃) hv]; rfl,
      by rw [hsum]; rfl, fun xv sv hxv hsv => ?_⟩, fun u st₄ hle₄ => ?_⟩
    · rw [CVar.eval_le ((hle₁.trans hle₂).trans hle₃) hv] at hxv
      injection hxv with hxv
      rw [hsum] at hsv
      injection hsv with hsv
      subst hxv hsv
      exact hrecomb.symm
    mvcgen
    refine hk ⟨lohi.val.1⟩ st₄ (fun vv' hv' => ?_)
      (((hle₁.trans hle₂).trans hle₃).trans hle₄)
    rw [hv] at hv'
    injection hv' with hv'
    subst hv'
    exact CVar.eval_le ((hle₂.trans hle₃).trans hle₄) hlo
  · have hsum := CVar.eval_add_ (CVar.eval_le hle₂ hlo)
      (CVar.eval_scale_ (CVar.eval_le hle₂ hhi) ((2 : F) ^ 128))
    refine ⟨⟨by rw [CVar.eval_le (hle₁.trans hle₂) hv]; rfl,
      by rw [hsum]; rfl, fun xv sv hxv hsv => ?_⟩, fun u st₄ hle₄ => ?_⟩
    · rw [CVar.eval_le (hle₁.trans hle₂) hv] at hxv
      injection hxv with hxv
      rw [hsum] at hsv
      injection hsv with hsv
      subst hxv hsv
      exact hrecomb.symm
    mvcgen
    refine hk ⟨lohi.val.1⟩ st₄ (fun vv' hv' => ?_)
      ((hle₁.trans hle₂).trans hle₄)
    rw [hv] at hv'
    injection hv' with hv'
    subst hv'
    exact CVar.eval_le (hle₂.trans hle₄) hlo

end Snarky.Kimchi
