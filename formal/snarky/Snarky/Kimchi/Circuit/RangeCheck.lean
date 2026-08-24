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
theorem rangeCheck128_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo : FVar F) (v : SizedF 128 (FVar F)) :
    ⦃⌜True⌝⦄
    (rangeCheck128 (c := Builder V (KimchiConstraint F)) endo v)
    ⦃⇓ _ _ => ⌜∃ n : ℕ, n < 2 ^ 128 ∧ v.val.val V = (n : F)⌝⦄ := by
  simp only [rangeCheck128]
  have ht := EndoScalar.toField_spec (V := V) h2 h3 8 v.val endo
  mvcgen [ht]
  rename_i r _ hr
  obtain ⟨crumbs, hvalid, hlen, -, hval⟩ := hr
  obtain ⟨n, hlt, hcast⟩ := nReconstruct_lt h2 h3 crumbs hvalid
  refine ⟨n, ?_, by rw [hval, hcast]⟩
  calc n < 4 ^ crumbs.length := hlt
    _ = 2 ^ 128 := by rw [hlen]; norm_num

/-- The state after `rangeCheck128`'s honest run: `toField`'s, the result dropped. -/
def rangeCheck128Run [Field F] [DecidableEq F] [ToNat F] (st : ProverState F) (endo : FVar F)
    (v : SizedF 128 (FVar F)) : ProverState F :=
  (EndoScalar.toFieldRun st 8 v.val endo).1

/-- `rangeCheck128`'s honest run on an in-range operand (`SizedF.Fits` — the width the
tag promises is the width the gate checks) lands at `rangeCheck128Run`. -/
theorem rangeCheck128_run [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] {endo : FVar F}
    {v : SizedF 128 (FVar F)} (st : ProverState F) (hv : v.val.Scoped st) (he : endo.Scoped st)
    (hfits : v.Fits st.env.toValuation) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (rangeCheck128 (c := KimchiConstraint F) endo v) st.nv st.env
      = .ok ((rangeCheck128Run st endo v).out ⟨⟩) := by
  have hlt : ToNat.toNat (v.val.val st.env.toValuation) < 4 ^ (8 * 8) :=
    calc ToNat.toNat (v.val.val st.env.toValuation) < 2 ^ 128 := hfits
      _ = 4 ^ (8 * 8) := by norm_num
  simp only [rangeCheck128, prove_bind, EndoScalar.toField_run 8 st hv he hlt, Except.bind]
  rfl

open Kimchi.Gate.EndoScalar (nReconstruct_lt) in
/-- `lowest128Bits'` is sound: the operand reads as `lo + 2^128·hi` for the returned
low half and SOME high half below `2^128`; the low half is below `2^128` exactly
when `constrainLowBits` asked for it — OCaml's `squeeze_challenge` /
`squeeze_scalar` split. -/
theorem lowest128Bits'_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (constrainLowBits : Bool) (endo x : FVar F) :
    ⦃⌜True⌝⦄
    (lowest128Bits' (c := Builder V (KimchiConstraint F)) constrainLowBits endo x)
    ⦃⇓ r _ => ⌜∃ hi : F,
          x.val V = r.val.val V + 2 ^ 128 * hi ∧
          (∃ n : ℕ, n < 2 ^ 128 ∧ hi = (n : F)) ∧
          (constrainLowBits = true →
            ∃ n : ℕ, n < 2 ^ 128 ∧ r.val.val V = (n : F))⌝⦄ := by
  simp only [lowest128Bits']
  have ht := EndoScalar.toField_spec (V := V) h2 h3 8
  mvcgen [ht]
  · rename_i lohi _ _ rhi _ _ hrhi rlo _ hrlo _ _ heq
    obtain ⟨cH, hHv, hHl, -, hHval⟩ := hrhi
    obtain ⟨nH, hnHlt, hnHcast⟩ := nReconstruct_lt h2 h3 cH hHv
    obtain ⟨cL, hLv, hLl, -, hLval⟩ := hrlo
    obtain ⟨nL, hnLlt, hnLcast⟩ := nReconstruct_lt h2 h3 cL hLv
    refine ⟨(lohi.val.2 : FVar F).val V,
      by rw [heq]; simp [CVar.val_add_, CVar.val_scale_],
      ⟨nH, by calc nH < 4 ^ cH.length := hnHlt
          _ = 2 ^ 128 := by rw [hHl]; norm_num,
        by rw [hHval, hnHcast]⟩,
      fun _ => ⟨nL, by calc nL < 4 ^ cL.length := hnLlt
          _ = 2 ^ 128 := by rw [hLl]; norm_num,
        by rw [hLval, hnLcast]⟩⟩
  · rename_i lohi _ _ rhi hcb _ hrhi _ _ heq
    obtain ⟨cH, hHv, hHl, -, hHval⟩ := hrhi
    obtain ⟨nH, hnHlt, hnHcast⟩ := nReconstruct_lt h2 h3 cH hHv
    refine ⟨(lohi.val.2 : FVar F).val V,
      by rw [heq]; simp [CVar.val_add_, CVar.val_scale_],
      ⟨nH, by calc nH < 4 ^ cH.length := hnHlt
          _ = 2 ^ 128 := by rw [hHl]; norm_num,
        by rw [hHval, hnHcast]⟩,
      fun hcb' => absurd hcb' hcb⟩

/-- The state and result of `lowest128Bits'`'s honest run: the split allocated, the
high half's range check, the low half's when asked, the recombination pin (nothing
allocated), the low half returned. -/
def lowest128Bits'Run [Field F] [DecidableEq F] [ToNat F] (st : ProverState F)
    (constrainLowBits : Bool) (endo x : FVar F) : ProverState F × SizedF 128 (FVar F) :=
  let st₁ := st.extendMany [((ToNat.toNat (x.val st.env.toValuation) % 2 ^ 128 : ℕ) : F),
    ((ToNat.toNat (x.val st.env.toValuation) / 2 ^ 128 : ℕ) : F)]
  let st₂ := (EndoScalar.toFieldRun st₁ 8 (.var (st.nv + 1)) endo).1
  let st₃ := if constrainLowBits then (EndoScalar.toFieldRun st₂ 8 (.var st.nv) endo).1 else st₂
  (st₃, ⟨.var st.nv⟩)

/-- `lowest128Bits'`'s honest run — the honest side of OCaml's `lowest_128_bits`: on an
in-scope operand whose split representatives are themselves faithful (free at the
deployed 255-bit fields), it lands at `lowest128Bits'Run`. -/
theorem lowest128Bits'_run [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (constrainLowBits : Bool) {endo x : FVar F} (st : ProverState F) (hx : x.Scoped st)
    (he : endo.Scoped st)
    (hhilt : ToNat.toNat (x.val st.env.toValuation) / 2 ^ 128 < 2 ^ 128)
    (hlosec : ToNat.toNat ((ToNat.toNat (x.val st.env.toValuation) % 2 ^ 128 : ℕ) : F)
      = ToNat.toNat (x.val st.env.toValuation) % 2 ^ 128)
    (hhisec : ToNat.toNat ((ToNat.toNat (x.val st.env.toValuation) / 2 ^ 128 : ℕ) : F)
      = ToNat.toNat (x.val st.env.toValuation) / 2 ^ 128) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (lowest128Bits' (c := KimchiConstraint F) constrainLowBits endo x) st.nv st.env
      = .ok ((lowest128Bits'Run st constrainLowBits endo x).1.out
          (lowest128Bits'Run st constrainLowBits endo x).2) := by
  generalize hxv : x.val st.env.toValuation = xv at hhilt hlosec hhisec ⊢
  have hrecomb : ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F)
      + (2 : F) ^ 128 * ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) = xv := by
    have h1 : (ToNat.toNat xv % 2 ^ 128) + 2 ^ 128 * (ToNat.toNat xv / 2 ^ 128)
        = ToNat.toNat xv := Nat.mod_add_div _ _
    calc ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) + (2 : F) ^ 128 * ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F)
        = ((ToNat.toNat xv % 2 ^ 128 + 2 ^ 128 * (ToNat.toNat xv / 2 ^ 128) : ℕ) : F) := by
          push_cast; ring
      _ = ((ToNat.toNat xv : ℕ) : F) := by rw [h1]
      _ = xv := LawfulToNat.cast_toNat xv
  have hle₁ := st.le_extendMany [((ToNat.toNat xv % 2 ^ 128 : ℕ) : F),
    ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F)]
  have hlo : (CVar.var st.nv).Scoped (st.extendMany [((ToNat.toNat xv % 2 ^ 128 : ℕ) : F),
      ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F)]) := ProverState.mem_extendMany_head ..
  have hhi : (CVar.var (st.nv + 1)).Scoped (st.extendMany [((ToNat.toNat xv % 2 ^ 128 : ℕ) : F),
      ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F)]) := st.new_mem_extendMany (i := 1) (by simp)
  have hlov : (CVar.var st.nv).val (st.extendMany [((ToNat.toNat xv % 2 ^ 128 : ℕ) : F),
      ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F)]).env.toValuation
      = ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) := by
    show (st.extendMany _).env.toValuation st.nv = _
    simp
  have hhiv : (CVar.var (st.nv + 1)).val (st.extendMany [((ToNat.toNat xv % 2 ^ 128 : ℕ) : F),
      ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F)]).env.toValuation
      = ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) := by
    show (st.extendMany _).env.toValuation (st.nv + 1) = _
    rw [ProverState.get_extendMany_new st (by simp)]
    rfl
  have hlt4 : ToNat.toNat ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) < 4 ^ (8 * 8) := by
    rw [hhisec]
    calc ToNat.toNat xv / 2 ^ 128 < 2 ^ 128 := hhilt
      _ = 4 ^ (8 * 8) := by norm_num
  have hlt4' : ToNat.toNat ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) < 4 ^ (8 * 8) := by
    rw [hlosec]
    calc ToNat.toNat xv % 2 ^ 128 < 2 ^ 128 := Nat.mod_lt _ (by positivity)
      _ = 4 ^ (8 * 8) := by norm_num
  have hg := EndoScalar.toFieldRun_grants 8 (st := st.extendMany
    [((ToNat.toNat xv % 2 ^ 128 : ℕ) : F), ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F)]) hhi (he.of_le hle₁)
  simp only [lowest128Bits', prove_bind]
  rw [prove_witness_run (w := UnChecked.mk <$> lowestWit x) st
    (.bind (.bind (.readCVar hx) fun _ => trivial) fun _ => trivial)
    (v := ⟨(((ToNat.toNat xv % 2 ^ 128 : ℕ) : F), ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F))⟩)
    (by simp [lowestWit, Except.bind, hxv])]
  rw [show (CircuitType.valueToFields (F := F) (var := UnChecked (FVar F × FVar F))
      (⟨(((ToNat.toNat xv % 2 ^ 128 : ℕ) : F), ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F))⟩ :
        UnChecked (F × F))).toList
      = [((ToNat.toNat xv % 2 ^ 128 : ℕ) : F), ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F)] from rfl,
    show CircuitType.fieldsToVar (F := F) (val := UnChecked (F × F))
      (mapVec CVar.var (allocRange st.nv (CircuitType.size F (UnChecked (F × F)))))
      = ⟨(.var st.nv, .var (st.nv + 1))⟩ from rfl]
  simp only [Except.bind]
  rw [EndoScalar.toField_run 8 _ hhi (he.of_le hle₁) (by rw [hhiv]; exact hlt4)]
  simp only [lowest128Bits'Run]
  rw [hxv]
  cases constrainLowBits with
  | true =>
    simp only [↓reduceIte, prove_bind]
    rw [EndoScalar.toField_run 8 _ (hlo.of_le hg.le) (he.of_le (hle₁.trans hg.le))
      (by rw [CVar.val_of_le hg.le hlo, hlov]; exact hlt4')]
    simp only [Except.bind, prove_pure]
    have hg' := EndoScalar.toFieldRun_grants 8 (st := (EndoScalar.toFieldRun (st.extendMany
      [((ToNat.toNat xv % 2 ^ 128 : ℕ) : F), ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F)]) 8
      (.var (st.nv + 1)) endo).1) (hlo.of_le hg.le) (he.of_le (hle₁.trans hg.le))
    have hle := hle₁.trans (hg.le.trans hg'.le)
    rw [assertEqual_run _ (hx.of_le hle)
      (CVar.Scoped.add_ (hlo.of_le (hg.le.trans hg'.le))
        (CVar.Scoped.scale_ _ (hhi.of_le (hg.le.trans hg'.le))))
      (by
        rw [CVar.val_of_le hle hx, hxv, CVar.val_add_, CVar.val_scale_,
          CVar.val_of_le (hg.le.trans hg'.le) hlo, CVar.val_of_le (hg.le.trans hg'.le) hhi,
          hlov, hhiv, hrecomb])]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, prove_bind, prove_pure, Except.bind]
    rw [assertEqual_run _ (hx.of_le (hle₁.trans hg.le))
      (CVar.Scoped.add_ (hlo.of_le hg.le) (CVar.Scoped.scale_ _ (hhi.of_le hg.le)))
      (by
        rw [CVar.val_of_le (hle₁.trans hg.le) hx, hxv, CVar.val_add_, CVar.val_scale_,
          CVar.val_of_le hg.le hlo, CVar.val_of_le hg.le hhi, hlov, hhiv, hrecomb])]

/-- `lowest128Bits'Run`'s low half reads as the pure split. -/
theorem lowest128Bits'Run_grants [Field F] [DecidableEq F] [ToNat F] (constrainLowBits : Bool)
    {endo x : FVar F} (st : ProverState F) (he : endo.Scoped st) :
    Grants F st ((lowest128Bits'Run st constrainLowBits endo x).1,
      (lowest128Bits'Run st constrainLowBits endo x).2.val)
      (lowest128BitsPure (x.val st.env.toValuation)).val := by
  have hle₁ := st.le_extendMany [((ToNat.toNat (x.val st.env.toValuation) % 2 ^ 128 : ℕ) : F),
    ((ToNat.toNat (x.val st.env.toValuation) / 2 ^ 128 : ℕ) : F)]
  have hlo : (CVar.var st.nv).Scoped (st.extendMany
      [((ToNat.toNat (x.val st.env.toValuation) % 2 ^ 128 : ℕ) : F),
        ((ToNat.toNat (x.val st.env.toValuation) / 2 ^ 128 : ℕ) : F)]) :=
    ProverState.mem_extendMany_head ..
  have hhi : (CVar.var (st.nv + 1)).Scoped (st.extendMany
      [((ToNat.toNat (x.val st.env.toValuation) % 2 ^ 128 : ℕ) : F),
        ((ToNat.toNat (x.val st.env.toValuation) / 2 ^ 128 : ℕ) : F)]) :=
    st.new_mem_extendMany (i := 1) (by simp)
  have hlov : (CVar.var st.nv).val (st.extendMany
      [((ToNat.toNat (x.val st.env.toValuation) % 2 ^ 128 : ℕ) : F),
        ((ToNat.toNat (x.val st.env.toValuation) / 2 ^ 128 : ℕ) : F)]).env.toValuation
      = ((ToNat.toNat (x.val st.env.toValuation) % 2 ^ 128 : ℕ) : F) := by
    show (st.extendMany _).env.toValuation st.nv = _
    simp
  have hg := EndoScalar.toFieldRun_grants 8 (st := st.extendMany
    [((ToNat.toNat (x.val st.env.toValuation) % 2 ^ 128 : ℕ) : F),
      ((ToNat.toNat (x.val st.env.toValuation) / 2 ^ 128 : ℕ) : F)]) hhi (he.of_le hle₁)
  simp only [lowest128Bits'Run]
  cases constrainLowBits with
  | true =>
    simp only [↓reduceIte]
    have hg' := EndoScalar.toFieldRun_grants 8 (st := (EndoScalar.toFieldRun (st.extendMany
      [((ToNat.toNat (x.val st.env.toValuation) % 2 ^ 128 : ℕ) : F),
        ((ToNat.toNat (x.val st.env.toValuation) / 2 ^ 128 : ℕ) : F)]) 8
      (.var (st.nv + 1)) endo).1) (hlo.of_le hg.le) (he.of_le (hle₁.trans hg.le))
    exact Grants.fvar (hle₁.trans (hg.le.trans hg'.le)) (hlo.of_le (hg.le.trans hg'.le))
      (by rw [CVar.val_of_le (hg.le.trans hg'.le) hlo, hlov]; rfl)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact Grants.fvar (hle₁.trans hg.le) (hlo.of_le hg.le)
      (by rw [CVar.val_of_le hg.le hlo, hlov]; rfl)

end Snarky.Kimchi
