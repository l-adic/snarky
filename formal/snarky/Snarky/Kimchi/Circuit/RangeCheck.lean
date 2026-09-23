import Snarky.Tactic
import Snarky.Kimchi.Circuit.EndoScalar
import Snarky.DSL.SizedF

/-!
# Range checks built on the EndoScalar gate

Transcribes packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/RangeCheck.purs.
`EndoScalar.toField` at 8 rows decomposes its operand into 128 bits, so it doubles as a
128-bit range check. `rangeCheck128` asserts the fit and discards the decomposition.
`split128Below` splits a field element into 128-bit halves, range-checks the high half (and the
low one when asked), pins the recombination below a bound, and returns the low half.
`lowest128Bits'` is that split below the field modulus, so the halves are the canonical
representative's.

Each gadget is followed by its soundness spec and completeness law, then sealed `irreducible`;
the pure split `lowest128BitsPure` stays transparent, since the statements speak about it. No
law assumes a field width up front: each carries the width facts it needs.
-/

namespace Snarky.Kimchi

open Snarky Std.Do

variable {F c : Type}

/-! ## The 128-bit range check -/

/-- 128-bit range assert: the `EndoScalar.toField` decomposition is the check; its result is
discarded. -/
def rangeCheck128 [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (endo : FVar F) (v : SizedF 128 (FVar F)) :
    CircuitM F c PUnit := do
  let _ ← EndoScalar.toField (c := c) 8 v.val endo
  pure ⟨⟩

/-- **Soundness** (`rangeCheck128`): any satisfying valuation reads the operand as a
natural below `2^128` — the value-level `SizedF` contract. -/
theorem rangeCheck128_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo : FVar F) (v : SizedF 128 (FVar F)) :
    ⦃⌜True⌝⦄
    rangeCheck128 (c := Builder V (KimchiConstraint F)) endo v
    ⦃⇓ _ _ => ⌜∃ n : ℕ, n < 2 ^ 128 ∧ v.val.val V = (n : F)⌝⦄ := by
  have htf := EndoScalar.toField_spec (V := V) h2 h3 v.val endo
  simp only [rangeCheck128]
  mvcgen [htf]
  rename_i _ _ hr
  obtain ⟨n, hlt, hval, -⟩ := hr
  exact ⟨n, hlt, hval⟩

/-- **Completeness** (`rangeCheck128`): the honest run accepts on an operand that reads a
value inside the tagged width. -/
theorem rangeCheck128_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo : FVar F) (v : SizedF 128 (FVar F))
    (vv ev : F) (hfits : ToNat.toNat vv < 2 ^ 128) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => CircuitType.ReadsAs (val := F) st v.val vv ∧
        CircuitType.ReadsAs (val := F) st endo ev)
      (rangeCheck128 (c := KimchiConstraint F) endo v)
      (fun _ _ => True) := by
  simp only [rangeCheck128]
  complete_walk
  exact Complete.pure_of fun _ _ => trivial

attribute [irreducible] rangeCheck128

/-! ## The split -/

/-- The pure split: the low half of the canonical representative. -/
def lowest128BitsPure [Field F] [ToNat F] (x : F) : SizedF 128 F :=
  ⟨((ToNat.toNat x % 2 ^ 128 : ℕ) : F)⟩

/-- The split advice: the canonical representative split at `2^128`, low half first. -/
private def lowestWit [Field F] [ToNat F] (x : FVar F) : AsProver F (F × F) := do
  let xv ← AsProver.readCVar x
  pure (((ToNat.toNat xv % 2 ^ 128 : ℕ) : F), ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F))

/-- The field's modulus: the canonical representative of `-1`, plus one. -/
def fieldModulus (F : Type) [Field F] [ToNat F] : ℕ := ToNat.toNat (-1 : F) + 1

/-- The limb comparison: `lo + 2^128·hi < bound` for 128-bit limbs,
as one range-checked difference — where `hi` equals the bound's high limb, `bound_lo − 1 − lo`;
elsewhere `bound_hi − 1 − hi`. A negative difference wraps past `2^128` and fails, so the
first case pins `lo < bound_lo` and the second `hi < bound_hi`. -/
private def assertSplitBelow [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (endo lo hi : FVar F) (bound : ℕ) : CircuitM F c PUnit := do
  let boundHi : F := ((bound / 2 ^ 128 : ℕ) : F)
  let boundLo : F := ((bound % 2 ^ 128 : ℕ) : F)
  let hiIsTop ← equals hi (.const boundHi)
  let d ← selectField hiIsTop (CVar.sub_ (.const (boundLo - 1)) lo)
    (CVar.sub_ (.const (boundHi - 1)) hi)
  let _ ← EndoScalar.toField (c := c) 8 d endo
  pure ⟨⟩

/-- The split below a bound: witness `x = lo + 2^128·hi`, range-check `hi` (and `lo` under
`constrainLowBits`), pin the recombination and `lo + 2^128·hi < bound`, and return `lo`. -/
def split128Below [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (constrainLowBits : Bool) (endo : FVar F) (bound : ℕ) (x : FVar F) :
    CircuitM F c (SizedF 128 (FVar F)) := do
  let lohi ← witness (val := UnChecked (F × F)) (.mk <$> lowestWit x)
  let _ ← EndoScalar.toField (c := c) 8 lohi.val.2 endo
  if constrainLowBits then
    let _ ← EndoScalar.toField (c := c) 8 lohi.val.1 endo
    pure ⟨⟩
  assertEqual x (CVar.add_ lohi.val.1 (CVar.scale_ ((2 : F) ^ 128) lohi.val.2))
  assertSplitBelow endo lohi.val.1 lohi.val.2 bound
  pure ⟨lohi.val.1⟩

/-- The lowest 128 bits: the split below the field modulus, so the low half is the canonical
representative's. -/
def lowest128Bits' [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (constrainLowBits : Bool) (endo x : FVar F) :
    CircuitM F c (SizedF 128 (FVar F)) :=
  split128Below constrainLowBits endo (fieldModulus F) x

/-- The limb comparison with a trivial postcondition, for callers' `mvcgen` to step over. -/
private theorem assertSplitBelow_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo lo hi : FVar F) (bound : ℕ) :
    ⦃⌜True⌝⦄
    assertSplitBelow (c := Builder V (KimchiConstraint F)) endo lo hi bound
    ⦃⇓ _ _ => ⌜True⌝⦄ := by
  have htf := fun (y : FVar F) => EndoScalar.toField_spec (V := V) h2 h3 y endo
  simp only [assertSplitBelow]
  mvcgen [htf]

/-- **Soundness** (`assertSplitBelow`, the comparison): where naturals below `2^130` cast
injectively and the bound fits in 256 bits, any satisfying valuation reading the limbs as
128-bit naturals reads them below the bound. -/
private theorem assertSplitBelow_below {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hinj : ∀ a b : ℕ, a < 2 ^ 130 → b < 2 ^ 130 → (a : F) = b → a = b)
    (endo lo hi : FVar F) (bound : ℕ) (hbound : bound < 2 ^ 256) :
    ⦃⌜True⌝⦄
    assertSplitBelow (c := Builder V (KimchiConstraint F)) endo lo hi bound
    ⦃⇓ _ _ => ⌜∀ l h : ℕ, l < 2 ^ 128 → h < 2 ^ 128 → lo.val V = l → hi.val V = h →
      l + 2 ^ 128 * h < bound⌝⦄ := by
  have htf := fun (y : FVar F) => EndoScalar.toField_spec (V := V) h2 h3 y endo
  simp only [assertSplitBelow]
  mvcgen [htf]
  rename_i top _ htop _ _ hsel _ _ hd
  intro l h hl hh hlo hhi
  have hdm := Nat.mod_add_div bound (2 ^ 128)
  have hbh : bound / 2 ^ 128 < 2 ^ 128 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc bound < 2 ^ 256 := hbound
      _ = 2 ^ 128 * 2 ^ 128 := by norm_num
  have hbl : bound % 2 ^ 128 < 2 ^ 128 := Nat.mod_lt _ (by positivity)
  obtain ⟨n, hn, hv, -⟩ := hd
  by_cases hheq : h = bound / 2 ^ 128
  · -- equal high limbs: the selected difference pins the low limb below the bound's
    have htop1 : (↑top : CVar F).val V = bit true := by
      rw [htop]
      simp [CVar.val, hhi, hheq, bit]
    have hd := hsel true htop1
    simp only [if_true, CVar.val_sub_, CVar.val, hlo] at hd
    rw [hd] at hv
    have he : bound % 2 ^ 128 = l + n + 1 :=
      hinj _ _ (by omega) (by omega) (by push_cast; linear_combination hv)
    rw [← hheq] at hdm
    nlinarith
  · -- a smaller high limb leaves room for any low limb
    have hne : (h : F) ≠ ((bound / 2 ^ 128 : ℕ) : F) :=
      fun hc => hheq (hinj _ _ (by omega) (by omega) hc)
    have htop0 : (↑top : CVar F).val V = bit false := by
      rw [htop]
      simpa [CVar.val, hhi, bit] using hne
    have hd := hsel false htop0
    simp only [Bool.false_eq_true, if_false, CVar.val_sub_, CVar.val, hhi] at hd
    rw [hd] at hv
    have he : bound / 2 ^ 128 = h + n + 1 :=
      hinj _ _ (by omega) (by omega) (by push_cast; linear_combination hv)
    have hm : 2 ^ 128 * (h + 1) ≤ 2 ^ 128 * (bound / 2 ^ 128) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [mul_add, mul_one] at hm
    generalize bound / 2 ^ 128 = bq at hm hdm
    generalize 2 ^ 128 * bq = kb at hm hdm
    generalize 2 ^ 128 * h = kh at hm ⊢
    omega

/-- The modulus read off a lawful field is its cardinality: `-1`'s representative is the
largest one. -/
theorem fieldModulus_eq_card [Field F] [ToNat F] [LawfulToNat F] :
    fieldModulus F = LawfulToNat.card (F := F) := by
  have hlt := LawfulToNat.toNat_lt (-1 : F)
  have hcast := LawfulToNat.cast_toNat (-1 : F)
  by_contra hne
  have hlt' : ToNat.toNat (-1 : F) + 1 < LawfulToNat.card (F := F) := by
    unfold fieldModulus at hne
    omega
  have h0 : ((ToNat.toNat (-1 : F) + 1 : ℕ) : F) = 0 := by
    push_cast
    rw [hcast]
    ring
  have hm := LawfulToNat.toNat_natCast (F := F) _ hlt'
  have hz := LawfulToNat.toNat_natCast (F := F) 0 (by omega)
  rw [h0] at hm
  rw [Nat.cast_zero] at hz
  omega

/-- **Completeness** (`assertSplitBelow`): the honest run accepts on limbs whose
recombination lies below the bound, where the bound is below `2^256` and at most the field's
cardinality. -/
@[complete_law]
private theorem assertSplitBelow_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo lo hi : FVar F) (bound lov hiv : ℕ) (ev : F)
    (hcard : bound ≤ LawfulToNat.card (F := F)) (hnarrow : bound < 2 ^ 256)
    (hbelow : lov + 2 ^ 128 * hiv < bound) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => CircuitType.ReadsAs (val := F) st lo (lov : F) ∧
        CircuitType.ReadsAs (val := F) st hi (hiv : F) ∧
        CircuitType.ReadsAs (val := F) st endo ev)
      (assertSplitBelow (c := KimchiConstraint F) endo lo hi bound)
      (fun _ _ => True) := by
  have hK : (0 : ℕ) < 2 ^ 128 := by positivity
  have hcast : ∀ n : ℕ, n < bound → ToNat.toNat ((n : ℕ) : F) = n :=
    fun n hn => LawfulToNat.toNat_natCast n (lt_of_lt_of_le hn hcard)
  have hdm := Nat.mod_add_div bound (2 ^ 128)
  have hhile : hiv ≤ bound / 2 ^ 128 := by
    rw [Nat.le_div_iff_mul_le hK]
    nlinarith
  have hbhlt : bound / 2 ^ 128 < 2 ^ 128 := by
    rw [Nat.div_lt_iff_lt_mul hK]
    calc bound < 2 ^ 256 := hnarrow
      _ = 2 ^ 128 * 2 ^ 128 := by norm_num
  have hbhb : bound / 2 ^ 128 < bound := Nat.div_lt_self (by omega) (by norm_num)
  -- the operands, read
  have hconst : ∀ {st : ProverState F} (k : F),
      CircuitType.ReadsAs (val := F) st (.const k : FVar F) k :=
    fun _ => ⟨CircuitType.scoped_fvar.mpr (CVar.scoped_const _ _),
      CircuitType.reads_fvar.mpr rfl⟩
  have hsubR : ∀ {st : ProverState F} {a b : FVar F} {av bv : F},
      CircuitType.ReadsAs (val := F) st a av → CircuitType.ReadsAs (val := F) st b bv →
      CircuitType.ReadsAs (val := F) st (CVar.sub_ a b) (av - bv) :=
    fun ha hb => ⟨CircuitType.scoped_fvar.mpr
        (CVar.Scoped.sub_ (CircuitType.scoped_fvar.mp ha.1) (CircuitType.scoped_fvar.mp hb.1)),
      CircuitType.reads_fvar.mpr (by
        rw [CVar.val_sub_, CircuitType.reads_fvar.mp ha.2, CircuitType.reads_fvar.mp hb.2])⟩
  simp only [assertSplitBelow]
  -- whether the high limb is the bound's
  refine Complete.seq (by complete_mono_tac)
    (Complete.imp (fun st h => ⟨h.2.1, hconst _⟩) (fun _ _ h => h)
      (equals_complete (c := KimchiConstraint F) hi (.const ((bound / 2 ^ 128 : ℕ) : F))
        (hiv : F) ((bound / 2 ^ 128 : ℕ) : F)))
    fun hiIsTop => ?_
  -- the difference that case selects
  refine Complete.seq (by complete_mono_tac)
    (Complete.imp (fun st h => ⟨h.2, hsubR (hconst _) h.1.1, hsubR (hconst _) h.1.2.1⟩)
      (fun _ _ h => h)
      (selectField_complete (c := KimchiConstraint F) hiIsTop _ _
        (decide ((hiv : F) = ((bound / 2 ^ 128 : ℕ) : F)))
        (((bound % 2 ^ 128 : ℕ) : F) - 1 - (lov : F))
        (((bound / 2 ^ 128 : ℕ) : F) - 1 - (hiv : F))))
    fun d => ?_
  refine Complete.bind
    (Complete.imp (fun st h => ⟨h.2, h.1.1.2.2⟩) (fun _ _ _ => trivial)
      (EndoScalar.toField_complete h2 h3 d endo
        (if decide ((hiv : F) = ((bound / 2 ^ 128 : ℕ) : F))
          then ((bound % 2 ^ 128 : ℕ) : F) - 1 - (lov : F)
          else ((bound / 2 ^ 128 : ℕ) : F) - 1 - (hiv : F)) ev ?hlt))
    fun _ => Complete.pure_of fun _ _ => trivial
  case hlt =>
    by_cases hc : (hiv : F) = ((bound / 2 ^ 128 : ℕ) : F)
    · -- equal high limbs: the low limb sits below the bound's
      have hn : hiv = bound / 2 ^ 128 := by
        have h := congrArg ToNat.toNat hc
        rwa [hcast _ (lt_of_le_of_lt hhile hbhb), hcast _ hbhb] at h
      simp only [hc, decide_true, if_true]
      have hlolt : lov < bound % 2 ^ 128 := by
        subst hn
        omega
      rw [← Nat.cast_one, ← Nat.cast_sub (by omega), ← Nat.cast_sub (by omega),
        hcast _ (by omega)]
      omega
    · -- a smaller high limb: it sits below the bound's
      have hn : hiv ≠ bound / 2 ^ 128 := fun h => hc (by rw [h])
      have hlt : hiv < bound / 2 ^ 128 := lt_of_le_of_ne hhile hn
      simp only [hc, decide_false, Bool.false_eq_true, if_false]
      rw [← Nat.cast_one, ← Nat.cast_sub (by omega), ← Nat.cast_sub (by omega),
        hcast _ (by omega)]
      omega

attribute [irreducible] assertSplitBelow

/-- **Soundness** (`split128Below`): the operand reads as `lo + 2^128·hi` for the returned low
half and some high half below `2^128`; under `constrainLowBits` the low half is below `2^128`
too. -/
theorem split128Below_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (constrainLowBits : Bool) (endo : FVar F)
    (bound : ℕ) (x : FVar F) :
    ⦃⌜True⌝⦄
    split128Below (c := Builder V (KimchiConstraint F)) constrainLowBits endo bound x
    ⦃⇓ r _ => ⌜∃ hiv : F,
      x.val V = r.val.val V + 2 ^ 128 * hiv ∧
      (∃ n : ℕ, n < 2 ^ 128 ∧ hiv = (n : F)) ∧
      (constrainLowBits = true →
        ∃ n : ℕ, n < 2 ^ 128 ∧ r.val.val V = (n : F))⌝⦄ := by
  have htf := fun (y : FVar F) => EndoScalar.toField_spec (V := V) h2 h3 y endo
  have hcmp := fun (lo hi : FVar F) => assertSplitBelow_spec (V := V) h2 h3 endo lo hi bound
  simp only [split128Below]
  mvcgen [htf, hcmp]
  · -- the low half is checked too
    rename_i lohi _ _ _ _ _ hhi _ _ hlo _ _ heq _ _
    obtain ⟨nh, hnhlt, hnh, -⟩ := hhi
    obtain ⟨nl, hnllt, hnl, -⟩ := hlo
    exact ⟨lohi.val.2.val V, by rw [heq, CVar.val_add_, CVar.val_scale_],
      ⟨nh, hnhlt, hnh⟩, fun _ => ⟨nl, hnllt, hnl⟩⟩
  · -- only the high half is checked
    rename_i lohi _ _ _ hfalse _ hhi _ _ heq _ _
    obtain ⟨nh, hnhlt, hnh, -⟩ := hhi
    exact ⟨lohi.val.2.val V, by rw [heq, CVar.val_add_, CVar.val_scale_],
      ⟨nh, hnhlt, hnh⟩, fun hc => absurd hc hfalse⟩

/-- **Soundness, below the bound** (`split128Below`): where naturals below `2^130` cast
injectively and the bound is below `2^256`, a low half reading as a 128-bit natural `l` gives
`x = l + 2^128·h` with `h < 2^128` and `l + 2^128·h < bound`. -/
theorem split128Below_below {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hinj : ∀ a b : ℕ, a < 2 ^ 130 → b < 2 ^ 130 → (a : F) = b → a = b)
    (constrainLowBits : Bool) (endo : FVar F) (bound : ℕ) (hbound : bound < 2 ^ 256)
    (x : FVar F) :
    ⦃⌜True⌝⦄
    split128Below (c := Builder V (KimchiConstraint F)) constrainLowBits endo bound x
    ⦃⇓ r _ => ⌜∀ l : ℕ, l < 2 ^ 128 → r.val.val V = l →
      ∃ h : ℕ, h < 2 ^ 128 ∧ x.val V = (l : F) + 2 ^ 128 * (h : F) ∧
        l + 2 ^ 128 * h < bound⌝⦄ := by
  have htf := fun (y : FVar F) => EndoScalar.toField_spec (V := V) h2 h3 y endo
  have hcmp := fun (lo hi : FVar F) =>
    assertSplitBelow_below (V := V) h2 h3 hinj endo lo hi bound hbound
  simp only [split128Below]
  mvcgen [htf, hcmp]
  · rename_i lohi _ _ _ _ _ hhi _ _ _ _ _ heq _ _ hb
    intro l hl hr
    obtain ⟨nh, hnhlt, hnh, -⟩ := hhi
    exact ⟨nh, hnhlt, by rw [heq, CVar.val_add_, CVar.val_scale_, ← hnh]; exact congrArg (· + _) hr,
      hb l nh hl hnhlt hr hnh⟩
  · rename_i lohi _ _ _ _ _ hhi _ _ heq _ _ hb
    intro l hl hr
    obtain ⟨nh, hnhlt, hnh, -⟩ := hhi
    exact ⟨nh, hnhlt, by rw [heq, CVar.val_add_, CVar.val_scale_, ← hnh]; exact congrArg (· + _) hr,
      hb l nh hl hnhlt hr hnh⟩

/-- **Soundness** (`lowest128Bits'`): `split128Below_spec` at the field's modulus. -/
theorem lowest128Bits'_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (constrainLowBits : Bool) (endo x : FVar F) :
    ⦃⌜True⌝⦄
    lowest128Bits' (c := Builder V (KimchiConstraint F)) constrainLowBits endo x
    ⦃⇓ r _ => ⌜∃ hiv : F,
      x.val V = r.val.val V + 2 ^ 128 * hiv ∧
      (∃ n : ℕ, n < 2 ^ 128 ∧ hiv = (n : F)) ∧
      (constrainLowBits = true →
        ∃ n : ℕ, n < 2 ^ 128 ∧ r.val.val V = (n : F))⌝⦄ :=
  split128Below_spec h2 h3 constrainLowBits endo (fieldModulus F) x

/-- **Soundness, canonical** (`lowest128Bits'`): `split128Below_below` at the field's
modulus, so a low half reading as a 128-bit natural is the canonical representative's. -/
theorem lowest128Bits'_below {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hinj : ∀ a b : ℕ, a < 2 ^ 130 → b < 2 ^ 130 → (a : F) = b → a = b)
    (hmod : fieldModulus F < 2 ^ 256) (constrainLowBits : Bool) (endo x : FVar F) :
    ⦃⌜True⌝⦄
    lowest128Bits' (c := Builder V (KimchiConstraint F)) constrainLowBits endo x
    ⦃⇓ r _ => ⌜∀ l : ℕ, l < 2 ^ 128 → r.val.val V = l →
      ∃ h : ℕ, h < 2 ^ 128 ∧ x.val V = (l : F) + 2 ^ 128 * (h : F) ∧
        l + 2 ^ 128 * h < fieldModulus F⌝⦄ :=
  split128Below_below h2 h3 hinj constrainLowBits endo (fieldModulus F) hmod x

/-- **Completeness** (`lowest128Bits'`): the honest run accepts and the result reads the
pure split's low half. The field is below `2^256`, and both halves' representatives survive
the cast. -/
theorem lowest128Bits'_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (constrainLowBits : Bool) (endo x : FVar F)
    (xv ev : F) (hcard : LawfulToNat.card (F := F) < 2 ^ 256)
    (hlo' : ToNat.toNat ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) = ToNat.toNat xv % 2 ^ 128)
    (hhi' : ToNat.toNat ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) = ToNat.toNat xv / 2 ^ 128) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => CircuitType.ReadsAs (val := F) st x xv ∧ CircuitType.ReadsAs (val := F) st endo ev)
      (lowest128Bits' (c := KimchiConstraint F) constrainLowBits endo x)
      (fun r st' => CircuitType.ReadsAs (val := F) st' r.val (lowest128BitsPure xv).val) := by
  have hxlt := LawfulToNat.toNat_lt xv
  have hhi : ToNat.toNat xv / 2 ^ 128 < 2 ^ 128 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc ToNat.toNat xv < 2 ^ 256 := hxlt.trans hcard
      _ = 2 ^ 128 * 2 ^ 128 := by norm_num
  -- the limb comparison's side conditions at the field's modulus, which the walk absorbs
  have hmodle : fieldModulus F ≤ LawfulToNat.card (F := F) :=
    (fieldModulus_eq_card (F := F)).le
  have hmodnarrow : fieldModulus F < 2 ^ 256 := (fieldModulus_eq_card (F := F)) ▸ hcard
  have hmodbelow :
      ToNat.toNat xv % 2 ^ 128 + 2 ^ 128 * (ToNat.toNat xv / 2 ^ 128) < fieldModulus F := by
    rw [Nat.mod_add_div, fieldModulus_eq_card]
    exact hxlt
  have hsplit : xv =
      ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) + 2 ^ 128 * ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) := by
    have hmd := Nat.mod_add_div (ToNat.toNat xv) (2 ^ 128)
    calc xv = ((ToNat.toNat xv : ℕ) : F) := (LawfulToNat.cast_toNat xv).symm
      _ = ((ToNat.toNat xv % 2 ^ 128 + 2 ^ 128 * (ToNat.toNat xv / 2 ^ 128) : ℕ) : F) := by
            rw [hmd]
      _ = _ := by push_cast; ring
  have hlolt : ToNat.toNat ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) < 2 ^ 128 := by
    rw [hlo']
    exact Nat.mod_lt _ (by positivity)
  have hhilt : ToNat.toNat ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) < 2 ^ 128 := by
    rw [hhi']
    exact hhi
  simp only [lowest128Bits']
  -- the split, in one witness
  refine Complete.seq (by complete_mono_tac)
    (Complete.imp
      (fun st h => by
        simp only [lowestWit, AsProver.map_eq, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.1.1),
          CircuitType.reads_fvar.mp h.1.2, Except.bind]
        rfl)
      (fun _ _ h => h)
      (Complete.witness (UnChecked.mk <$> lowestWit x)
        (⟨(((ToNat.toNat xv % 2 ^ 128 : ℕ) : F),
          ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F))⟩ : UnChecked (F × F))
        (by simp)))
    fun lohi => ?_
  obtain ⟨⟨lo, hi⟩⟩ := lohi
  -- the split's halves, componentwise
  have hw : ∀ {st : ProverState F},
      CircuitType.ReadsAs (val := UnChecked (F × F)) st ⟨(lo, hi)⟩
          ⟨(((ToNat.toNat xv % 2 ^ 128 : ℕ) : F),
            ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F))⟩ →
        CircuitType.ReadsAs (val := F) st lo ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) ∧
        CircuitType.ReadsAs (val := F) st hi ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) := by
    intro st h
    have hsc := h.1
    have hrd := h.2
    simp only [CircuitType.scoped_unchecked, CircuitType.scoped_prod,
      CircuitType.scoped_fvar] at hsc
    simp only [CircuitType.reads_unchecked, CircuitType.reads_prod,
      CircuitType.reads_fvar] at hrd
    exact ⟨⟨CircuitType.scoped_fvar.mpr hsc.1, CircuitType.reads_fvar.mpr hrd.1⟩,
      ⟨CircuitType.scoped_fvar.mpr hsc.2, CircuitType.reads_fvar.mpr hrd.2⟩⟩
  -- the halves and the recombination, as search rules for the walk
  have hloR := fun {st : ProverState F} h => (hw (st := st) h).1
  have hhiR := fun {st : ProverState F} h => (hw (st := st) h).2
  have hxread : ∀ {st : ProverState F},
      CircuitType.ReadsAs (val := F) st lo ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) →
      CircuitType.ReadsAs (val := F) st hi ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) →
      CircuitType.ReadsAs (val := F) st
        (CVar.add_ lo (CVar.scale_ ((2 : F) ^ 128) hi)) xv :=
    fun hl hh => ⟨CircuitType.scoped_fvar.mpr
        (CVar.Scoped.add_ (CircuitType.scoped_fvar.mp hl.1)
          (CVar.Scoped.scale_ (CircuitType.scoped_fvar.mp hh.1))),
      CircuitType.reads_fvar.mpr (by
        rw [CVar.val_add_, CVar.val_scale_, CircuitType.reads_fvar.mp hl.2,
          CircuitType.reads_fvar.mp hh.2]
        exact hsplit.symm)⟩
  -- range-check the high half; the walk then stops at the statement-position `if`
  complete_walk
  by_cases hc : constrainLowBits = true
  · simp only [hc, if_true]
    complete_walk
    exact Complete.pure_of fun _ h => hloR h.1.1.1.1.1.2
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, if_false]
    complete_walk
    exact Complete.pure_of fun _ h => hloR h.1.1.1.1.2

attribute [irreducible] lowestWit split128Below lowest128Bits'

end Snarky.Kimchi
