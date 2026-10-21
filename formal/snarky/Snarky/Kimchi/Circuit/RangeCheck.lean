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

Each gadget is followed by its soundness spec and its completeness law at the prover's reading,
then sealed `irreducible`; the pure split `lowest128BitsPure` stays transparent, since the
statements speak about it. No law assumes a field width up front: each carries the width facts
it needs.
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-! ## The 128-bit range check -/

/-- 128-bit range assert: the `EndoScalar.toField` decomposition is the check; its result is
discarded. -/
def rangeCheck128 [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c] (endo : FVar F) (v : SizedF 128 (FVar F)) :
    CircuitM F c PUnit := do
  let _ ← EndoScalar.toField (c := c) 8 v.val endo
  pure ⟨⟩

open Std.WP in
/-- **Soundness** (`rangeCheck128`): any satisfying valuation reads the operand as a
natural below `2^128` — the value-level `SizedF` contract. -/
theorem rangeCheck128_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo : FVar F) (v : SizedF 128 (FVar F)) :
    ⦃fun _ => True⦄
    rangeCheck128 (c := Builder V (KimchiConstraint F)) endo v
    ⦃fun _ _ => ∃ n : ℕ, n < 2 ^ 128 ∧ v.val.val V = (n : F)⦄ := by
  have htf := EndoScalar.toField_spec (V := V) h2 h3 v.val endo
  simp only [rangeCheck128]
  vcgen [htf]
  rename_i _ _ hr
  obtain ⟨n, hlt, hval, -⟩ := hr
  exact ⟨n, hlt, hval⟩

open Snarky.Prover Std.WP in
/-- `rangeCheck128`'s completeness: on an operand reading `a` below `2 ^ 128` and a coefficient
reading `e`, the honest run accepts. -/
theorem Prover.rangeCheck128_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (endo : FVar F) (v : SizedF 128 (FVar F)) (a e : F) (hlt : ToNat.toNat a < 2 ^ 128) :
    ⦃Reads v.val a ⊓ Reads endo e⦄ rangeCheck128 (c := Prover (KimchiConstraint F)) endo v
    ⦃fun _ ↦ ⊤⦄ := by
  have ht := EndoScalar.Prover.toField_spec_rows 8 v.val endo a e hlt
  unfold rangeCheck128
  vcgen [ht]
  all_goals prover_assert

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
    [ConstraintHolds F c]
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
def split128Below [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [ConstraintHolds F c]
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
def lowest128Bits' [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c] (constrainLowBits : Bool) (endo x : FVar F) :
    CircuitM F c (SizedF 128 (FVar F)) :=
  split128Below constrainLowBits endo (fieldModulus F) x

open Std.WP in
/-- The limb comparison with a trivial postcondition, for callers' `vcgen` to step over. -/
private theorem assertSplitBelow_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo lo hi : FVar F) (bound : ℕ) :
    ⦃fun _ => True⦄
    assertSplitBelow (c := Builder V (KimchiConstraint F)) endo lo hi bound
    ⦃fun _ _ => True⦄ := by
  have htf := fun (y : FVar F) => EndoScalar.toField_spec (V := V) h2 h3 y endo
  simp only [assertSplitBelow]
  vcgen [htf]

open Std.WP in
/-- **Soundness** (`assertSplitBelow`, the comparison): where naturals below `2^130` cast
injectively and the bound fits in 256 bits, any satisfying valuation reading the limbs as
128-bit naturals reads them below the bound. -/
private theorem assertSplitBelow_below {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hinj : ∀ a b : ℕ, a < 2 ^ 130 → b < 2 ^ 130 → (a : F) = b → a = b)
    (endo lo hi : FVar F) (bound : ℕ) (hbound : bound < 2 ^ 256) :
    ⦃fun _ => True⦄
    assertSplitBelow (c := Builder V (KimchiConstraint F)) endo lo hi bound
    ⦃fun _ _ => ∀ l h : ℕ, l < 2 ^ 128 → h < 2 ^ 128 → lo.val V = l → hi.val V = h →
      l + 2 ^ 128 * h < bound⦄ := by
  have htf := fun (y : FVar F) => EndoScalar.toField_spec (V := V) h2 h3 y endo
  simp only [assertSplitBelow]
  vcgen [htf]
  rename_i htop _ hsel _ _ hd l h hl hh hlo hhi
  have hdm := Nat.mod_add_div bound (2 ^ 128)
  have hbh : bound / 2 ^ 128 < 2 ^ 128 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc bound < 2 ^ 256 := hbound
      _ = 2 ^ 128 * 2 ^ 128 := by norm_num
  have hbl : bound % 2 ^ 128 < 2 ^ 128 := Nat.mod_lt _ (by positivity)
  obtain ⟨n, hn, hv, -⟩ := hd
  by_cases hheq : h = bound / 2 ^ 128
  · -- equal high limbs: the selected difference pins the low limb below the bound's
    have htop1 : (↑hiIsTop : CVar F).val V = bit true := by
      rw [htop]
      simp [CVar.val, hhi, hheq, bit]
    have hd := hsel true htop1
    simp only [ite_true, CVar.val_sub_, CVar.val, hlo] at hd
    rw [hd] at hv
    have he : bound % 2 ^ 128 = l + n + 1 :=
      hinj _ _ (by omega) (by omega) (by push_cast; linear_combination hv)
    rw [← hheq] at hdm
    nlinarith
  · -- a smaller high limb leaves room for any low limb
    have hne : (h : F) ≠ ((bound / 2 ^ 128 : ℕ) : F) :=
      fun hc => hheq (hinj _ _ (by omega) (by omega) hc)
    have htop0 : (↑hiIsTop : CVar F).val V = bit false := by
      rw [htop]
      simpa [CVar.val, hhi, bit] using hne
    have hd := hsel false htop0
    simp only [Bool.false_eq_true, ite_false, CVar.val_sub_, CVar.val, hhi] at hd
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

open Snarky.Prover Std.WP in
/-- `assertSplitBelow`'s completeness: on limbs reading `l` and `h` whose canonical recombination
lies below the bound, where the bound is below `2 ^ 256` and at most the field's cardinality,
and a coefficient reading `e`, the honest run accepts. -/
private theorem Prover.assertSplitBelow_spec [Field F] [DecidableEq F] [ToNat F]
    [LawfulToNat F] (endo lo hi : FVar F) (bound : ℕ) (l h e : F)
    (hcard : bound ≤ LawfulToNat.card (F := F)) (hnarrow : bound < 2 ^ 256)
    (hbelow : ToNat.toNat l + 2 ^ 128 * ToNat.toNat h < bound) :
    ⦃Reads lo l ⊓ Reads hi h ⊓ Reads endo e⦄
    assertSplitBelow (c := Prover (KimchiConstraint F)) endo lo hi bound
    ⦃fun _ ↦ ⊤⦄ := by
  -- the selected difference fits 128 bits: the limb comparison's arithmetic
  have hdlt : ToNat.toNat (if decide (h = ((bound / 2 ^ 128 : ℕ) : F)) then
      ((bound % 2 ^ 128 : ℕ) : F) - 1 - l else ((bound / 2 ^ 128 : ℕ) : F) - 1 - h) <
      2 ^ (16 * 8) := by
    generalize hL : ToNat.toNat l = L at hbelow
    generalize hH : ToNat.toNat h = H at hbelow
    have hl : l = (L : F) := by rw [← hL, LawfulToNat.cast_toNat]
    have hh : h = (H : F) := by rw [← hH, LawfulToNat.cast_toNat]
    subst hl hh
    have hK : (0 : ℕ) < 2 ^ 128 := by positivity
    have hcast : ∀ n : ℕ, n < bound → ToNat.toNat ((n : ℕ) : F) = n :=
      fun n hn => LawfulToNat.toNat_natCast n (lt_of_lt_of_le hn hcard)
    have hdm := Nat.mod_add_div bound (2 ^ 128)
    have hhile : H ≤ bound / 2 ^ 128 := by
      rw [Nat.le_div_iff_mul_le hK]
      nlinarith
    have hbhlt : bound / 2 ^ 128 < 2 ^ 128 := by
      rw [Nat.div_lt_iff_lt_mul hK]
      calc bound < 2 ^ 256 := hnarrow
        _ = 2 ^ 128 * 2 ^ 128 := by norm_num
    have hbhb : bound / 2 ^ 128 < bound := Nat.div_lt_self (by omega) (by norm_num)
    by_cases hc : (H : F) = ((bound / 2 ^ 128 : ℕ) : F)
    · -- equal high limbs: the low limb sits below the bound's
      have hn : H = bound / 2 ^ 128 := by
        have h := congrArg ToNat.toNat hc
        rwa [hcast _ (lt_of_le_of_lt hhile hbhb), hcast _ hbhb] at h
      simp only [hc, decide_true, ↓reduceIte]
      have hlolt : L < bound % 2 ^ 128 := by
        subst hn
        omega
      rw [← Nat.cast_one, ← Nat.cast_sub (by omega), ← Nat.cast_sub (by omega),
        hcast _ (by omega)]
      omega
    · -- a smaller high limb: it sits below the bound's
      have hn : H ≠ bound / 2 ^ 128 := fun h => hc (by rw [h])
      have hlt : H < bound / 2 ^ 128 := lt_of_le_of_ne hhile hn
      simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [← Nat.cast_one, ← Nat.cast_sub (by omega), ← Nat.cast_sub (by omega),
        hcast _ (by omega)]
      omega
  have he := Prover.equals_spec (c := KimchiConstraint F) hi
    (.const ((bound / 2 ^ 128 : ℕ) : F)) h ((bound / 2 ^ 128 : ℕ) : F)
  have hs := fun b : BoolVar F ↦ Prover.selectField_spec (c := KimchiConstraint F) b
    (CVar.sub_ (.const (((bound % 2 ^ 128 : ℕ) : F) - 1)) lo)
    (CVar.sub_ (.const (((bound / 2 ^ 128 : ℕ) : F) - 1)) hi)
    (decide (h = ((bound / 2 ^ 128 : ℕ) : F)))
    (((bound % 2 ^ 128 : ℕ) : F) - 1 - l) (((bound / 2 ^ 128 : ℕ) : F) - 1 - h)
  have ht := fun d : FVar F ↦ EndoScalar.Prover.toField_spec_rows 8 d endo _ e hdlt
  simp only [assertSplitBelow]
  vcgen [he, hs, ht]
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, CVar.val_sub_, CVar.Scoped.sub_, CVar.val])

attribute [irreducible] assertSplitBelow

open Std.WP in
/-- **Soundness** (`split128Below`): the operand reads as `lo + 2^128·hi` for the returned low
half and some high half below `2^128`; under `constrainLowBits` the low half is below `2^128`
too. -/
theorem split128Below_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (constrainLowBits : Bool) (endo : FVar F)
    (bound : ℕ) (x : FVar F) :
    ⦃fun _ => True⦄
    split128Below (c := Builder V (KimchiConstraint F)) constrainLowBits endo bound x
    ⦃fun r _ => ∃ hiv : F,
      x.val V = r.val.val V + 2 ^ 128 * hiv ∧
      (∃ n : ℕ, n < 2 ^ 128 ∧ hiv = (n : F)) ∧
      (constrainLowBits = true →
        ∃ n : ℕ, n < 2 ^ 128 ∧ r.val.val V = (n : F))⦄ := by
  have htf := fun (y : FVar F) => EndoScalar.toField_spec (V := V) h2 h3 y endo
  have hcmp := fun (lo hi : FVar F) => assertSplitBelow_spec (V := V) h2 h3 endo lo hi bound
  simp only [split128Below]
  vcgen [htf, hcmp]
  · -- the low half is checked too
    rename_i hhi _ _ _ hlo _ _ heq _ _
    obtain ⟨nh, hnhlt, hnh, -⟩ := hhi
    obtain ⟨nl, hnllt, hnl, -⟩ := hlo
    exact ⟨lohi.val.2.val V, by rw [heq, CVar.val_add_, CVar.val_scale_],
      ⟨nh, hnhlt, hnh⟩, fun _ => ⟨nl, hnllt, hnl⟩⟩
  · -- only the high half is checked
    rename_i hhi hfalse _ _ heq _ _
    obtain ⟨nh, hnhlt, hnh, -⟩ := hhi
    exact ⟨lohi.val.2.val V, by rw [heq, CVar.val_add_, CVar.val_scale_],
      ⟨nh, hnhlt, hnh⟩, fun hc => absurd hc hfalse⟩

open Std.WP in
/-- **Soundness, below the bound** (`split128Below`): where naturals below `2^130` cast
injectively and the bound is below `2^256`, a low half reading as a 128-bit natural `l` gives
`x = l + 2^128·h` with `h < 2^128` and `l + 2^128·h < bound`. -/
theorem split128Below_below {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hinj : ∀ a b : ℕ, a < 2 ^ 130 → b < 2 ^ 130 → (a : F) = b → a = b)
    (constrainLowBits : Bool) (endo : FVar F) (bound : ℕ) (hbound : bound < 2 ^ 256)
    (x : FVar F) :
    ⦃fun _ => True⦄
    split128Below (c := Builder V (KimchiConstraint F)) constrainLowBits endo bound x
    ⦃fun (r : SizedF 128 (FVar F)) _ => ∀ l : ℕ, l < 2 ^ 128 → r.val.val V = l →
      ∃ h : ℕ, h < 2 ^ 128 ∧ x.val V = (l : F) + 2 ^ 128 * (h : F) ∧
        l + 2 ^ 128 * h < bound⦄ := by
  have htf := fun (y : FVar F) => EndoScalar.toField_spec (V := V) h2 h3 y endo
  have hcmp := fun (lo hi : FVar F) =>
    assertSplitBelow_below (V := V) h2 h3 hinj endo lo hi bound hbound
  simp only [split128Below]
  vcgen [htf, hcmp]
  · rename_i hhi _ _ _ _ _ _ heq _ _ hb l hl hr
    obtain ⟨nh, hnhlt, hnh, -⟩ := hhi
    exact ⟨nh, hnhlt, by rw [heq, CVar.val_add_, CVar.val_scale_, ← hnh]; exact congrArg (· + _) hr,
      hb l nh hl hnhlt hr hnh⟩
  · rename_i hhi _ _ _ heq _ _ hb l hl hr
    obtain ⟨nh, hnhlt, hnh, -⟩ := hhi
    exact ⟨nh, hnhlt, by rw [heq, CVar.val_add_, CVar.val_scale_, ← hnh]; exact congrArg (· + _) hr,
      hb l nh hl hnhlt hr hnh⟩

open Std.WP in
/-- **Soundness** (`lowest128Bits'`): `split128Below_spec` at the field's modulus. -/
theorem lowest128Bits'_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (constrainLowBits : Bool) (endo x : FVar F) :
    ⦃fun _ => True⦄
    lowest128Bits' (c := Builder V (KimchiConstraint F)) constrainLowBits endo x
    ⦃fun r _ => ∃ hiv : F,
      x.val V = r.val.val V + 2 ^ 128 * hiv ∧
      (∃ n : ℕ, n < 2 ^ 128 ∧ hiv = (n : F)) ∧
      (constrainLowBits = true →
        ∃ n : ℕ, n < 2 ^ 128 ∧ r.val.val V = (n : F))⦄ :=
  split128Below_spec h2 h3 constrainLowBits endo (fieldModulus F) x

open Std.WP in
/-- **Soundness, canonical** (`lowest128Bits'`): `split128Below_below` at the field's
modulus, so a low half reading as a 128-bit natural is the canonical representative's. -/
theorem lowest128Bits'_below {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hinj : ∀ a b : ℕ, a < 2 ^ 130 → b < 2 ^ 130 → (a : F) = b → a = b)
    (hmod : fieldModulus F < 2 ^ 256) (constrainLowBits : Bool) (endo x : FVar F) :
    ⦃fun _ => True⦄
    lowest128Bits' (c := Builder V (KimchiConstraint F)) constrainLowBits endo x
    ⦃fun (r : SizedF 128 (FVar F)) _ => ∀ l : ℕ, l < 2 ^ 128 → r.val.val V = l →
      ∃ h : ℕ, h < 2 ^ 128 ∧ x.val V = (l : F) + 2 ^ 128 * (h : F) ∧
        l + 2 ^ 128 * h < fieldModulus F⦄ :=
  split128Below_below h2 h3 hinj constrainLowBits endo (fieldModulus F) hmod x

section ProverReading

open Snarky.Prover Std.WP

/-- An unchecked pair of limbs reads an unchecked pair of values exactly when its payload does. -/
private theorem Prover.reads_unchecked_apply [Field F] (u : UnChecked (FVar F × FVar F))
    (v : UnChecked (F × F)) (s : ProverState F) : Reads u v s ↔ Reads u.val v.val s := Iff.rfl

/-- The split advice returns the halves of the canonical representative of the operand's
reading, low half first. -/
private theorem Prover.lowestWit_advice_run [Field F] [ToNat F] {x : FVar F}
    {s : ProverState F} (hx : x.Scoped s) :
    (lowestWit x).run s.env =
      .ok (((ToNat.toNat (x.val s.env.get) % 2 ^ 128 : ℕ) : F),
        ((ToNat.toNat (x.val s.env.get) / 2 ^ 128 : ℕ) : F)) := by
  simp [lowestWit, AsProver.readCVar_run hx]

/-- `lowest128Bits'`'s completeness: on an operand reading `a` and a coefficient reading `e`,
the result reads the pure split's low half. The field is below `2 ^ 256`, and both halves of
`a`'s canonical representative survive the cast. -/
theorem Prover.lowest128Bits'_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (hcard : LawfulToNat.card (F := F) < 2 ^ 256) (constrainLowBits : Bool) (endo x : FVar F)
    (a e : F)
    (hlo : ToNat.toNat (((ToNat.toNat a % 2 ^ 128 : ℕ) : F)) = ToNat.toNat a % 2 ^ 128)
    (hhi : ToNat.toNat (((ToNat.toNat a / 2 ^ 128 : ℕ) : F)) = ToNat.toNat a / 2 ^ 128) :
    ⦃Reads x a ⊓ Reads endo e⦄
    lowest128Bits' (c := Prover (KimchiConstraint F)) constrainLowBits endo x
    ⦃fun r ↦ Reads r.val (lowest128BitsPure a).val⦄ := by
  have hmodle : fieldModulus F ≤ LawfulToNat.card (F := F) :=
    (fieldModulus_eq_card (F := F)).le
  have hmodnarrow : fieldModulus F < 2 ^ 256 := (fieldModulus_eq_card (F := F)) ▸ hcard
  have hxlt := LawfulToNat.toNat_lt a
  have hlolt : ToNat.toNat (((ToNat.toNat a % 2 ^ 128 : ℕ) : F)) < 2 ^ (16 * 8) := by
    rw [hlo]
    exact Nat.mod_lt _ (by positivity)
  have hhilt : ToNat.toNat (((ToNat.toNat a / 2 ^ 128 : ℕ) : F)) < 2 ^ (16 * 8) := by
    rw [hhi, Nat.div_lt_iff_lt_mul (by positivity)]
    calc ToNat.toNat a < 2 ^ 256 := hxlt.trans hcard
      _ = 2 ^ 128 * 2 ^ 128 := by norm_num
  have hbelow : ToNat.toNat (((ToNat.toNat a % 2 ^ 128 : ℕ) : F)) +
      2 ^ 128 * ToNat.toNat (((ToNat.toNat a / 2 ^ 128 : ℕ) : F)) < fieldModulus F := by
    rw [hlo, hhi, Nat.mod_add_div, fieldModulus_eq_card]
    exact hxlt
  -- the recombination of the halves is the operand's reading
  have hsplit : ((ToNat.toNat a % 2 ^ 128 : ℕ) : F) +
      2 ^ 128 * ((ToNat.toNat a / 2 ^ 128 : ℕ) : F) = a := by
    have hmd := Nat.mod_add_div (ToNat.toNat a) (2 ^ 128)
    calc _ = ((ToNat.toNat a % 2 ^ 128 + 2 ^ 128 * (ToNat.toNat a / 2 ^ 128) : ℕ) : F) := by
          push_cast; ring
      _ = ((ToNat.toNat a : ℕ) : F) := by rw [hmd]
      _ = a := LawfulToNat.cast_toNat _
  have hw := Spec.witness (c := KimchiConstraint F) (UnChecked.mk <$> lowestWit x)
    (⟨(((ToNat.toNat a % 2 ^ 128 : ℕ) : F), ((ToNat.toNat a / 2 ^ 128 : ℕ) : F))⟩ :
      UnChecked (F × F)) valid_unchecked
  have hth := fun u : UnChecked (FVar F × FVar F) ↦ EndoScalar.Prover.toField_spec_rows 8
    u.val.2 endo _ e hhilt
  have htl := fun u : UnChecked (FVar F × FVar F) ↦ EndoScalar.Prover.toField_spec_rows 8
    u.val.1 endo _ e hlolt
  have ha := fun u : UnChecked (FVar F × FVar F) ↦ Prover.assertEqual_spec
    (c := KimchiConstraint F) x (CVar.add_ u.val.1 (CVar.scale_ ((2 : F) ^ 128) u.val.2)) a
  have hs := fun u : UnChecked (FVar F × FVar F) ↦ Prover.assertSplitBelow_spec endo u.val.1
    u.val.2 (fieldModulus F) _ _ e hmodle hmodnarrow hbelow
  unfold lowest128Bits' split128Below
  vcgen [hw, hth, htl, ha, hs]
  -- the calls' laws are spent; left in the context, they time `simp_all` out
  all_goals prover_assert with
    (intros; simp_all [Prover.reads_unchecked_apply, Reads.prod_apply, Reads.fvar_apply,
      Prover.lowestWit_advice_run, lowest128BitsPure, CVar.val_add_, CVar.val_scale_,
      CVar.Scoped.add_, CVar.Scoped.scale_])

end ProverReading

attribute [irreducible] lowestWit split128Below lowest128Bits'

end Snarky.Kimchi
