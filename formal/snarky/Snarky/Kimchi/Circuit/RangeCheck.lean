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

open Snarky Std.Do

variable {F c : Type}

/-! ## The 128-bit range check -/

/-- 128-bit range assert: the `EndoScalar.toField` decomposition is the check; its result is
discarded. -/
def rangeCheck128 [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [ConstraintHolds F c]
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

/-- `rangeCheck128`'s state-relative completeness: on an operand whose reading fits the tagged
width, the honest run accepts. -/
theorem Prover.rangeCheck128_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (endo : FVar F) (v : SizedF 128 (FVar F)) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ v.val.Scoped st₀ ∧ endo.Scoped st₀ ∧
      ToNat.toNat (st₀.read v.val) < 2 ^ 128⌝⦄
    rangeCheck128 (c := Prover (KimchiConstraint F)) endo v
    ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄ := by
  unfold rangeCheck128
  mvcgen
  case vc1 =>
    rename_i _ h
    obtain ⟨rfl, hv, he, hlt⟩ := h
    exact ⟨trivial, hv, he, by simpa using hlt⟩
  case vc2 =>
    rename_i _ h₀ _ _ h₁
    obtain ⟨rfl, -⟩ := h₀
    exact (Prover.Reg.iff.mp h₁).2.2

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
    simp only [ite_true, CVar.val_sub_, CVar.val, hlo] at hd
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

/-- `assertSplitBelow`'s state-relative completeness: on limbs whose canonical recombination
lies below the bound, where the bound is below `2^256` and at most the field's cardinality, the
honest run accepts. -/
private theorem Prover.assertSplitBelow_spec [Field F] [DecidableEq F] [ToNat F]
    [LawfulToNat F] (endo lo hi : FVar F) (bound : ℕ)
    (hcard : bound ≤ LawfulToNat.card (F := F)) (hnarrow : bound < 2 ^ 256)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ lo.Scoped st₀ ∧ hi.Scoped st₀ ∧ endo.Scoped st₀ ∧
      ToNat.toNat (st₀.read lo) + 2 ^ 128 * ToNat.toNat (st₀.read hi) < bound⌝⦄
    assertSplitBelow (c := Prover (KimchiConstraint F)) endo lo hi bound
    ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄ := by
  unfold assertSplitBelow
  mvcgen
  case vc1 =>
    rename_i _ _ _ h
    obtain ⟨rfl, -, hhi, -, -⟩ := h
    exact ⟨trivial, hhi, trivial⟩
  case vc2 =>
    rename_i _ _ _ h b s₁ h₁
    obtain ⟨rfl, hlo, hhi, -, -⟩ := h
    obtain ⟨hb, hbv, hle⟩ := Prover.Reg.iff.mp h₁
    refine ⟨trivial, hb, CVar.Scoped.sub_ trivial (hlo.of_le hle),
      CVar.Scoped.sub_ trivial (hhi.of_le hle), ?_⟩
    rw [hbv]
    split <;> simp
  -- the selected difference fits 128 bits: the limb comparison's arithmetic
  case vc3 =>
    rename_i bH bL s₀ h₀ b s₁ h₁ d s₂ h₂
    obtain ⟨rfl, hlo, hhi, he, hbelow⟩ := h₀
    obtain ⟨-, hbv, hle₁⟩ := Prover.Reg.iff.mp h₁
    obtain ⟨hd, hdv, hle₂⟩ := Prover.Reg.iff.mp h₂
    refine ⟨trivial, hd, he.of_le (hle₁.trans hle₂), ?_⟩
    rw [hdv, hbv]
    simp only [ProverState.read, CVar.val_sub_, CVar.val, CVar.val_of_le hle₁ hlo,
      CVar.val_of_le hle₁ hhi, bH, bL]
    simp only [ProverState.read] at hbelow
    generalize hL : ToNat.toNat (CVar.val lo s₀.env.get) = L at hbelow
    generalize hH : ToNat.toNat (CVar.val hi s₀.env.get) = H at hbelow
    have hlo' : CVar.val lo s₀.env.get = (L : F) := by rw [← hL, LawfulToNat.cast_toNat]
    have hhi' : CVar.val hi s₀.env.get = (H : F) := by rw [← hH, LawfulToNat.cast_toNat]
    simp only [hlo', hhi']
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
      simp only [hc, ↓reduceIte]
      have hlolt : L < bound % 2 ^ 128 := by
        subst hn
        omega
      rw [← Nat.cast_one, ← Nat.cast_sub (by omega), ← Nat.cast_sub (by omega),
        hcast _ (by omega)]
      omega
    · -- a smaller high limb: it sits below the bound's
      have hn : H ≠ bound / 2 ^ 128 := fun h => hc (by rw [h])
      have hlt : H < bound / 2 ^ 128 := lt_of_le_of_ne hhile hn
      simp only [hc, ↓reduceIte, zero_ne_one]
      rw [← Nat.cast_one, ← Nat.cast_sub (by omega), ← Nat.cast_sub (by omega),
        hcast _ (by omega)]
      omega
  case vc4 =>
    rename_i _ _ _ h₀ _ _ h₁ _ _ h₂ _ _ h₃
    obtain ⟨rfl, -⟩ := h₀
    exact (Prover.Reg.iff.mp h₁).2.2.trans
      ((Prover.Reg.iff.mp h₂).2.2.trans (Prover.Reg.iff.mp h₃).2.2)

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

/-- `lowest128Bits'`'s state-relative completeness: the result reads the pure split's low half.
The field is below `2^256`, and both halves of the operand's canonical representative survive
the cast. -/
theorem Prover.lowest128Bits'_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (hcard : LawfulToNat.card (F := F) < 2 ^ 256) (constrainLowBits : Bool) (endo x : FVar F)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ x.Scoped st₀ ∧ endo.Scoped st₀ ∧
      ToNat.toNat (((ToNat.toNat (st₀.read x) % 2 ^ 128 : ℕ) : F)) =
        ToNat.toNat (st₀.read x) % 2 ^ 128 ∧
      ToNat.toNat (((ToNat.toNat (st₀.read x) / 2 ^ 128 : ℕ) : F)) =
        ToNat.toNat (st₀.read x) / 2 ^ 128⌝⦄
    lowest128Bits' (c := Prover (KimchiConstraint F)) constrainLowBits endo x
    ⦃⇓ r s' => ⌜r.val.Scoped s' ∧ s'.read r.val = (lowest128BitsPure (st₀.read x)).val ∧
      st₀ ≤ s'⌝⦄ := by
  have hmodle : fieldModulus F ≤ LawfulToNat.card (F := F) :=
    (fieldModulus_eq_card (F := F)).le
  have hmodnarrow : fieldModulus F < 2 ^ 256 := (fieldModulus_eq_card (F := F)) ▸ hcard
  have hw := Prover.register (Prover.witness_of_run (c := KimchiConstraint F)
    (UnChecked.mk <$> lowestWit x) (fun st => x.Scoped st)
    (fun st => (⟨(((ToNat.toNat (st.read x) % 2 ^ 128 : ℕ) : F),
      ((ToNat.toNat (st.read x) / 2 ^ 128 : ℕ) : F))⟩ : UnChecked (F × F)))
    (fun st h => by
      simp only [lowestWit, AsProver.map_eq, AsProver.bind_eq, AsProver.run_bind,
        AsProver.readCVar_run h, Except.bind]
      rfl)
    (fun _ _ _ _ _ => trivial))
  have hs := fun lo hi => Prover.register
    (Prover.assertSplitBelow_spec (F := F) endo lo hi (fieldModulus F) hmodle hmodnarrow)
  unfold lowest128Bits' split128Below
  mvcgen [hw, hs]
  case vc1 =>
    rename_i _ h
    obtain ⟨rfl, hx, -⟩ := h
    exact ⟨trivial, hx⟩
  -- name each condition's trailing facts, then read the split off the witness once
  case' vc3 => rename_i t jp hc s₂ ht
  case' vc4 => rename_i t jp hc s₂ ht u s₃ hu
  case' vc5 => rename_i t jp hc s₂ ht u s₃ hu e s₄ he
  case' vc6 => rename_i t jp hc s₂ ht u s₃ hu e s₄ he b s₅ hb
  case' vc7 => rename_i t jp hc s₂ ht
  case' vc8 => rename_i t jp hc s₂ ht e s₃ he
  case' vc9 => rename_i t jp hc s₂ ht e s₃ he b s₄ hb
  case' vc2 | vc3 | vc4 | vc5 | vc6 | vc7 | vc8 | vc9 =>
    rename_i s₀ h₀ w s₁ hw
    obtain ⟨⟨lo, hi⟩⟩ := w
    obtain ⟨rfl, hx, hendo, hlo', hhi'⟩ := h₀
    obtain ⟨⟨hsc, hrd⟩, hle₁⟩ := Prover.Reg.iff.mp hw
    simp only [CircuitType.scoped_unchecked, CircuitType.scoped_prod,
      CircuitType.scoped_fvar] at hsc
    simp only [CircuitType.reads_unchecked, CircuitType.reads_prod,
      CircuitType.reads_fvar] at hrd
    obtain ⟨hlo, hhi⟩ := hsc
    obtain ⟨vlo, vhi⟩ := hrd
    have hxlt := LawfulToNat.toNat_lt (s₀.read x)
    have hlolt : ToNat.toNat (((ToNat.toNat (s₀.read x) % 2 ^ 128 : ℕ) : F)) < 2 ^ 128 := by
      rw [hlo']
      exact Nat.mod_lt _ (by positivity)
    have hhilt : ToNat.toNat (((ToNat.toNat (s₀.read x) / 2 ^ 128 : ℕ) : F)) < 2 ^ 128 := by
      rw [hhi', Nat.div_lt_iff_lt_mul (by positivity)]
      calc ToNat.toNat (s₀.read x) < 2 ^ 256 := hxlt.trans hcard
        _ = 2 ^ 128 * 2 ^ 128 := by norm_num
    have hsplit : s₀.read x = ((ToNat.toNat (s₀.read x) % 2 ^ 128 : ℕ) : F) +
        2 ^ 128 * ((ToNat.toNat (s₀.read x) / 2 ^ 128 : ℕ) : F) := by
      have hmd := Nat.mod_add_div (ToNat.toNat (s₀.read x)) (2 ^ 128)
      calc s₀.read x = ((ToNat.toNat (s₀.read x) : ℕ) : F) := (LawfulToNat.cast_toNat _).symm
        _ = ((ToNat.toNat (s₀.read x) % 2 ^ 128 + 2 ^ 128 * (ToNat.toNat (s₀.read x) / 2 ^ 128) :
              ℕ) : F) := by rw [hmd]
        _ = _ := by push_cast; ring
  -- the high half's range check
  case vc2 =>
    refine ⟨trivial, hhi, hendo.of_le hle₁, ?_⟩
    rw [ProverState.read, vhi]
    simpa using hhilt
  -- the low half's, under `constrainLowBits`
  case vc3 =>
    obtain ⟨-, -, hle₂⟩ := Prover.Reg.iff.mp ht
    refine ⟨trivial, hlo.of_le hle₂, hendo.of_le (by le_chain), ?_⟩
    rw [ProverState.read, CVar.val_of_le hle₂ hlo, vlo]
    simpa using hlolt
  -- the recombination
  case vc4 =>
    obtain ⟨-, -, hle₂⟩ := Prover.Reg.iff.mp ht
    obtain ⟨-, -, hle₃⟩ := Prover.Reg.iff.mp hu
    refine ⟨trivial, hx.of_le (by le_chain), CVar.Scoped.add_ (hlo.of_le (by le_chain))
      (CVar.Scoped.scale_ (hhi.of_le (by le_chain))), ?_⟩
    simp only [ProverState.read, CVar.val_add_, CVar.val_scale_,
      CVar.val_of_le (show s₁ ≤ s₃ by le_chain) hlo, CVar.val_of_le (show s₁ ≤ s₃ by le_chain) hhi,
      CVar.val_of_le (show s₀ ≤ s₃ by le_chain) hx, vlo, vhi]
    exact hsplit
  case vc7 =>
    obtain ⟨-, -, hle₂⟩ := Prover.Reg.iff.mp ht
    refine ⟨trivial, hx.of_le (by le_chain), CVar.Scoped.add_ (hlo.of_le (by le_chain))
      (CVar.Scoped.scale_ (hhi.of_le (by le_chain))), ?_⟩
    simp only [ProverState.read, CVar.val_add_, CVar.val_scale_,
      CVar.val_of_le (show s₁ ≤ s₂ by le_chain) hlo, CVar.val_of_le (show s₁ ≤ s₂ by le_chain) hhi,
      CVar.val_of_le (show s₀ ≤ s₂ by le_chain) hx, vlo, vhi]
    exact hsplit
  -- the limb comparison below the field's modulus
  case vc5 =>
    obtain ⟨-, -, hle₂⟩ := Prover.Reg.iff.mp ht
    obtain ⟨-, -, hle₃⟩ := Prover.Reg.iff.mp hu
    have hle₄ := Prover.Reg.iff.mp he
    refine ⟨trivial, hlo.of_le (by le_chain), hhi.of_le (by le_chain),
      hendo.of_le (by le_chain), ?_⟩
    simp only [ProverState.read, CVar.val_of_le (show s₁ ≤ s₄ by le_chain) hlo,
      CVar.val_of_le (show s₁ ≤ s₄ by le_chain) hhi, vlo, vhi, hlo', hhi', Nat.mod_add_div,
      fieldModulus_eq_card]
    exact hxlt
  case vc8 =>
    obtain ⟨-, -, hle₂⟩ := Prover.Reg.iff.mp ht
    have hle₃ := Prover.Reg.iff.mp he
    refine ⟨trivial, hlo.of_le (by le_chain), hhi.of_le (by le_chain),
      hendo.of_le (by le_chain), ?_⟩
    simp only [ProverState.read, CVar.val_of_le (show s₁ ≤ s₃ by le_chain) hlo,
      CVar.val_of_le (show s₁ ≤ s₃ by le_chain) hhi, vlo, vhi, hlo', hhi', Nat.mod_add_div,
      fieldModulus_eq_card]
    exact hxlt
  -- the result: the low half
  case vc6 =>
    obtain ⟨-, -, hle₂⟩ := Prover.Reg.iff.mp ht
    obtain ⟨-, -, hle₃⟩ := Prover.Reg.iff.mp hu
    have hle₄ := Prover.Reg.iff.mp he
    have hle₅ := Prover.Reg.iff.mp hb
    refine ⟨hlo.of_le (by le_chain), ?_, by le_chain⟩
    rw [ProverState.read, CVar.val_of_le (show s₁ ≤ s₅ by le_chain) hlo, vlo]
    rfl
  case vc9 =>
    obtain ⟨-, -, hle₂⟩ := Prover.Reg.iff.mp ht
    have hle₃ := Prover.Reg.iff.mp he
    have hle₄ := Prover.Reg.iff.mp hb
    refine ⟨hlo.of_le (by le_chain), ?_, by le_chain⟩
    rw [ProverState.read, CVar.val_of_le (show s₁ ≤ s₄ by le_chain) hlo, vlo]
    rfl

attribute [irreducible] lowestWit split128Below lowest128Bits'

end Snarky.Kimchi
