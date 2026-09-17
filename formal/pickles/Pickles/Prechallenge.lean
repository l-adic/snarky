import Snarky.DSL.SizedF
import Snarky.Kimchi.Circuit.RangeCheck
import Kimchi.Verifier.Kimchi

/-!
# Reading prechallenges at the circuit boundary

The only `SizedF 128` a verifier circuit ever reads is a prechallenge
(`Poseidon.FqSponge.Prechallenge`, the paper's Definition [Prechallenge]): the four plonk
prechallenges, `ξ`, the IPA round prechallenges and the Schnorr prechallenge. So the circuit
boundary has one reading relation for them, `Reads128`, and the wire verifier's
prechallenge is met through it:

* `Reads128 V u m` — the 128-bit circuit value `u` reads as the prechallenge `m`;
* `Low128 V x u` — the `lowest_128_bits` relation between a raw squeeze `x` and its low
  half `u`: a 128-bit reading `lo` of `u` splits `x = lo + 2¹²⁸·hi` below the modulus, so at
  a prime field it is the verifier's prechallenge (`Low128.exact`), at the widths
  `SplitWidth` names;
* `CastInj128 F` — naturals below `2¹²⁸` cast injectively into `F`, what pins a gadget's
  own reading of a prechallenge to the claimed one, and makes a cell's reading unique
  (`Reads128.unique`). A list of readings is one equation of lists (`forall₂_reads128_iff`).
-/

namespace Pickles

open Snarky Snarky.Kimchi Poseidon.FqSponge Kimchi.Verifier

-- The prechallenge type, in the pickles namespace: every `SizedF 128` here reads as one.
export Poseidon.FqSponge (Prechallenge)

variable {F : Type} [Field F] [DecidableEq F]

/-- A 128-bit circuit value reads as the prechallenge `m`. -/
def Reads128 (V : Valuation F) (u : SizedF 128 (FVar F)) (m : Prechallenge) : Prop :=
  u.val.val V = (m.val : F)

/-- The field widths the canonical 128-bit split reads at: naturals below `2¹³⁰` cast
injectively, and the modulus fits in 256 bits. -/
structure SplitWidth (F : Type) [Field F] [ToNat F] : Prop where
  /-- Naturals below `2¹³⁰` cast injectively. -/
  inj : ∀ a b : ℕ, a < 2 ^ 130 → b < 2 ^ 130 → (a : F) = b → a = b
  /-- The modulus fits in 256 bits. -/
  modulus_lt : fieldModulus F < 2 ^ 256

omit [DecidableEq F] in
/-- A field with the split's widths is not of characteristic 2. -/
theorem SplitWidth.two_ne [ToNat F] (hsw : SplitWidth F) : (2 : F) ≠ 0 := fun h =>
  absurd (hsw.inj 2 0 (by norm_num) (by norm_num) (by simpa using h)) (by norm_num)

omit [DecidableEq F] in
/-- A field with the split's widths is not of characteristic 3. -/
theorem SplitWidth.three_ne [ToNat F] (hsw : SplitWidth F) : (3 : F) ≠ 0 := fun h =>
  absurd (hsw.inj 3 0 (by norm_num) (by norm_num) (by simpa using h)) (by norm_num)

/-- A raw squeeze and a 128-bit circuit value in the `lowest_128_bits` relation: a reading
`lo < 2¹²⁸` of the value is the low half of a split `x = lo + 2¹²⁸·hi` below the field's
modulus, so of the canonical representative. -/
def Low128 [ToNat F] (V : Valuation F) (x : F) (u : SizedF 128 (FVar F)) : Prop :=
  ∀ lo : ℕ, lo < 2 ^ 128 → u.val.val V = lo →
    ∃ hi : ℕ, hi < 2 ^ 128 ∧ x = (lo : F) + 2 ^ 128 * (hi : F) ∧ lo + 2 ^ 128 * hi < fieldModulus F

/-- Naturals below `2¹²⁸` cast injectively into `F`. -/
def CastInj128 (F : Type) [NatCast F] : Prop :=
  ∀ a b : ℕ, a < 2 ^ 128 → b < 2 ^ 128 → (a : F) = b → a = b

omit [DecidableEq F] in
/-- The shape a gadget's range check leaves (`Snarky.Kimchi.lowest128Bits'_spec`,
`EndoScalar.toField_spec`): a reading as some prechallenge. -/
theorem reads128_of_nat {V : Valuation F} {u : SizedF 128 (FVar F)}
    (h : ∃ n : ℕ, n < 2 ^ 128 ∧ u.val.val V = (n : F)) : ∃ m : Prechallenge, Reads128 V u m :=
  let ⟨n, hn, e⟩ := h
  ⟨⟨n, hn⟩, e⟩

/-- A prime field above `2¹²⁸` casts the prechallenges injectively. -/
theorem castInj128_of_lt (p : ℕ) (hp : 2 ^ 128 < p) : CastInj128 (ZMod p) := by
  intro a b ha hb h
  have h' := (ZMod.natCast_eq_natCast_iff' a b p).mp h
  rwa [Nat.mod_eq_of_lt (lt_trans ha hp), Nat.mod_eq_of_lt (lt_trans hb hp)] at h'

omit [Field F] [DecidableEq F] in
/-- The prechallenge cast is injective where naturals below `2¹²⁸` cast injectively. -/
theorem CastInj128.prechallenge_injective [NatCast F] (hinj : CastInj128 F) :
    Function.Injective (fun m : Prechallenge => (m.val : F)) :=
  fun m m' h => Subtype.ext (hinj _ _ m.2 m'.2 h)

omit [DecidableEq F] in
/-- A cell reads as at most one prechallenge, the casts being injective below `2¹²⁸`. -/
theorem Reads128.unique (hinj : CastInj128 F) {V : Valuation F} {u : SizedF 128 (FVar F)}
    {m m' : Prechallenge} (h : Reads128 V u m) (h' : Reads128 V u m') : m = m' :=
  hinj.prechallenge_injective (h.symm.trans h')

omit [DecidableEq F] in
/-- A cell list reads as a prechallenge list: `Forall₂ (Reads128 V)` is one equation of
lists, the cells' values against the prechallenges' casts. -/
theorem forall₂_reads128_iff {V : Valuation F} {cs : List (SizedF 128 (FVar F))}
    {ms : List Prechallenge} :
    List.Forall₂ (Reads128 V) cs ms ↔ cs.map (·.val.val V) = ms.map (fun m => (m.val : F)) := by
  rw [← List.forall₂_eq_eq_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  rfl

/-- The modulus read off `ZMod p` is `p`. -/
theorem fieldModulus_zmod (p : ℕ) [Fact p.Prime] : fieldModulus (ZMod p) = p :=
  fieldModulus_eq_card (F := ZMod p)

/-- A prime field between `2¹³⁰` and `2²⁵⁶` has the split's widths. -/
theorem SplitWidth.zmod {p : ℕ} [Fact p.Prime] (hlo : 2 ^ 130 < p) (hhi : p < 2 ^ 256) :
    SplitWidth (ZMod p) where
  inj a b ha hb h := by
    have h' := (ZMod.natCast_eq_natCast_iff' a b p).mp h
    rwa [Nat.mod_eq_of_lt (lt_trans ha hlo), Nat.mod_eq_of_lt (lt_trans hb hlo)] at h'
  modulus_lt := by rw [fieldModulus_zmod]; exact hhi

/-- A split `x = lo + 2¹²⁸·hi` below the modulus is the canonical one: `lo` is the low
128 bits of `x`'s representative. -/
theorem low128_of_split {p : ℕ} [NeZero p] (x : ZMod p) {lo hi : ℕ} (hlo : lo < 2 ^ 128)
    (hx : x = (lo : ZMod p) + 2 ^ 128 * (hi : ZMod p)) (hlt : lo + 2 ^ 128 * hi < p) :
    x.val % 2 ^ 128 = lo := by
  have hcast : (lo : ZMod p) + 2 ^ 128 * (hi : ZMod p) = ((lo + 2 ^ 128 * hi : ℕ) : ZMod p) := by
    push_cast; ring
  rw [hx, hcast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hlo]

/-- A `Low128` split read through a prechallenge is the verifier's prechallenge: the low
128 bits of the squeeze's canonical representative. -/
theorem Low128.exact {p : ℕ} [Fact p.Prime] {V : Valuation (ZMod p)}
    {x : ZMod p} {u : SizedF 128 (FVar (ZMod p))} {m : Prechallenge}
    (hlow : Low128 V x u) (hm : Reads128 V u m) : x.val % 2 ^ 128 = m.val := by
  obtain ⟨hi, -, hx, hlt⟩ := hlow m.val m.2 hm
  exact low128_of_split x m.2 hx (fieldModulus_zmod p ▸ hlt)

end Pickles
