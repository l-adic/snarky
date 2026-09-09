import Snarky.DSL.SizedF
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
  half `u`: `x = u + 2¹²⁸·hi` for some `hi < 2¹²⁸`, the decomposition the gadget pins (not
  necessarily the canonical one, hence `PrechallengeAlias`);
* `CastInj128 F` — naturals below `2¹²⁸` cast injectively into `F`, what pins a gadget's
  own reading of a prechallenge to the claimed one.
-/

namespace Pickles

open Snarky Poseidon.FqSponge Kimchi.Verifier

-- The prechallenge type, in the pickles namespace: every `SizedF 128` here reads as one.
export Poseidon.FqSponge (Prechallenge)

variable {F : Type} [Field F] [DecidableEq F]

/-- A 128-bit circuit value reads as the prechallenge `m`. -/
def Reads128 (V : Valuation F) (u : SizedF 128 (FVar F)) (m : Prechallenge) : Prop :=
  u.val.val V = (m.val : F)

/-- A raw squeeze and a 128-bit circuit value in the `lowest_128_bits` relation:
`x = lo + 2¹²⁸·hi` with `hi < 2¹²⁸`. -/
def Low128 (V : Valuation F) (x : F) (u : SizedF 128 (FVar F)) : Prop :=
  ∃ hi : ℕ, hi < 2 ^ 128 ∧ x = u.val.val V + 2 ^ 128 * hi

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

/-- At a prime field of more than 254 bits, a `Low128` decomposition reads, through any
prechallenge reading of its low half, as the verifier's prechallenge up to
`PrechallengeAlias` (`low128_of_decomp`). -/
theorem Low128.alias {p : ℕ} [Fact p.Prime] (hp : 2 ^ 254 < p) {V : Valuation (ZMod p)}
    {x : ZMod p} {u : SizedF 128 (FVar (ZMod p))} {m : Prechallenge}
    (hlow : Low128 V x u) (hm : Reads128 V u m) : PrechallengeAlias p (x.val % 2 ^ 128) m :=
  let ⟨hi, hhi, hx⟩ := hlow
  low128_of_decomp hp x m hi hhi (by rw [hx, hm])

end Pickles
