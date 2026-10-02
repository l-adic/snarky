import Pickles.Verify

/-!
# Verifier keys at the main circuits' layouts

`KeyLayout` checks a key's public-input and old-accumulator counts against the circuit's
configuration. `WrapKeyLayout` uses the full wrap statement, including its optional-feature
cells, and the padded accumulator count. `StepKeyLayout` uses the tag's padded statement width
and the selected branch's slot count.
-/

namespace Pickles

open Snarky Kimchi.Verifier Bulletproof Bulletproof.Ipa CompElliptic.Fields.Pasta

/-- The key's metadata agrees with the circuit's public-input and old-accumulator counts. -/
structure KeyLayout {C : KimchiCurve} {nc : ℕ}
    (vk : KimchiVK C nc) (publicCount oldCount : ℕ) : Prop where
  /-- The key declares every field of the circuit's public statement. -/
  publicCount_eq : vk.publicCount = publicCount
  /-- The key declares the circuit's number of old accumulators. -/
  prevChallenges_eq : vk.prevChallenges = oldCount

/-- A key's layout is checked by comparing its two counts. -/
instance {C : KimchiCurve} {nc : ℕ} (vk : KimchiVK C nc) (p n : ℕ) :
    Decidable (KeyLayout vk p n) :=
  decidable_of_iff (vk.publicCount = p ∧ vk.prevChallenges = n)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.publicCount_eq, h.prevChallenges_eq⟩⟩

/-- A wrap key's full public statement and padded accumulator count. -/
abbrev WrapKeyLayout (vk : KimchiVK IpaPallas.curve 1) : Prop :=
  KeyLayout vk
    (CircuitType.size Fq (StatementPacked StepIPARounds (Type1 Fq) Fq)) MaxProofsVerified

/-- A step key's statement at padded width `w` and the selected branch's `n` slots. -/
abbrev StepKeyLayout {nc : ℕ} (vk : KimchiVK IpaVesta.curve nc) (w n : ℕ) : Prop :=
  KeyLayout vk
    (CircuitType.size Fp (StepStatement (UnfVal WrapIPARounds) Fp w)) n

end Pickles
