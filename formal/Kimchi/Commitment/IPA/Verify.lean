import Mathlib
import Kimchi.Commitment.IPA.Basic

/-!
# The kimchi IPA opening proof and verifier

The final stage of the kimchi inner-product-argument (IPA) polynomial commitment:
the opening proof structure, the recombined commitment `Q`, and the verifier's
acceptance equation. Definitions only; the group `G` and field `F` are abstract.

The scheme is asymmetric: `bPoly = ∏(1 + u · x ^ (2 ^ i))` and the recombination
uses `u⁻¹ • L + u • R`. The opening proof has no final-scalar field — the final
folded scalar `a₀` is absorbed into the Schnorr response `z1 = a₀ · c + d`.
-/

namespace Kimchi.Commitment.IPA

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## The opening proof -/

/-- An IPA opening proof over `k` rounds: the per-round cross-commitments
`lr : Fin k → G × G`, the Schnorr commitment `delta : G`, the Schnorr responses
`z1 z2 : F`, and the final folded generator `sg : G` (`= g₀`).

There is no field for the final folded scalar `a₀`: it is not sent, but absorbed
into the Schnorr response `z1 = a₀ · c + d`. -/
structure OpeningProof (F G : Type*) (k : ℕ) where
  /-- The `k` rounds of `(L, R)` cross-commitments. -/
  lr : Fin k → G × G
  /-- The Schnorr commitment `δ`. -/
  delta : G
  /-- The first Schnorr response `z1 = a₀ · c + d`. -/
  z1 : F
  /-- The second Schnorr response `z2 = r' · c + r_delta`. -/
  z2 : F
  /-- The final folded generator `sg = g₀`. -/
  sg : G

/-! ## The recombined commitment `Q` -/

/-- Recombined commitment `Q`. For a commitment `P`, opened value `v`, round
challenges `u`, and cross-commitments `lr`,
`Q = P + v • σ.U + ∑ j, (uⱼ⁻¹ • Lⱼ + uⱼ • Rⱼ)`, where `(Lⱼ, Rⱼ) = lr j`. The term
`P + v • σ.U` folds the opened value into the commitment against the base `U`. -/
def recombine (σ : SRS G) (P : G) (v : F) {k : ℕ} (u : Fin k → F)
    (lr : Fin k → G × G) : G :=
  P + v • σ.U + ∑ j : Fin k, ((u j)⁻¹ • (lr j).1 + (u j) • (lr j).2)

/-! ## The verifier acceptance equation -/

/-- The verifier accepts, with final Schnorr challenge `c`, iff both hold:

* `c • Q + δ = z1 • sg + (z1 · bPoly(u, x)) • σ.U + z2 • σ.h` (the Schnorr check,
  with `Q = recombine σ P v u proof.lr`);
* `sg = ⟨bPolyCoefficients u, σ.g⟩` (the `sg`-correctness check: the final folded
  generator is the challenge-coefficient combination of the generators). -/
def VerifierAccepts (σ : SRS G) (proof : OpeningProof F G σ.k) (P : G) (x v c : F)
    (u : Fin σ.k → F) : Prop :=
  (c • recombine σ P v u proof.lr + proof.delta
      = proof.z1 • proof.sg + (proof.z1 * bPoly u x) • σ.U + proof.z2 • σ.h)
  ∧ (proof.sg = commitGen σ.g (bPolyCoefficients u))

end Kimchi.Commitment.IPA
