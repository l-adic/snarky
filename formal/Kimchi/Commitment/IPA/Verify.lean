import Mathlib
import Kimchi.Commitment.IPA.Basic

/-!
# The kimchi IPA opening proof and verifier (implementation)

This module transcribes the *implementation* — data and functions — of the final
stage of the kimchi inner-product-argument (IPA) polynomial commitment scheme: the
opening proof structure, the recombined commitment `Q`, and the verifier's
acceptance equation. It is a **definitions-only** file: no soundness, binding, or
special-soundness statement appears; the group `G` and field `F` are abstract and no
hardness assumption is invoked.

Ground truth is the deployed Rust in `references/ipa.rs` (`struct OpeningProof`
l.1042, `verify` acceptance l.211–227, `sg` check l.229–230, and the recombined
commitment `Q`/`P'` at l.331–342), cross-checked against `references/ironwood/`.

The kimchi IPA is **asymmetric**: `bPoly = ∏(1 + u·x^{2^i})` and the recombination
uses `u⁻¹·L + u·R`. The `OpeningProof` has **no `a` field** — the final folded
scalar `a₀` is folded into the Schnorr response `z1 = a0·c + d`.

Blueprint chapter: `chapters/Kimchi_Commitment_IPA.tex` (§Verify;
`def:ipa_openingProof`, `def:ipa_recombine`, `def:ipa_verifierAccepts`).
-/

namespace Kimchi.Commitment.IPA

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## The opening proof -/

/-- **Opening proof.** An IPA opening proof over `k` rounds records the per-round
cross-commitments `lr : Fin k → G × G`, the Schnorr commitment `delta : G`, the
Schnorr responses `z1 z2 : F`, and the final folded generator `sg : G` (`= g₀`).

There is deliberately **no `a` field**: the final folded scalar `a₀` is not sent; it
is folded into the Schnorr response `z1 = a0·c + d` (ipa.rs l.917).

Source: ipa.rs `struct OpeningProof<G, const FULL_ROUNDS>` (l.1042). -/
structure OpeningProof (F G : Type*) (k : ℕ) where
  /-- The `k` rounds of `(L, R)` cross-commitments. -/
  lr : Fin k → G × G
  /-- The Schnorr commitment `δ`. -/
  delta : G
  /-- The first Schnorr response `z1 = a0·c + d`. -/
  z1 : F
  /-- The second Schnorr response `z2 = r'·c + r_delta`. -/
  z2 : F
  /-- The final folded generator `sg = g₀`. -/
  sg : G

/-! ## The recombined commitment `Q` -/

/-- **Recombined commitment `Q`.** For a commitment `P`, opened value `v`, round
challenges `u : Fin k → F`, and cross-commitments `lr`,
`Q = P + v • σ.U + ∑ⱼ (uⱼ⁻¹ • Lⱼ + uⱼ • Rⱼ)`, where `(Lⱼ, Rⱼ) = lr j`. The term
`P + v • σ.U` is the Rust's `P' = (combined commitment) + combined_inner_product • U`.

Source: ipa.rs `verify`, `Q_i` / `P'` (l.331–342). -/
def recombine (σ : SRS G) (P : G) (v : F) {k : ℕ} (u : Fin k → F)
    (lr : Fin k → G × G) : G :=
  P + v • σ.U + ∑ j : Fin k, ((u j)⁻¹ • (lr j).1 + (u j) • (lr j).2)

/-! ## The verifier acceptance equation -/

/-- **Verifier acceptance.** With final Schnorr challenge `c`, the verifier accepts
iff both hold:

* `c • Q + δ = z1 • sg + (z1 · bPoly(u, x)) • σ.U + z2 • σ.h` (the Schnorr check,
  with `Q = recombine σ P v u proof.lr`);
* `sg = ⟨s, σ.g⟩ = ∑ᵢ sᵢ • σ.gᵢ` where `s = bPolyCoefficients u` (the `sg`-correctness
  check).

Source: ipa.rs `verify`, acceptance equation (l.211–227) + `sg` check (l.229–230). -/
def VerifierAccepts (σ : SRS G) (proof : OpeningProof F G σ.k) (P : G) (x v c : F)
    (u : Fin σ.k → F) : Prop :=
  (c • recombine σ P v u proof.lr + proof.delta
      = proof.z1 • proof.sg + (proof.z1 * bPoly u x) • σ.U + proof.z2 • σ.h)
  ∧ (proof.sg = commitGen σ.g (bPolyCoefficients u))

end Kimchi.Commitment.IPA
