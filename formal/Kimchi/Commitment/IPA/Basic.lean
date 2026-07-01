import Mathlib

/-!
# The kimchi IPA polynomial commitment — structured reference string and commitment

Implementation-only transcription of the data and functions of the kimchi
inner-product-argument (IPA) polynomial commitment scheme, exactly as deployed in
`proof-systems` (`poly-commitment/src/ipa.rs` and `commitment.rs`), cross-checked
against the Ironwood halo2 transcription (`references/ironwood/`).

This file (`Basic.lean`) carries the structured reference string, the (hiding)
commitment, the scalar inner product, the evaluation vector, the challenge
polynomial `b` and its coefficient vector, and the opening relation. It is
curve-generic over a scalar field `F` and an `F`-module `G` (the curve group,
written additively).

**These are DEFINITIONS ONLY** — no soundness, binding, or knowledge statement
appears here; the group and field are abstract and no hardness assumption is
invoked. `k` is the number of IPA rounds; the argument operates on `2 ^ k`
generators / coefficients.

Blueprint: `chapters/Kimchi_Commitment_IPA.tex` (§Basic).
-/

namespace Kimchi.Commitment.IPA

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- IPA structured reference string.

Source: ipa.rs, `struct SRS<G>` (l.41) and `u_base` (l.773). Carries a round
count `k`, a vector of committing generators `g : Fin (2 ^ k) → G` (`SRS.g`), a
blinding base `h : G` (`SRS.h`), and the IPA generator `U : G` (`u_base`;
Ironwood `URS.u`). The `lagrange_bases` cache is an optimisation with no
cryptographic content and is omitted. (`def:ipa_srs`) -/
structure SRS (G : Type*) where
  /-- Number of IPA rounds; the committing set has `2 ^ k` entries. -/
  k : ℕ
  /-- The vector of committing generators. -/
  g : Fin (2 ^ k) → G
  /-- The blinding base `H`. -/
  h : G
  /-- The IPA randomisation base `U` (`u_base`). -/
  U : G

/-- Generator commitment `⟨a, g⟩ = ∑ i, a i • g i`.

Source: ipa.rs, `commit_non_hiding` (l.516), the MSM `⟨a, g⟩`. This size-generic
form is reused for the SRS commitment and for the cross-terms. (`def:ipa_commitGen`) -/
def commitGen {n : ℕ} (g : Fin n → G) (a : Fin n → F) : G := ∑ i, a i • g i

/-- Hiding commitment `Commit_σ(a, r) = ⟨a, σ.g⟩ + r • σ.h`.

Source: ipa.rs, `commit_non_hiding` (l.516) ∘ `mask` (l.488). (`def:ipa_commit`) -/
def commit (σ : SRS G) (a : Fin (2 ^ σ.k) → F) (r : F) : G :=
  commitGen σ.g a + r • σ.h

/-- Scalar inner product `⟨a, b⟩ = ∑ i, a i * b i`.

Source: ipa.rs, `inner_prod` (used at l.809, l.819). (`def:ipa_innerProduct`) -/
def innerProduct {n : ℕ} (a b : Fin n → F) : F := ∑ i, a i * b i

/-- Evaluation vector `evalVector(n, x) i = x ^ i`.

Source: ipa.rs `open`, the powers vector `pows` (l.746); Ironwood `evalVector`.
The inner product `⟨a, evalVector(n, x)⟩` is `∑ i, a i * x ^ i`, the polynomial
with coefficients `a` evaluated at `x`. (`def:ipa_evalVector`) -/
def evalVector (n : ℕ) (x : F) : Fin n → F := fun i => x ^ (i : ℕ)

/-- Challenge polynomial `b` evaluated at `x`:
`bPoly(chal, x) = ∏ i, (1 + chal i * x ^ (2 ^ (k - 1 - i)))`.

Source: commitment.rs, `b_poly` (l.416, product at l.425). This is the linear
(asymmetric) form `∏ (1 + u * X ^ (2 ^ i))` — NOT the symmetric
`∏ (u⁻¹ + u * X ^ (2 ^ i))` of the Halo 2019 paper. (`def:ipa_bPoly`) -/
def bPoly {k : ℕ} (chal : Fin k → F) (x : F) : F :=
  ∏ i : Fin k, (1 + chal i * x ^ (2 ^ (k - 1 - (i : ℕ))))

/-- The `2 ^ k` coefficients of `bPoly`: for `m : Fin (2 ^ k)`,
`s_m = ∏ j, if bit j of m is set then chal (Fin.rev j) else 1`,
where `Fin.rev j = k - 1 - j`.

Source: commitment.rs, `b_poly_coefficients` (l.454). (`def:ipa_bPolyCoefficients`) -/
def bPolyCoefficients {k : ℕ} (chal : Fin k → F) : Fin (2 ^ k) → F :=
  fun m => ∏ j : Fin k, if Nat.testBit (m : ℕ) (j : ℕ) then chal (Fin.rev j) else 1

/-- Opening relation: witness `(a, r)` opens commitment `P` at `x` to value `v`
when `commit σ a r = P ∧ v = ⟨a, evalVector (2 ^ σ.k) x⟩`.

Source: ipa.rs `open`, `combined_inner_product` (l.755); Ironwood `IpaRelation`.
This is the relation the inner-product argument is an argument of knowledge for.
(`def:ipa_openingRelation`) -/
def openingRelation (σ : SRS G) (P : G) (x v : F) (a : Fin (2 ^ σ.k) → F) (r : F) : Prop :=
  commit σ a r = P ∧ v = innerProduct a (evalVector (2 ^ σ.k) x)

end Kimchi.Commitment.IPA
