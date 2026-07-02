import Mathlib

/-!
# The kimchi IPA polynomial commitment — structured reference string and commitment

The data and functions of the kimchi inner-product-argument (IPA) polynomial
commitment scheme.

This file carries the structured reference string, the (hiding) commitment, the
scalar inner product, the evaluation vector, the challenge polynomial `b` and its
coefficient vector, and the opening relation. It is curve-generic over a scalar
field `F` and an `F`-module `G` (the curve group, written additively).

These are definitions only: the group and field are abstract and no hardness
assumption is invoked. `k` is the number of IPA rounds; the argument operates on
`2 ^ k` generators / coefficients.
-/

namespace Kimchi.Commitment.IPA

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- IPA structured reference string: a round count `k`, a vector of committing
generators `g : Fin (2 ^ k) → G`, a blinding base `h : G`, and the IPA
randomisation base `U : G`. -/
structure SRS (G : Type*) where
  /-- Number of IPA rounds; the committing set has `2 ^ k` entries. -/
  k : ℕ
  /-- The vector of committing generators. -/
  g : Fin (2 ^ k) → G
  /-- The blinding base `H`. -/
  h : G
  /-- The IPA randomisation base `U`. -/
  U : G

/-- Generator commitment `⟨a, g⟩ = ∑ i, a i • g i` — the multi-scalar
multiplication of a witness `a` against generators `g`. Size-generic, so it serves
the SRS commitment and the cross-terms alike. -/
def commitGen {n : ℕ} (g : Fin n → G) (a : Fin n → F) : G := ∑ i, a i • g i

/-- Hiding commitment `Commitσ(a, r) = ⟨a, σ.g⟩ + r • σ.h`: the generator
commitment to `a`, blinded by `r` against the blinding base. -/
def commit (σ : SRS G) (a : Fin (2 ^ σ.k) → F) (r : F) : G :=
  commitGen σ.g a + r • σ.h

/-- Scalar inner product `⟨a, b⟩ = ∑ i, a i * b i`. -/
def innerProduct {n : ℕ} (a b : Fin n → F) : F := ∑ i, a i * b i

/-- Evaluation vector `evalVector n x i = x ^ i`. The inner product
`⟨a, evalVector n x⟩ = ∑ i, a i * x ^ i` is the polynomial with coefficients `a`
evaluated at `x`. -/
def evalVector (n : ℕ) (x : F) : Fin n → F := fun i => x ^ (i : ℕ)

/-- Challenge polynomial `b` evaluated at `x`:
`bPoly(chal, x) = ∏ i, (1 + chal i * x ^ (2 ^ (k - 1 - i)))`. This is the linear
(asymmetric) form `∏ (1 + u · X ^ (2 ^ i))`, not the symmetric
`∏ (u⁻¹ + u · X ^ (2 ^ i))`. -/
def bPoly {k : ℕ} (chal : Fin k → F) (x : F) : F :=
  ∏ i : Fin k, (1 + chal i * x ^ (2 ^ (k - 1 - (i : ℕ))))

/-- The `2 ^ k` coefficients of `bPoly`: for `m : Fin (2 ^ k)`,
`s_m = ∏ j, if bit j of m is set then chal (Fin.rev j) else 1`, where
`Fin.rev j = k - 1 - j`. -/
def bPolyCoefficients {k : ℕ} (chal : Fin k → F) : Fin (2 ^ k) → F :=
  fun m => ∏ j : Fin k, if Nat.testBit (m : ℕ) (j : ℕ) then chal (Fin.rev j) else 1

/-- Opening relation: a witness `(a, r)` opens commitment `P` at `x` to value `v`
when `commit σ a r = P` and `v = ⟨a, evalVector (2 ^ σ.k) x⟩`. This is the relation
the inner-product argument is an argument of knowledge for. -/
def openingRelation (σ : SRS G) (P : G) (x v : F) (a : Fin (2 ^ σ.k) → F) (r : F) : Prop :=
  commit σ a r = P ∧ v = innerProduct a (evalVector (2 ^ σ.k) x)

end Kimchi.Commitment.IPA
