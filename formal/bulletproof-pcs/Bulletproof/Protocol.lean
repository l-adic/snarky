import Mathlib

/-!
# The kimchi IPA polynomial commitment: its algebra

The curve-generic pieces of the inner-product-argument commitment that the executable wire
verifier (`Bulletproof.Ipa`) is stated with, over a scalar field `F` and an `F`-module `G`
(the curve group, written additively): the structured reference string, the generator
commitment and its linearity, the challenge polynomial `b` with its coefficient vector, and
the batched opening's two scalar combiners. Throughout, `k` is the number of IPA rounds, so
the argument operates on `2 ^ k` generators and coefficients.
-/

namespace Bulletproof

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

/-- The generator commitment is `F`-linear in the witness: `commitGen g` as a linear map,
Mathlib's `Fintype.linearCombination`. -/
def commitGenₗ {n : ℕ} (g : Fin n → G) : (Fin n → F) →ₗ[F] G :=
  Fintype.linearCombination F g

theorem commitGenₗ_apply {n : ℕ} (g : Fin n → G) (a : Fin n → F) :
    commitGenₗ g a = commitGen g a := rfl

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

/-- Combined inner product: the aggregated claimed evaluation. Each polynomial `i`
contributes one segment scaled by `ξ ^ i`; within a segment, the point-values are
read as coefficients of a polynomial in `r` and evaluated at `r`,
`combinedInnerProduct ξ r e = ∑ i, ξ ^ i * (∑ j, e i j * r ^ j)`.

Over the segment entries the general exponent `k * n + i` reads `i`. -/
def combinedInnerProduct (ξ r : F) {n m : ℕ} (e : Fin n → Fin m → F) : F :=
  ∑ i : Fin n, ξ ^ (i : ℕ) * (∑ j : Fin m, e i j * r ^ (j : ℕ))

/-- Combined `b₀`: the single-scalar evaluation slot of the batched verifier — the
challenge polynomial `bPoly u ·` evaluated at each point and combined by powers of
the evalscale `r`,
`combinedB u r x = ∑ j, r ^ j * bPoly u (x j)`. -/
def combinedB {k : ℕ} (u : Fin k → F) (r : F) {m : ℕ} (x : Fin m → F) : F :=
  ∑ j : Fin m, r ^ (j : ℕ) * bPoly u (x j)

end Bulletproof
