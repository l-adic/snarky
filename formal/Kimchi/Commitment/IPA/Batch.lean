import Mathlib
import Kimchi.Commitment.IPA.Verify

/-!
# Batched multi-polynomial, multi-point opening of the kimchi IPA commitment

The kimchi verifier never opens one polynomial at one point: it opens ~20
commitments at the two points `{ζ, ζω}` through ONE IPA opening of a random linear
combination — `polyscale ξ` across polynomials, `evalscale r` across evaluation
points. This file gives the definitions of that batching, on top of the
single-opening IPA stack (`Basic`/`Verify`); nothing there is redefined.

The batched setting fixes:

* `n` committed polynomials, indexed `i : Fin n`, with commitments `C : Fin n → G`
  (one chunk each, `nc = 1`);
* `m` evaluation points `x : Fin m → F` (for vanilla PlonK, `m = 2`);
* claimed evaluations `e : Fin n → Fin m → F`, where `e i j` is the prover's
  claimed value of polynomial `i` at point `x j`.

These combiners are definitional transcriptions of the deployed verifier's
commitment/value aggregation and its `b₀` evaluation slot: their faithfulness is by
transcription, not by proof. The soundness theorem (`Soundness/Batch.lean`) consumes
them as given and never re-derives the verifier's acceptance equation from them — see
its header for the trust boundary. Scope: `nc = 1` throughout; the
`rand_base`/`sg_rand_base` cross-proof MSM batching and the Fiat–Shamir sponge are
out of scope.
-/

namespace Kimchi.Commitment.IPA

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Batch definitions -/

/-- Combined commitment: the random linear combination of the commitments by
powers of the polyscale `ξ`,
`combinedCommitment ξ C = ∑ i, ξ ^ i • C i`.

At `rand_base = 1` and `nc = 1` (one chunk per commitment); the `rand_base`
cross-proof MSM randomiser is out of scope. -/
def combinedCommitment (ξ : F) {n : ℕ} (C : Fin n → G) : G :=
  ∑ i : Fin n, ξ ^ (i : ℕ) • C i

/-- Combined inner product: the aggregated claimed evaluation. Each polynomial `i`
contributes one segment scaled by `ξ ^ i`; within a segment, the point-values are
read as coefficients of a polynomial in `r` and evaluated at `r`,
`combinedInnerProduct ξ r e = ∑ i, ξ ^ i * (∑ j, e i j * r ^ j)`.

At `nc = 1` (one segment per polynomial), the general exponent `k * n + i` collapses
to `i`. -/
def combinedInnerProduct (ξ r : F) {n m : ℕ} (e : Fin n → Fin m → F) : F :=
  ∑ i : Fin n, ξ ^ (i : ℕ) * (∑ j : Fin m, e i j * r ^ (j : ℕ))

/-- Combined `b₀`: the single-scalar evaluation slot of the batched verifier — the
challenge polynomial `bPoly u ·` evaluated at each point and combined by powers of
the evalscale `r`,
`combinedB u r x = ∑ j, r ^ j * bPoly u (x j)`.

This is the scalar fed into the `b0` slot of `VerifierAcceptsAt`. -/
def combinedB {k : ℕ} (u : Fin k → F) (r : F) {m : ℕ} (x : Fin m → F) : F :=
  ∑ j : Fin m, r ^ (j : ℕ) * bPoly u (x j)

/-- Combined evaluation vector: the length-`N` vector against which the extracted
witness is opened — the evalscale-combination of the per-point evaluation vectors,
`combinedEvalVector N r x = ∑ j, r ^ j • evalVector N (x j)`, so componentwise
`combinedEvalVector N r x ℓ = ∑ j, r ^ j * (x j) ^ ℓ`.

It is the vector-level analogue of `combinedB`; stated as a `•`-combination of
`evalVector`s so the bridge lemma `innerProduct_combinedEvalVector` is pure
linearity. -/
def combinedEvalVector (N : ℕ) (r : F) {m : ℕ} (x : Fin m → F) : Fin N → F :=
  ∑ j : Fin m, r ^ (j : ℕ) • evalVector N (x j)

/-- Generalized opening relation: `openingRelation` with the eval vector abstracted
to an arbitrary `b : Fin (2 ^ σ.k) → F`. A witness `(a, ρ)` opens `P` against `b`
to value `v` iff `commit σ a ρ = P ∧ v = ⟨a, b⟩`.

The original is the specialization
`openingRelation σ P x v a ρ = openingRelationB σ P (evalVector (2 ^ σ.k) x) v a ρ`. -/
def openingRelationB (σ : SRS G) (P : G) (b : Fin (2 ^ σ.k) → F) (v : F)
    (a : Fin (2 ^ σ.k) → F) (ρ : F) : Prop :=
  commit σ a ρ = P ∧ v = innerProduct a b

/-- Batched verifier acceptance: the single-opening `VerifierAcceptsAt` check
instantiated at the combined commitment, combined `b₀`, and combined value. No new
verifier equation is invented — this is `VerifierAcceptsAt` with
`P = combinedCommitment ξ C`, `b0 = combinedB u r x`, and
`v = combinedInnerProduct ξ r e`. -/
def BatchAccepts (σ : SRS G) (proof : OpeningProof F G σ.k) (ξ r c : F)
    (u : Fin σ.k → F) {n m : ℕ} (C : Fin n → G) (x : Fin m → F)
    (e : Fin n → Fin m → F) : Prop :=
  VerifierAcceptsAt σ proof (combinedCommitment ξ C) (combinedB u r x)
    (combinedInnerProduct ξ r e) c u

/-- Inner product of the combined eval vector: for any witness `a : Fin N → F`,
`⟨a, combinedEvalVector N r x⟩ = ∑ j, r ^ j * ⟨a, evalVector N (x j)⟩`.

`⟨a, ·⟩` is `F`-linear in its second argument and `combinedEvalVector N r x` is by
definition `∑ j, r ^ j • evalVector N (x j)`; distribute the sum and pull out the
scalars `r ^ j`. -/
theorem innerProduct_combinedEvalVector {N : ℕ} (a : Fin N → F) (r : F) {m : ℕ}
    (x : Fin m → F) :
    innerProduct a (combinedEvalVector N r x)
      = ∑ j : Fin m, r ^ (j : ℕ) * innerProduct a (evalVector N (x j)) := by
  simp only [innerProduct, combinedEvalVector, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Kimchi.Commitment.IPA
