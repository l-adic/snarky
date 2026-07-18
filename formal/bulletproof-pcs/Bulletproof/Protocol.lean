import Mathlib

/-!
# The kimchi IPA polynomial commitment — the abstract protocol

The definitions of the kimchi inner-product-argument (IPA) polynomial commitment,
curve-generic over a scalar field `F` and an `F`-module `G` (the curve group): the
structured reference string and commitment (§ SRS and commitment), the opening proof
and single-opening verifier (§ opening proof and verifier), the batched multi-polynomial
multi-point opening (§ batched opening), and the chunk layer for polynomials wider than
the SRS (§ chunk layer). No hardness assumption is invoked; soundness over these
definitions is `Bulletproof.Soundness`.
-/

/-!
## The kimchi IPA polynomial commitment — structured reference string and commitment

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

end Bulletproof

/-!
## The kimchi IPA opening proof and verifier

The final stage of the kimchi inner-product-argument (IPA) polynomial commitment:
the opening proof structure, the recombined commitment `Q`, and the verifier's
acceptance equation. Definitions only; the group `G` and field `F` are abstract.

The scheme is asymmetric: `bPoly = ∏(1 + u · x ^ (2 ^ i))` and the recombination
uses `u⁻¹ • L + u • R`. The opening proof has no final-scalar field — the final
folded scalar `a₀` is absorbed into the Schnorr response `z1 = a₀ · c + d`.
-/

namespace Bulletproof

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

/-- The verifier acceptance equation with the evaluation slot abstracted to a free
scalar `b0`. With final Schnorr challenge `c`, accepts iff both hold:

* `c • Q + δ = z1 • sg + (z1 · b0) • σ.U + z2 • σ.h` (Schnorr check, with
  `Q = recombine σ P v u proof.lr`);
* `sg = ⟨bPolyCoefficients u, σ.g⟩` (the `sg`-correctness check).

`VerifierAccepts` is the specialization at `b0 = bPoly u x`; the batched verifier
feeds `b0 = combinedB u r x` (see `IPA/Batch.lean`). -/
def VerifierAcceptsAt (σ : SRS G) (proof : OpeningProof F G σ.k) (P : G) (b0 v c : F)
    (u : Fin σ.k → F) : Prop :=
  (c • recombine σ P v u proof.lr + proof.delta
      = proof.z1 • proof.sg + (proof.z1 * b0) • σ.U + proof.z2 • σ.h)
  ∧ (proof.sg = commitGen σ.g (bPolyCoefficients u))

/-- The verifier accepts, with final Schnorr challenge `c`, iff both hold. This is
`VerifierAcceptsAt` at `b0 = bPoly u x`:

* `c • Q + δ = z1 • sg + (z1 · bPoly(u, x)) • σ.U + z2 • σ.h` (the Schnorr check,
  with `Q = recombine σ P v u proof.lr`);
* `sg = ⟨bPolyCoefficients u, σ.g⟩` (the `sg`-correctness check: the final folded
  generator is the challenge-coefficient combination of the generators). -/
def VerifierAccepts (σ : SRS G) (proof : OpeningProof F G σ.k) (P : G) (x v c : F)
    (u : Fin σ.k → F) : Prop :=
  VerifierAcceptsAt σ proof P (bPoly u x) v c u

end Bulletproof

/-!
## Batched multi-polynomial, multi-point opening of the kimchi IPA commitment

The kimchi verifier never opens one polynomial at one point: it opens ~20
commitments at the two points `{ζ, ζω}` through ONE IPA opening of a random linear
combination — `polyscale ξ` across polynomials, `evalscale r` across evaluation
points. This file defines that batching over the single-opening IPA stack
(`Basic`/`Verify`).

The batched setting fixes:

* `n` committed segments, indexed `i : Fin n`, with commitments `C : Fin n → G` — one
  segment per entry (a multi-chunk commitment enters as consecutive entries);
* `m` evaluation points `x : Fin m → F` (for vanilla PlonK, `m = 2`);
* claimed evaluations `e : Fin n → Fin m → F`, where `e i j` is the prover's
  claimed value of polynomial `i` at point `x j`.

The combiners transcribe the deployed verifier's commitment/value aggregation and its
`b₀` evaluation slot; their faithfulness is by transcription. The `rand_base` cross-proof
MSM batching and the Fiat–Shamir sponge are out of scope.

The chunked-batch section generalizes the combiners to per-polynomial chunk counts
(`nc : Fin n → ℕ`): in the deployed batch each chunk is one *segment*, consumed
polynomial-outer, chunk-inner, at one consecutive polyscale power per segment
(`combined_inner_product` / `combine_commitments`, `poly-commitment/src/commitment.rs`).
The flattening lemmas show the chunked combiners are the plain combiners of the
flattened segment family under `finSigmaFinEquiv` — chunking changes the indexing, not
the combination — which is how `Soundness/ChunkedBatch.lean` reduces chunked-batch
soundness to `batch_soundnessA`.
-/

namespace Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Batch definitions -/

/-- Combined commitment: the random linear combination of the commitments by
powers of the polyscale `ξ`,
`combinedCommitment ξ C = ∑ i, ξ ^ i • C i`.

At `rand_base = 1`, over the segment entries; the `rand_base`
cross-proof MSM randomiser is out of scope. -/
def combinedCommitment (ξ : F) {n : ℕ} (C : Fin n → G) : G :=
  ∑ i : Fin n, ξ ^ (i : ℕ) • C i

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

/-! ## Chunked batch definitions

Chunked commitments in the batch (`PolyComm` with more than one chunk): each chunk of
each polynomial is one *segment* of the batch stream, and the stream is consumed
polynomial-outer, chunk-inner, at one consecutive polyscale power per segment. The
combiners below transcribe that layout for per-polynomial chunk counts `nc : Fin n → ℕ`;
the flattening lemmas identify them with the plain combiners of the flattened segment
family, so the flat soundness stack applies to chunked batches. -/

/-- The polyscale power at which the chunks of polynomial `i` begin: the total chunk
count of the earlier polynomials. Chunk `c` of polynomial `i` is segment
`segmentOffset nc i + c` of the batch stream — `finSigmaFinEquiv`'s value
(`segment_flatten_val`). -/
private def segmentOffset {n : ℕ} (nc : Fin n → ℕ) (i : Fin n) : ℕ :=
  ∑ i' : Fin i.val, nc (Fin.castLE i.isLt.le i')

/-- The flat position of chunk `c` of polynomial `i` is `segmentOffset nc i + c` —
`finSigmaFinEquiv` in the batch's vocabulary. -/
private theorem segment_flatten_val {n : ℕ} {nc : Fin n → ℕ} (i : Fin n) (c : Fin (nc i)) :
    ((finSigmaFinEquiv ⟨i, c⟩ : Fin (∑ i', nc i')) : ℕ)
      = segmentOffset nc i + (c : ℕ) :=
  finSigmaFinEquiv_apply ⟨i, c⟩

/-- Chunked combined commitment (`combine_commitments` at `rand_base = 1`): the
polyscale combination of the segment stream,
`∑ i, ∑ c, ξ ^ (segmentOffset nc i + c) • C i c`. At one chunk per polynomial the
offsets collapse to `i` and this is `combinedCommitment`. -/
def chunkedCombinedCommitment (ξ : F) {n : ℕ} {nc : Fin n → ℕ}
    (C : (i : Fin n) → Fin (nc i) → G) : G :=
  ∑ i, ∑ c : Fin (nc i), ξ ^ (segmentOffset nc i + (c : ℕ)) • C i c

/-- Chunked combined inner product (`combined_inner_product`): segment `(i, c)`
contributes its evalscale-combined point values at the segment's polyscale power,
`∑ i, ∑ c, ξ ^ (segmentOffset nc i + c) * (∑ j, e i c j * r ^ j)` — the documented
`Σₖ Σᵢ polyscale^{k·n+i} (Σⱼ polys[k][j][i] · evalscale^j)`, at ragged chunk counts. -/
def chunkedCombinedInnerProduct (ξ r : F) {n m : ℕ} {nc : Fin n → ℕ}
    (e : (i : Fin n) → Fin (nc i) → Fin m → F) : F :=
  ∑ i, ∑ c : Fin (nc i), ξ ^ (segmentOffset nc i + (c : ℕ)) * (∑ j, e i c j * r ^ (j : ℕ))

/-- **Commitment flattening.** The chunked combined commitment is the plain
`combinedCommitment` of the flattened segment family: chunking changes the indexing,
not the combination. -/
theorem chunkedCombinedCommitment_eq_flat (ξ : F) {n : ℕ} {nc : Fin n → ℕ}
    (C : (i : Fin n) → Fin (nc i) → G) :
    chunkedCombinedCommitment ξ C
      = combinedCommitment ξ (fun s : Fin (∑ i, nc i) =>
          C (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2) := by
  rw [combinedCommitment,
    ← Equiv.sum_comp (finSigmaFinEquiv (n := nc))
      (fun s : Fin (∑ i, nc i) => ξ ^ (s : ℕ)
        • C (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2)]
  rw [chunkedCombinedCommitment, ← Fintype.sum_sigma']
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Equiv.symm_apply_apply, segment_flatten_val]

/-- **Value flattening.** The chunked combined inner product is the plain
`combinedInnerProduct` of the flattened evaluation family. -/
theorem chunkedCombinedInnerProduct_eq_flat (ξ r : F) {n m : ℕ} {nc : Fin n → ℕ}
    (e : (i : Fin n) → Fin (nc i) → Fin m → F) :
    chunkedCombinedInnerProduct ξ r e
      = combinedInnerProduct ξ r (fun s : Fin (∑ i, nc i) =>
          e (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2) := by
  rw [combinedInnerProduct,
    ← Equiv.sum_comp (finSigmaFinEquiv (n := nc))
      (fun s : Fin (∑ i, nc i) => ξ ^ (s : ℕ)
        * ∑ j, e (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2 j
            * r ^ (j : ℕ))]
  rw [chunkedCombinedInnerProduct, ← Fintype.sum_sigma']
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Equiv.symm_apply_apply, segment_flatten_val]

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

end Bulletproof

/-!
## The chunk layer: long polynomials over a bounded SRS

Kimchi's SRS commits at most `2^k` coefficients, but committed polynomials exceed that
bound — the quotient `t` does in *every* proof (degree `~7·n` against an SRS of size
`n`). The scheme's answer (`poly_commitment/src/commitment.rs`) is chunking: split the
coefficients into width-`2^k` windows, commit each window (`PolyComm.elems`), and at
evaluation time recombine with powers of `y = x^(2^k)` — one combined commitment, one
combined claimed value, one IPA run.

The definitions of the chunk layer: the chunk windows (`chunkCoeffs`/`chunkPoly`), the
assembly inverse (`assemblePoly` — the long polynomial with prescribed windows, the
extractor's tool in `Soundness/ChunkedBatch.lean`), the eval recombination
(`eval_eq_sum_chunkPoly` — the reassembly `p = ∑ Xⁱ·²ᵏ · chunkᵢ` read at a point,
kimchi's `combined_inner_product` identity), and the commitment recombination
(`commit_combine` — kimchi's `chunk_commitment`, by linearity). Chunked-opening
soundness over these definitions is `Soundness/Chunk.lean`.
-/

namespace Bulletproof

open Polynomial

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Chunk windows -/

/-- The `i`-th width-`n` coefficient window of `p`, as the vector kimchi commits
(`PolyComm.elems i`). -/
def chunkCoeffs (n : ℕ) (p : Polynomial F) (i : ℕ) : Fin n → F :=
  fun j => p.coeff (i * n + (j : ℕ))

/-- The `i`-th window as a polynomial of degree `< n`. -/
noncomputable def chunkPoly (n : ℕ) (p : Polynomial F) (i : ℕ) : Polynomial F :=
  ∑ j ∈ Finset.range n, monomial j (p.coeff (i * n + j))

private theorem chunkPoly_natDegree_lt {n : ℕ} (hn : 0 < n) (p : Polynomial F) (i : ℕ) :
    (chunkPoly n p i).natDegree < n := by
  apply lt_of_le_of_lt (natDegree_sum_le _ _)
  rw [Finset.fold_max_lt]
  exact ⟨hn, fun j hj =>
    lt_of_le_of_lt (natDegree_monomial_le _) (Finset.mem_range.mp hj)⟩

/-- A chunk's evaluation is its window's inner product with the evaluation vector —
the bridge between the polynomial view and the committed-vector view. -/
theorem chunkPoly_eval (n : ℕ) (p : Polynomial F) (i : ℕ) (x : F) :
    (chunkPoly n p i).eval x = innerProduct (chunkCoeffs n p i) (evalVector n x) := by
  unfold chunkPoly innerProduct chunkCoeffs evalVector
  rw [eval_finsetSum]
  simp only [eval_monomial]
  exact (Fin.sum_univ_eq_sum_range (fun j => p.coeff (i * n + j) * x ^ j) n).symm

/-! ## Eval recombination -/

/-- Splitting a `range (c·n)` sum into `c` windows of width `n`. -/
private theorem sum_range_mul_eq_sum_windows {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (c n : ℕ) :
    ∑ m ∈ Finset.range (c * n), f m
      = ∑ i ∈ Finset.range c, ∑ j ∈ Finset.range n, f (i * n + j) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- **Eval recombination** — the reassembly `p = ∑ᵢ X^(i·n) · chunkᵢ` read at a point:
a polynomial of degree `< c·n` evaluates as the `(x^n)`-power combination of its chunk
evaluations. The identity behind kimchi's `combined_inner_product`. -/
theorem eval_eq_sum_chunkPoly {n c : ℕ} (p : Polynomial F)
    (hdeg : p.natDegree < c * n) (x : F) :
    p.eval x = ∑ i ∈ Finset.range c, (x ^ n) ^ i * (chunkPoly n p i).eval x := by
  rw [eval_eq_sum_range' hdeg, sum_range_mul_eq_sum_windows]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold chunkPoly
  rw [eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_monomial, ← pow_mul, ← mul_assoc, mul_comm ((x ^ (n * i))) _, mul_assoc,
    ← pow_add, mul_comm n i]

/-! ## Assembly

The inverse of windowing: build the long polynomial with prescribed width-`n` chunk
windows. This is the extractor's tool — chunked-batch soundness
(`Soundness/ChunkedBatch.lean`) produces per-chunk witness vectors and assembles them
into the one bound polynomial the commitment opens to. -/

/-- The polynomial with chunk window `ci` equal to `as ci`, for `ci < c`
(`chunkCoeffs_assemblePoly`). -/
noncomputable def assemblePoly (n c : ℕ) (as : ℕ → Fin n → F) : Polynomial F :=
  ∑ ci ∈ Finset.range c, ∑ j : Fin n, monomial (ci * n + (j : ℕ)) (as ci j)

theorem assemblePoly_coeff {n c : ℕ} (as : ℕ → Fin n → F) {ci : ℕ} (hci : ci < c)
    (j : Fin n) : (assemblePoly n c as).coeff (ci * n + (j : ℕ)) = as ci j := by
  -- The windows are disjoint: `ci' * n + j' = ci * n + j` with `j', j < n` forces
  -- `ci' = ci` (divide by `n`) and then `j' = j`.
  have hdiv : ∀ (a b : ℕ), b < n → (a * n + b) / n = a := fun a b hb => by
    rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hb, add_zero]
  unfold assemblePoly
  simp only [finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single ci, Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro j' _ hj'
    rw [if_neg fun h => hj' (Fin.ext (by omega))]
  · intro h
    exact absurd (Finset.mem_univ j) h
  · intro ci' _ hci'
    refine Finset.sum_eq_zero fun j' _ => if_neg fun h => hci' ?_
    have h' : ci' = (ci * n + (j : ℕ)) / n := by rw [← hdiv ci' j' j'.isLt, h]
    rw [hdiv ci j j.isLt] at h'
    exact h'
  · intro h
    exact absurd (Finset.mem_range.mpr hci) h

/-- Assembly inverts windowing: chunk `ci` of `assemblePoly n c as` is `as ci`. -/
theorem chunkCoeffs_assemblePoly {n c : ℕ} (as : ℕ → Fin n → F) {ci : ℕ}
    (hci : ci < c) : chunkCoeffs n (assemblePoly n c as) ci = as ci :=
  funext fun j => assemblePoly_coeff as hci j

/-- The assembled polynomial meets the chunk-count degree bound. -/
theorem assemblePoly_natDegree_lt {n c : ℕ} (hn : 0 < n) (hc : 0 < c)
    (as : ℕ → Fin n → F) : (assemblePoly n c as).natDegree < c * n := by
  have hcn : 0 < c * n := Nat.mul_pos hc hn
  apply lt_of_le_of_lt (natDegree_sum_le _ _)
  rw [Finset.fold_max_lt]
  refine ⟨hcn, fun ci hci => ?_⟩
  apply lt_of_le_of_lt (natDegree_sum_le _ _)
  rw [Finset.fold_max_lt]
  refine ⟨hcn, fun j _ => ?_⟩
  apply lt_of_le_of_lt (natDegree_monomial_le _)
  have h1 : ci * n + (j : ℕ) < (ci + 1) * n := by
    have := j.isLt
    rw [add_mul, one_mul]
    omega
  exact lt_of_lt_of_le h1
    (Nat.mul_le_mul_right n (Finset.mem_range.mp hci))

/-! ## Commitment recombination -/

/-- **The hiding commitment is `F`-linear** in the witness pair `(a, r)` — the
first-class form of "commit is linear"; every recombination fact is an image of a
module identity under this map. -/
def commitₗ (σ : SRS G) : ((Fin (2 ^ σ.k) → F) × F) →ₗ[F] G where
  toFun p := commit σ p.1 p.2
  map_add' p q := by
    unfold commit commitGen
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
    abel
  map_smul' t p := by
    unfold commit commitGen
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
      smul_add, Finset.smul_sum, RingHom.id_apply]

/-- **Commitment recombination** — kimchi's `chunk_commitment` formula: the `y`-power
combination of hiding commitments is the hiding commitment of the `y`-power-combined
witness. `map_sum` of `commitₗ` at the family `i ↦ yⁱ • (asᵢ, rsᵢ)`. -/
theorem commit_combine (σ : SRS G) (y : F) (c : ℕ)
    (as : ℕ → Fin (2 ^ σ.k) → F) (rs : ℕ → F) :
    ∑ i ∈ Finset.range c, y ^ i • commit σ (as i) (rs i)
      = commit σ (∑ i ∈ Finset.range c, y ^ i • as i)
          (∑ i ∈ Finset.range c, y ^ i • rs i) := by
  have hpair : (∑ i ∈ Finset.range c, y ^ i • ((as i, rs i) : (Fin (2 ^ σ.k) → F) × F))
      = (∑ i ∈ Finset.range c, y ^ i • as i, ∑ i ∈ Finset.range c, y ^ i • rs i) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      exact Finset.sum_congr rfl fun i _ => rfl
    · rw [Prod.snd_sum]
      exact Finset.sum_congr rfl fun i _ => rfl
  have hmap : commitₗ σ (∑ i ∈ Finset.range c,
        y ^ i • ((as i, rs i) : (Fin (2 ^ σ.k) → F) × F))
      = ∑ i ∈ Finset.range c, y ^ i • commit σ (as i) (rs i) := by
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [← hmap, hpair]
  rfl

/-- The inner product is linear in its first argument — the vector side of the same
recombination. -/
theorem innerProduct_combine {n : ℕ} (y : F) (c : ℕ) (as : ℕ → Fin n → F)
    (b : Fin n → F) :
    innerProduct (∑ i ∈ Finset.range c, y ^ i • as i) b
      = ∑ i ∈ Finset.range c, y ^ i * innerProduct (as i) b := by
  unfold innerProduct
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Bulletproof
