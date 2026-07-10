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
its header for the trust boundary. The `rand_base`/`sg_rand_base` cross-proof MSM
batching and the Fiat–Shamir sponge are out of scope.

The chunked-batch section generalizes the combiners to per-polynomial chunk counts
(`nc : Fin n → ℕ`): in the deployed batch each chunk is one *segment*, consumed
polynomial-outer, chunk-inner, at one consecutive polyscale power per segment
(`combined_inner_product` / `combine_commitments`, `poly-commitment/src/commitment.rs`).
The flattening lemmas show the chunked combiners are the plain combiners of the
flattened segment family under `finSigmaFinEquiv` — chunking changes the indexing, not
the combination — which is how `Soundness/ChunkedBatch.lean` reduces chunked-batch
soundness to `batch_soundness`.
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

/-! ## Chunked batch definitions

Chunked commitments in the batch (`PolyComm` with more than one chunk): each chunk of
each polynomial is one *segment* of the batch stream, and the stream is consumed
polynomial-outer, chunk-inner, at one consecutive polyscale power per segment. The
combiners below transcribe that layout for per-polynomial chunk counts `nc : Fin n → ℕ`;
the flattening lemmas identify them with the plain combiners of the flattened segment
family, so the `nc = 1` soundness stack applies verbatim to chunked batches. -/

/-- The polyscale power at which the chunks of polynomial `i` begin: the total chunk
count of the earlier polynomials. Chunk `c` of polynomial `i` is segment
`segmentOffset nc i + c` of the batch stream — `finSigmaFinEquiv`'s value
(`segment_flatten_val`). -/
def segmentOffset {n : ℕ} (nc : Fin n → ℕ) (i : Fin n) : ℕ :=
  ∑ i' : Fin i.val, nc (Fin.castLE i.isLt.le i')

/-- The flat position of chunk `c` of polynomial `i` is `segmentOffset nc i + c` —
`finSigmaFinEquiv` in the batch's vocabulary. -/
theorem segment_flatten_val {n : ℕ} {nc : Fin n → ℕ} (i : Fin n) (c : Fin (nc i)) :
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

end Kimchi.Commitment.IPA
