import Bulletproof.Soundness
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Inductions

/-!
# The chunk layer: long polynomials over a bounded SRS

Kimchi's SRS commits at most `2^k` coefficients, but committed polynomials exceed that
bound — the quotient `t` does in *every* proof (degree `~7·n` against an SRS of size
`n`). The scheme's answer (`poly_commitment/src/commitment.rs`) is chunking: split the
coefficients into width-`2^k` windows, commit each window (`PolyComm.elems`), and at
evaluation time recombine with powers of `y = x^(2^k)` — one combined commitment, one
combined claimed value, one IPA run.

This file is the additive layer over the `nc = 1` argument: the chunk windows
(`chunkCoeffs`/`chunkPoly`), the assembly inverse (`assemblePoly` — the long polynomial
with prescribed windows, the extractor's tool in `Soundness/ChunkedBatch.lean`), the
eval recombination (`eval_eq_sum_chunkPoly` — the reassembly `p = ∑ Xⁱ·²ᵏ · chunkᵢ`
read at a point, kimchi's `combined_inner_product`
identity), the commitment recombination (`commit_combine` — kimchi's
`chunk_commitment`, by linearity), and the headline `chunked_ipa_soundness`: under
commitment binding, an accepting IPA run on the combined commitment of honestly
committed chunks forces the claimed value to be the *full* polynomial's evaluation.
No existing statement changes; the `nc = 1` theorems are the kernel this composes onto,
mirroring the verifier's own combine-then-open order. The chunk count is the degree
bound (`natDegree_lt_of_chunks` is deferred to the consumer — here the bound enters as
the hypothesis `p.natDegree < c · 2^k`).
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

theorem chunkPoly_natDegree_lt {n : ℕ} (hn : 0 < n) (p : Polynomial F) (i : ℕ) :
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
theorem sum_range_mul_eq_sum_windows {M : Type*} [AddCommMonoid M]
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

/-! ## The headline -/

/-- **Chunked opening soundness.** The verifier combines the chunk commitments with
powers of `y = x^(2^k)` and runs one IPA on the combination — kimchi's chunked
opening. Under commitment binding, an accepting run against honestly committed chunks
of `p` (degree `< c·2^k`) forces the claimed value to be `p.eval x`: binding pins the
extracted witness to the combined chunk vector, whose inner product with the
evaluation vector is `p`'s evaluation by recombination. -/
theorem chunked_ipa_soundness (σ : SRS G) (proof : OpeningProof F G σ.k)
    (hbind : CommitmentBinding (F := F) σ)
    (p : Polynomial F) (c : ℕ) (hdeg : p.natDegree < c * 2 ^ σ.k)
    (rs : ℕ → F) (x v cc : F) (u : Fin σ.k → F) (P : G)
    (hP : P = ∑ i ∈ Finset.range c,
      (x ^ 2 ^ σ.k) ^ i • commit σ (chunkCoeffs (2 ^ σ.k) p i) (rs i))
    (hFS : FiatShamirTree σ P x v (VerifierAccepts σ proof P x v cc u))
    (hacc : VerifierAccepts σ proof P x v cc u) :
    v = p.eval x := by
  obtain ⟨a, r, hopen⟩ := ipa_soundness σ proof P x v cc u hFS hacc
  have hhonest : commit σ
      (∑ i ∈ Finset.range c, (x ^ 2 ^ σ.k) ^ i • chunkCoeffs (2 ^ σ.k) p i)
      (∑ i ∈ Finset.range c, (x ^ 2 ^ σ.k) ^ i • rs i) = P := by
    rw [hP, commit_combine]
  have hpair := @hbind (a, r) (_, _) (hopen.1.trans hhonest.symm)
  have ha : a = ∑ i ∈ Finset.range c, (x ^ 2 ^ σ.k) ^ i • chunkCoeffs (2 ^ σ.k) p i :=
    (Prod.ext_iff.mp hpair).1
  have hval : innerProduct
      (∑ i ∈ Finset.range c, (x ^ 2 ^ σ.k) ^ i • chunkCoeffs (2 ^ σ.k) p i)
      (evalVector (2 ^ σ.k) x) = p.eval x := by
    rw [innerProduct_combine, eval_eq_sum_chunkPoly p hdeg x]
    exact Finset.sum_congr rfl fun i _ => by rw [chunkPoly_eval]
  rw [hopen.2, ha]
  exact hval

end Bulletproof
