import Mathlib
import Kimchi.Commitment.IPA.Batch
import Kimchi.Commitment.IPA.Chunk
import Kimchi.Commitment.IPA.Soundness.Batch

/-!
# Knowledge soundness of the chunked batched kimchi IPA opening

The headline of the chunked-batch development (`chunked_batch_soundness`): in a batch
whose commitments are chunked (`PolyComm` with per-polynomial chunk counts
`nc : Fin n → ℕ`), correct combined openings at enough distinct
`(polyscale ξ, evalscale r)` pairs bind every commitment to ONE genuine polynomial of
degree `< nc i · 2^k` — each wire chunk commits to a window of it, and each claimed
chunk evaluation is that window's true evaluation.

The proof is a reduction, not a new extraction: the flattening lemmas
(`chunkedCombinedCommitment_eq_flat` / `chunkedCombinedInnerProduct_eq_flat`, in
`Batch.lean`) identify the chunked combiners with the plain combiners of the flattened
segment family, so `batch_soundnessA` extracts one witness vector per *segment*; the
assembly layer (`assemblePoly`, in `Chunk.lean`) then reconstitutes the per-polynomial
witnesses into the bound long polynomial, whose chunk windows are the segment witnesses
by `chunkCoeffs_assemblePoly` and whose evaluations recombine the claimed chunk values
by `eval_eq_sum_chunkPoly`.

The trust boundary is that of `Soundness/Batch.lean` verbatim — the Fiat–Shamir tree
hypothesis per grid point and the no-DL-relation binding idealization; see that header.
The grid is `(∑ i, nc i) × m`: the polyscale Vandermonde must separate *segments*, so
the polyscale row count is the total chunk count, not the polynomial count.
-/

namespace Kimchi.Commitment.IPA

open Polynomial

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- **Chunked batched opening soundness.** Let `nc` be the per-polynomial chunk counts
(all positive), `ξ` injective over the segment count `∑ i, nc i`, and `r` injective over
the `m ≥ 1` evaluation points. Under the per-grid-point Fiat–Shamir hypothesis on the
chunked combiners, the no-DL-relation binding hypothesis, and acceptance at every grid
point, every polynomial of the batch is bound: there is a genuine `q i` of degree
`< nc i · 2^k` whose chunk windows are what the wire chunks commit to and whose
evaluations are the `x^(2^k)`-power recombinations of the claimed chunk evaluations. -/
theorem chunked_batch_soundness (σ : SRS G) {n m : ℕ} {nc : Fin n → ℕ}
    (hnc : ∀ i, 0 < nc i)
    (ξ : Fin (∑ i, nc i) → F) (hξ : Function.Injective ξ)
    (r : Fin m → F) (hr : Function.Injective r) (hm : 0 < m)
    (C : (i : Fin n) → Fin (nc i) → G) (x : Fin m → F)
    (e : (i : Fin n) → Fin (nc i) → Fin m → F)
    (A : Fin (∑ i, nc i) → Fin m → Prop)
    (hFS : ∀ s t, FiatShamirTreeB σ (chunkedCombinedCommitment (ξ s) C)
      (combinedEvalVector (2 ^ σ.k) (r t) x)
      (chunkedCombinedInnerProduct (ξ s) (r t) e) (A s t))
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F),
      DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (hacc : ∀ s t, A s t) :
    ∃ q : Fin n → Polynomial F, ∀ i,
      (q i).natDegree < nc i * 2 ^ σ.k
        ∧ (∀ c : Fin (nc i), ∃ ρ,
            commit σ (chunkCoeffs (2 ^ σ.k) (q i) (c : ℕ)) ρ = C i c)
        ∧ ∀ j, (q i).eval (x j)
            = ∑ c : Fin (nc i), ((x j) ^ 2 ^ σ.k) ^ (c : ℕ) * e i c j := by
  classical
  -- **Step 1 (flatten).** The chunked hypotheses are the flat-segment hypotheses.
  set C' : Fin (∑ i, nc i) → G :=
    fun s => C (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2 with hC'
  set e' : Fin (∑ i, nc i) → Fin m → F :=
    fun s => e (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2 with he'
  have hFS' : ∀ s t, FiatShamirTreeB σ (combinedCommitment (ξ s) C')
      (combinedEvalVector (2 ^ σ.k) (r t) x) (combinedInnerProduct (ξ s) (r t) e')
      (A s t) := by
    intro s t
    rw [hC', he', ← chunkedCombinedCommitment_eq_flat,
      ← chunkedCombinedInnerProduct_eq_flat]
    exact hFS s t
  -- **Step 2 (extract per segment).** One witness vector per segment.
  obtain ⟨a, ρ, hseg⟩ := batch_soundnessA σ ξ hξ r hr hm C' x e' A hFS' hbind hacc
  -- The segment data of chunk `c` of polynomial `i`, through the equiv.
  have hCseg : ∀ (i : Fin n) (c : Fin (nc i)),
      commit σ (a (finSigmaFinEquiv ⟨i, c⟩)) (ρ (finSigmaFinEquiv ⟨i, c⟩)) = C i c := by
    intro i c
    rw [(hseg (finSigmaFinEquiv ⟨i, c⟩)).1, hC']
    exact congrArg (fun p : (i : Fin n) × Fin (nc i) => C p.1 p.2)
      (Equiv.symm_apply_apply _ _)
  have hEseg : ∀ (i : Fin n) (c : Fin (nc i)) (j : Fin m),
      e i c j = innerProduct (a (finSigmaFinEquiv ⟨i, c⟩))
        (evalVector (2 ^ σ.k) (x j)) := by
    intro i c j
    have h := (hseg (finSigmaFinEquiv ⟨i, c⟩)).2 j
    rw [he'] at h
    exact (congrArg (fun p : (i : Fin n) × Fin (nc i) => e p.1 p.2 j)
      (Equiv.symm_apply_apply finSigmaFinEquiv ⟨i, c⟩)).symm.trans h
  -- **Step 3 (assemble).** One long polynomial per commitment from its segment
  -- witnesses; its chunk windows are the witnesses.
  refine ⟨fun i => assemblePoly (2 ^ σ.k) (nc i)
    (fun ci => if h : ci < nc i then a (finSigmaFinEquiv ⟨i, ⟨ci, h⟩⟩) else 0),
    fun i => ?_⟩
  have hwin : ∀ c : Fin (nc i),
      chunkCoeffs (2 ^ σ.k) (assemblePoly (2 ^ σ.k) (nc i)
          (fun ci => if h : ci < nc i then a (finSigmaFinEquiv ⟨i, ⟨ci, h⟩⟩) else 0))
        (c : ℕ) = a (finSigmaFinEquiv ⟨i, c⟩) := by
    intro c
    rw [chunkCoeffs_assemblePoly _ c.isLt, dif_pos c.isLt]
  have hdeg := assemblePoly_natDegree_lt (Nat.two_pow_pos σ.k) (hnc i)
    (fun ci => if h : ci < nc i then a (finSigmaFinEquiv ⟨i, ⟨ci, h⟩⟩) else 0)
  refine ⟨hdeg, fun c => ⟨ρ (finSigmaFinEquiv ⟨i, c⟩), ?_⟩, fun j => ?_⟩
  · rw [hwin c]
    exact hCseg i c
  -- **Step 4 (recombine).** The assembled polynomial evaluates as the chunk
  -- recombination of the claimed values.
  rw [eval_eq_sum_chunkPoly _ hdeg (x j), ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [chunkPoly_eval, hwin c, ← hEseg i c j]

end Kimchi.Commitment.IPA
