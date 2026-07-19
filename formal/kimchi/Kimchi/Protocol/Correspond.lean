import Kimchi.Index.Aggregate
import Bulletproof.Protocol

/-!
# The verifier key ↔ index correspondence

The seam the implementations leave implicit: the Rust verifier receives a
`VerifierIndex` produced by the same pipeline that holds the gates, so "the key
commits the circuit you think it does" is true by code path and never stated. Our
soundness conclusion names a specific circuit model (`Satisfies idx …`), so the fact
becomes a proposition: `VKCorresponds` — the key's committed columns are commitments
of the Index's own interpolants. It is discharged two ways:

* **constructively**: `indexerOf` is the Lean-side indexer — the commitments of
  `idx`'s interpolants — and `VKCorresponds σ (indexerOf σ idx) idx` holds by
  definition (`vkCorresponds_indexerOf`), mirroring how the Rust pipeline discharges
  the fact by construction;
* **by value**: for the production key, `commitPoly_columnPoly` reduces each
  commitment to the value-MSM of the Lagrange-basis commitments, which
  `scripts/check_vk_correspond.lean` checks numerically against the dumped VK
  (`fixtures/kimchi_proof_vesta.json`) using the production-validated column values
  (`fixtures/index_vesta.json`).

Stated abstractly (an `F`-module `G`, as the whole IPA soundness stack is): the wire
connection to `KimchiVK`'s concrete points is part of the milestone-4 composition,
through the same reflection layer that carries `Ipa.verify` to `batch_soundness`.
-/

open Bulletproof

namespace Kimchi.Protocol

open Polynomial Kimchi.Quotient Kimchi.Index Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G] {n : ℕ}

/-- Commitment of a polynomial: the generator MSM of its low coefficient vector
(production's unblinded `commit_non_hiding` of a verifier-key column). Coefficients
at or above `2^σ.k` are not read — the keys this file speaks about hold interpolants
of degree `< n ≤ 2^σ.k`. -/
noncomputable def commitPoly (σ : SRS G) (p : Polynomial F) : G :=
  commitGen σ.g (fun i => p.coeff i)

/-- Interpolation is linear in the column: `columnPoly v = ∑ⱼ vⱼ • Lⱼ` with
`Lⱼ = columnPoly (rowIndicator j)` the Lagrange basis. Degree-`< n` agreement on the
domain: at node `i` the left side reads `vᵢ` and the right collapses to the `j = i`
term. -/
theorem columnPoly_eq_sum_indicator {ω : F} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (v : Fin n → F) :
    columnPoly ω v
      = ∑ j : Fin n, v j • columnPoly ω (Permutation.rowIndicator j) := by
  have hd2 : (∑ j : Fin n, v j • columnPoly ω (Permutation.rowIndicator j)).degree
      < n := by
    apply lt_of_le_of_lt (degree_sum_le _ _)
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe (n : ℕ))]
    exact fun j _ => lt_of_le_of_lt (degree_smul_le _ _) (degree_columnPoly_lt hω _)
  refine eq_of_eval_eq_on_domain hω hn (degree_columnPoly_lt hω _) hd2 ?_
  intro i hi
  rw [show ((ω : F) ^ i) = ω ^ ((⟨i, hi⟩ : Fin n) : ℕ) from rfl, eval_columnPoly hω,
    eval_finsetSum]
  rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
  · rw [eval_smul, eval_columnPoly hω, Permutation.rowIndicator, if_pos rfl,
      smul_eq_mul, mul_one]
  · intro j _ hj
    rw [eval_smul, eval_columnPoly hω, Permutation.rowIndicator,
      if_neg (fun hEq => hj hEq.symm), smul_eq_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Committing an interpolant is the value-MSM of the basis commitments**:
`commitPoly (columnPoly v) = ∑ⱼ vⱼ • commitPoly Lⱼ`. This is what makes
`VKCorresponds` checkable by value — the fixture script MSMs the production column
values against the production Lagrange-basis commitments. -/
theorem commitPoly_columnPoly (σ : SRS G) {ω : F} (hω : IsPrimitiveRoot ω n)
    (hn : 0 < n) (v : Fin n → F) :
    commitPoly σ (columnPoly ω v)
      = ∑ j : Fin n, v j
          • commitPoly σ (columnPoly ω (Permutation.rowIndicator j)) := by
  rw [commitPoly, columnPoly_eq_sum_indicator hω hn v]
  unfold commitPoly commitGen
  simp only [finsetSum_coeff, coeff_smul, smul_eq_mul, Finset.sum_smul, mul_smul,
    Finset.smul_sum]
  exact Finset.sum_comm

/-- The committed-column view of a verifier key, abstractly: one commitment per
Index column family the verifier reads — the 7 permutation columns, the 15
coefficient columns, and the six gate selectors (the zero gate has none). -/
structure IndexComms (G : Type*) where
  sigma : Fin 7 → G
  coefficients : Fin 15 → G
  generic : G
  poseidon : G
  completeAdd : G
  varBaseMul : G
  endoMul : G
  endoScalar : G

/-- The fixed-blinder commitment: `commitPoly + h`. Production wraps exactly the six
selector commitments (and the lookup tables) in `mask_fixed` — `mask_custom` with the
blinder `1`, i.e. one unit of the blinding base — while the σ and coefficient columns
are committed unblinded (`verifier_index.rs:173,225–263`; the asymmetry is
production's, see its own `TODO: Switch to commit_evaluations for all index polys`).
Caught by value: the fixture MSM check fails on the selectors without the `+ σ.h`. -/
noncomputable def commitPolyMasked (σ : SRS G) (p : Polynomial F) : G :=
  commitPoly σ p + σ.h

/-- **The Lean-side indexer**: the verifier key an honest setup produces from the
Index — the commitments of its own interpolants, the selectors carrying production's
fixed blinder. -/
noncomputable def indexerOf (σ : SRS G) (idx : Index F n) : IndexComms G where
  sigma i := commitPoly σ (idx.sigmaPoly i)
  coefficients c := commitPoly σ (idx.coeffPoly c)
  generic := commitPolyMasked σ (idx.selectorPoly .generic)
  poseidon := commitPolyMasked σ (idx.selectorPoly .poseidon)
  completeAdd := commitPolyMasked σ (idx.selectorPoly .completeAdd)
  varBaseMul := commitPolyMasked σ (idx.selectorPoly .varBaseMul)
  endoMul := commitPolyMasked σ (idx.selectorPoly .endoMul)
  endoScalar := commitPolyMasked σ (idx.selectorPoly .endoScalar)

/-- **The key ↔ index correspondence**: the committed columns are the Index's own —
the key is in the image of the indexer. The soundness composition consumes this as a
hypothesis; honest keys discharge it by `vkCorresponds_indexerOf`, and the production
key by the fixture MSM check. -/
def VKCorresponds (σ : SRS G) (comms : IndexComms G) (idx : Index F n) : Prop :=
  comms = indexerOf σ idx

/-- Honest keys correspond by construction — the constructive discharge. -/
theorem vkCorresponds_indexerOf (σ : SRS G) (idx : Index F n) :
    VKCorresponds σ (indexerOf σ idx) idx := rfl

end Kimchi.Protocol
