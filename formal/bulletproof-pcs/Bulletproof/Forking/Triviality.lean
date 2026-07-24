import Bulletproof.Soundness

/-!
# Is the Fiat–Shamir tree conclusion content-bearing?

`Bulletproof.FiatShamirTreeB σ P b v A` (`Bulletproof/Soundness.lean:124`) concludes
`A → ∃ ρ t, IpaAcceptV σ.g b (P - ρ • σ.h) v t`, and it is the conclusion the two declared
Fiat–Shamir axioms produce. Before instantiating a forking argument to *derive* it, we should
know what deriving it would buy — and there is reason to think the answer is "nothing", for
the same structural reason the package already concedes for `hbind`.

Two observations:

* the tree is **discarded**: `ipa_soundnessA` (`Soundness.lean:135`) destructures it and keeps
  only `∃ a ρ, openingRelationB σ P b v a ρ`; the node data `L, R, Lv, Rv`, the node challenges
  and the leaf scalars are unconstrained existentials;
* the deployed point group is a **1-dimensional `F`-vector space** (prime order, so `G ≅ F` as
  `F`-modules), which is exactly the fact the package already invokes to concede that `hbind`
  is information-theoretically false (`Soundness.lean:105-108`: "among `2 ^ k + 1` generators in
  a group of order `|F|` a nontrivial relation always exists").

Together these suggest `FiatShamirTreeB` is satisfiable *unconditionally* — never using `A` —
so the axioms would be tautologies rather than assumptions, and a forking derivation of them
would remove two axioms from the gate while establishing nothing. This module records that as
a checkable claim rather than an argument.

**This is parallel work.** Nothing here changes `FiatShamirTreeB`, the axioms, or any consumer;
it only states, alongside them, what they do and do not carry. The counterpart in
`zcash/ironwood` is `deployedIpaAcceptV_of_witness`
(`Zcash/Snark/Soundness/Deployed/Ipa.lean:104`), whose docstring calls it "the sanity gate: the
accept does not exclude honest executions" — the same construction, by honest folding with zero
blinding cross-terms and one triple of distinct nonzero challenges reused at every node.
-/

namespace Bulletproof.Forking

open Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Local bilinearity of `commitGen`

The `commitGen` bilinearity helpers proved in `Soundness/SingleOpening.lean`
(`commitGen_split`, the generator/coefficient additivity) are `private`, hence
invisible here. We reprove the exact instances this file needs, unfolding
`commitGen` to the underlying `∑ i, a i • g i`. -/

/-- Additivity of `commitGen` in the generators. -/
private theorem commitGen_add_gen {n : ℕ} (g g' : Fin n → G) (a : Fin n → F) :
    commitGen (g + g') a = commitGen g a + commitGen g' a := by
  simp only [commitGen, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- `commitGen` pulls a scalar out of the generators. -/
private theorem commitGen_smul_gen {n : ℕ} (s : F) (g : Fin n → G) (a : Fin n → F) :
    commitGen (s • g) a = s • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm (a i) s (g i)

/-- Additivity of `commitGen` in the coefficients. -/
private theorem commitGen_add_coeff {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a + a') = commitGen g a + commitGen g a' := by
  simp only [commitGen, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- `commitGen` pulls a scalar out of the coefficients. -/
private theorem commitGen_smul_coeff {n : ℕ} (s : F) (g : Fin n → G) (a : Fin n → F) :
    commitGen g (s • a) = s • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- A length-`2^{d+1}` commitment splits over the two halves (local copy of the
`private` `commitGen_split`). -/
private theorem commitGen_split' {d : ℕ} (g : Fin (2 ^ (d + 1)) → G)
    (a : Fin (2 ^ (d + 1)) → F) :
    commitGen g a = commitGen (loHalf g) (loHalf a) + commitGen (hiHalf g) (hiHalf a) := by
  have e : 2 ^ d + 2 ^ d = 2 ^ (d + 1) := by rw [pow_succ]; ring
  let φ : Fin (2 ^ d) ⊕ Fin (2 ^ d) ≃ Fin (2 ^ (d + 1)) := finSumFinEquiv.trans (finCongr e)
  simp only [commitGen]
  rw [← φ.sum_comp (fun j => a j • g j), Fintype.sum_sum_type]
  congr 1

/-- **One-round fold identity.** Committing the honest sub-witness
`loHalf a + u⁻¹ • hiHalf a` against the folded generators `foldHalves g u`
recovers the parent commitment plus the two blinded cross-terms. Because our
`foldHalves` scales the *high* half by `u` (chapter Rmk on the fold convention),
the sub-witness carries `u⁻¹` on its high half; `u ≠ 0` is exactly what makes the
`u • u⁻¹` on the pure-high term collapse. -/
private theorem commitGen_fold_identity {d : ℕ}
    (g : Fin (2 ^ (d + 1)) → G) (a : Fin (2 ^ (d + 1)) → F) (u : F) (hu : u ≠ 0) :
    commitGen (foldHalves g u) (loHalf a + u⁻¹ • hiHalf a) =
      commitGen g a + u⁻¹ • commitGen (loHalf g) (hiHalf a)
        + u • commitGen (hiHalf g) (loHalf a) := by
  rw [commitGen_split' g a]
  simp only [foldHalves, commitGen_add_gen, commitGen_smul_gen, commitGen_add_coeff,
    commitGen_smul_coeff, smul_add, smul_smul, inv_mul_cancel₀ hu, one_smul]
  abel

/-- **Completeness of the accept predicate (the sanity gate).** From any opening witness `a`,
honest folding builds an accepting tree: the accept does not exclude honest executions. One
triple of distinct nonzero challenges is reused at every node, and the blinding cross-terms are
zero.

Independently valuable — the package proves soundness of `IpaAcceptV`
(`ipaRelation_of_acceptV`) but never its converse, so nothing currently rules out the predicate
being unsatisfiable. Modelled on ironwood's `deployedIpaAcceptV_of_witness`. -/
theorem ipaAcceptV_of_witness (u₁ u₂ u₃ : F)
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0) :
    ∀ {d : ℕ} (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F) (a : Fin (2 ^ d) → F),
      ∃ t : IpaTreeV F G d, IpaAcceptV g b (commitGen g a) (commitGen b a) t := by
  intro d
  induction d with
  | zero =>
    intro g b a
    haveI : Subsingleton (Fin (2 ^ 0)) := by rw [pow_zero]; infer_instance
    refine ⟨.leaf (a 0), ?_, ?_⟩
    · show commitGen g a = commitGen g (fun _ => a 0)
      congr 1; funext i; rw [Subsingleton.elim i 0]
    · show commitGen b a = commitGen b (fun _ => a 0)
      congr 1; funext i; rw [Subsingleton.elim i 0]
  | succ d ih =>
    intro g b a
    obtain ⟨t₁, ht₁⟩ := ih (foldHalves g u₁) (foldHalves b u₁) (loHalf a + u₁⁻¹ • hiHalf a)
    obtain ⟨t₂, ht₂⟩ := ih (foldHalves g u₂) (foldHalves b u₂) (loHalf a + u₂⁻¹ • hiHalf a)
    obtain ⟨t₃, ht₃⟩ := ih (foldHalves g u₃) (foldHalves b u₃) (loHalf a + u₃⁻¹ • hiHalf a)
    rw [commitGen_fold_identity g a u₁ hu₁, commitGen_fold_identity b a u₁ hu₁] at ht₁
    rw [commitGen_fold_identity g a u₂ hu₂, commitGen_fold_identity b a u₂ hu₂] at ht₂
    rw [commitGen_fold_identity g a u₃ hu₃, commitGen_fold_identity b a u₃ hu₃] at ht₃
    exact ⟨.node (commitGen (loHalf g) (hiHalf a)) (commitGen (hiHalf g) (loHalf a))
        (commitGen (loHalf b) (hiHalf a)) (commitGen (hiHalf b) (loHalf a))
        u₁ u₂ u₃ t₁ t₂ t₃,
      h12, h13, h23, hu₁, hu₂, hu₃, ht₁, ht₂, ht₃⟩

/-- **The opening relation is underdetermined in a 1-dimensional group.** If every point is a
multiple of a single generator — the deployed Pasta situation, a cyclic group of prime order
`|F|` — then the two equations of `openingRelationB` in `2 ^ k + 1` unknowns always have a
solution, for *any* claimed commitment `P` and *any* claimed value `v`.

This is the same counting the package already uses to concede `hbind` is false
(`Soundness.lean:105-108`); here it runs in the opposite direction, making a conclusion free
rather than a hypothesis unsatisfiable. -/
theorem openingRelation_solvable (σ : SRS G) (P : G) (b : Fin (2 ^ σ.k) → F) (v : F)
    (H : G) (hspan : ∀ x : G, ∃ s : F, x = s • H)
    (hh : ∃ s : F, σ.h = s • H ∧ s ≠ 0)
    (hb : ∃ i, b i ≠ 0) :
    ∃ (a : Fin (2 ^ σ.k) → F) (ρ : F),
      commitGen σ.g a + ρ • σ.h = P ∧ commitGen b a = v := by
  obtain ⟨i₀, hi₀⟩ := hb
  obtain ⟨s₀, hs₀, hs₀ne⟩ := hh
  set a : Fin (2 ^ σ.k) → F := fun i => if i = i₀ then v / b i₀ else 0 with ha
  obtain ⟨t, ht⟩ := hspan (P - commitGen σ.g a)
  refine ⟨a, t / s₀, ?_, ?_⟩
  · rw [hs₀, smul_smul, div_mul_cancel₀ t hs₀ne, ← ht]; abel
  · rw [commitGen, Finset.sum_eq_single i₀]
    · rw [ha]; simp only [if_pos, smul_eq_mul]; rw [div_mul_cancel₀ v hi₀]
    · intro i _ hne; rw [ha]; simp only [if_neg hne, zero_smul]
    · intro h; exact absurd (Finset.mem_univ i₀) h

/-- **The tree conclusion carries no content at the deployed instantiation.** Under
1-dimensionality, `FiatShamirTreeB` holds for every claim — with the acceptance hypothesis `A`
never used. So deriving it by a forking argument would establish nothing that is not already
true by linear algebra, and the two declared Fiat–Shamir axioms are tautologies at these
parameters rather than assumptions.

The honest consequence: a content-bearing replacement must be AGM-relative or data-valued (as
ironwood's is), not a `Prop`-level existential over this group. -/
theorem fiatShamirTreeB_trivial (σ : SRS G) (P : G) (b : Fin (2 ^ σ.k) → F) (v : F) (A : Prop)
    (u₁ u₂ u₃ : F) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (H : G) (hspan : ∀ x : G, ∃ s : F, x = s • H)
    (hh : ∃ s : F, σ.h = s • H ∧ s ≠ 0)
    (hb : ∃ i, b i ≠ 0) :
    FiatShamirTreeB σ P b v A := by
  intro _
  obtain ⟨a, ρ, hP, hv⟩ := openingRelation_solvable σ P b v H hspan hh hb
  obtain ⟨t, ht⟩ := ipaAcceptV_of_witness u₁ u₂ u₃ h12 h13 h23 hu₁ hu₂ hu₃ σ.g b a
  refine ⟨ρ, t, ?_⟩
  have hPg : commitGen σ.g a = P - ρ • σ.h := by
    rw [← hP]; abel
  rw [← hPg, ← hv]
  exact ht

end Bulletproof.Forking
