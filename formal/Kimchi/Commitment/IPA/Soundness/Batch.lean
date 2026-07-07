import Mathlib
import Kimchi.Commitment.IPA.Batch
import Kimchi.Commitment.IPA.Soundness
import Kimchi.Commitment.IPA.Soundness.Vandermonde

/-!
# Knowledge soundness of the batched kimchi IPA opening

The headline of the batch development (`batch_soundness`): correct combined openings
at enough distinct `(polyscale ξ, evalscale r)` pairs imply that every individual
claimed evaluation is the true evaluation of the committed polynomial. Built on the
single-opening IPA stack (`Basic`/`Verify`/`Soundness`/`Soundness/{Linear,Tree,Binding}`)
and the batch definitions (`Batch`, `Soundness/Vandermonde`); nothing there is
redefined.

The extraction is the standard multi-poly/multi-point PCS reduction, specialized to
the kimchi IPA relation:

1. generalize the single-opening extractor to an arbitrary eval vector
   (`ipa_soundnessB`);
2. separate commitments by a Vandermonde combination in the polyscale
   (`perCommitment_separation`), using commitment linearity (`commit_sum_smul`);
3. use binding to force one witness per commitment, then a second Vandermonde in the
   evalscale to pin every individual evaluation (`batch_soundness`).

## Scope: what is proved, and what is assumed

What is *proved* is the algebraic core: from accepting transcript trees, the
special-soundness extraction of the single-opening stack, the two Vandermonde
separations, and binding-uniqueness together yield per-commitment witnesses whose
claimed evaluations are genuine. Two hypotheses are *assumed*, and they carry the
cryptographic weight:

* **`BatchFiatShamir`** — the grid analogue of `FiatShamirTree`: an accepting
  verifier run yields a de-blinded accepting transcript tree. This is the entire
  rewinding / Fiat–Shamir extraction step, taken as a hypothesis rather than proved.
  It also carries the correspondence between the verifier's scalar acceptance
  equation (through `combinedB`, `bPoly`, `sg`) and the tree over
  `combinedEvalVector`: that equation is never exercised by a proof here —
  `ipa_soundnessB` holds for *any* `b0`, since `b0` occurs only in the antecedent.
  The witness opens against whatever eval vector the hypothesis is instantiated at
  (here `combinedEvalVector`); the tie to the deployed verifier rests on this
  hypothesis plus the transcription of the `Batch` combiners, not on a derivation.

* **Binding** (`hbind` / no nontrivial discrete-log relation) — the idealization of
  computational DL-relation hardness. It is *information-theoretically false* for a
  real single-curve SRS: among `2 ^ k + 1` generators in a group of order `|F|`
  there is always a nontrivial relation, so at real parameters the hypothesis is
  unsatisfiable and the theorem is vacuous there. It is meaningful only as the
  computational assumption, discharged outside this development.

So this is the machine-checked algebraic skeleton of batch knowledge soundness, not
an unconditional soundness proof of the deployed verifier: a clean axiom closure
certifies the derivation is `sorry`-free, not that these hypotheses hold. Closing the
gap would take formalizing the rewinding (to discharge `BatchFiatShamir`) and a
computational layer (to discharge binding).
-/

namespace Kimchi.Commitment.IPA

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Per-commitment separation -/

/-- Generalized Fiat–Shamir tree hypothesis: `FiatShamirTree` with the eval vector
abstracted to an arbitrary `b : Fin (2 ^ σ.k) → F`. An accepting run yields a
de-blinded accepting tree over `b`,
`accepts → ∃ (ρ : F) (t : IpaTreeV F G σ.k), IpaAcceptV σ.g b (P - ρ • σ.h) v t`.

The original is the specialization
`FiatShamirTree σ P x v accepts = FiatShamirTreeB σ P (evalVector (2 ^ σ.k) x) v accepts`. -/
def FiatShamirTreeB (σ : SRS G) (P : G) (b : Fin (2 ^ σ.k) → F) (v : F)
    (accepts : Prop) : Prop :=
  accepts → ∃ (ρ : F) (t : IpaTreeV F G σ.k),
    IpaAcceptV σ.g b (P - ρ • σ.h) v t

/-- **Generalized single-opening soundness.** The verbatim generalization of
`ipa_soundness` to an arbitrary eval vector `b`: under
`FiatShamirTreeB σ P b v (VerifierAcceptsAt σ proof P b0 v c u)`, an accepting run
yields an opening witness for `openingRelationB`. -/
theorem ipa_soundnessB (σ : SRS G) (proof : OpeningProof F G σ.k) (P : G)
    (b : Fin (2 ^ σ.k) → F) (b0 v c : F) (u : Fin σ.k → F)
    (hFS : FiatShamirTreeB σ P b v (VerifierAcceptsAt σ proof P b0 v c u))
    (hacc : VerifierAcceptsAt σ proof P b0 v c u) :
    ∃ (a : Fin (2 ^ σ.k) → F) (ρ : F), openingRelationB σ P b v a ρ := by
  obtain ⟨ρ, t, ht⟩ := hFS hacc
  obtain ⟨a, hP, hv⟩ := ipaRelation_of_acceptV σ b (P - ρ • σ.h) v t ht
  refine ⟨a, ρ, ?_, hv⟩
  show commitGen σ.g a + ρ • σ.h = P
  rw [hP]
  abel

/-- **Acceptance-generalized single-opening soundness.** `ipa_soundnessB` with the
acceptance proposition fully abstract: the extraction consumes only the modus ponens of
the Fiat-Shamir hypothesis against acceptance, never the shape of acceptance itself. This
is the form the deployed verifier's acceptance (`Ipa.verify … = true`) plugs into. -/
theorem ipa_soundnessA (σ : SRS G) (P : G) (b : Fin (2 ^ σ.k) → F) (v : F) {A : Prop}
    (hFS : FiatShamirTreeB σ P b v A) (hacc : A) :
    ∃ (a : Fin (2 ^ σ.k) → F) (ρ : F), openingRelationB σ P b v a ρ := by
  obtain ⟨ρ, t, ht⟩ := hFS hacc
  obtain ⟨a, hP, hv⟩ := ipaRelation_of_acceptV σ b (P - ρ • σ.h) v t ht
  refine ⟨a, ρ, ?_, hv⟩
  show commitGen σ.g a + ρ • σ.h = P
  rw [hP]
  abel

/-- **Generator-commitment linearity over finite combinations.** Pushes a
`•`-combination of witnesses through `commitGen`. Pure glue for `commit_sum_smul`. -/
private theorem commitGen_sum_smul {n N : ℕ} (g : Fin N → G) (l : Fin n → F)
    (a : Fin n → (Fin N → F)) :
    commitGen g (∑ s, l s • a s) = ∑ s, l s • commitGen g (a s) := by
  simp only [commitGen, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul,
    mul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]

/-- **Commitment linearity over finite combinations.** For coefficients
`l : Fin n → F`, witnesses `a : Fin n → (Fin (2 ^ σ.k) → F)`, and blinders
`ρ : Fin n → F`,
`commit σ (∑ s, l s • a s) (∑ s, l s * ρ s) = ∑ s, l s • commit σ (a s) (ρ s)`. -/
theorem commit_sum_smul (σ : SRS G) {n : ℕ} (l : Fin n → F)
    (a : Fin n → (Fin (2 ^ σ.k) → F)) (ρ : Fin n → F) :
    commit σ (∑ s, l s • a s) (∑ s, l s * ρ s)
      = ∑ s, l s • commit σ (a s) (ρ s) := by
  simp only [commit, commitGen_sum_smul, smul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_smul]

/-- **Inner-product linearity over finite combinations (first slot).** Pushes a
`•`-combination of witnesses through `innerProduct`. Pure glue for
`perCommitment_separation`. -/
private theorem innerProduct_sum_smul {n N : ℕ} (l : Fin n → F)
    (a : Fin n → (Fin N → F)) (b : Fin N → F) :
    innerProduct (∑ s, l s • a s) b = ∑ s, l s * innerProduct (a s) b := by
  simp only [innerProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    mul_assoc, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- **Per-commitment separation.** Fix an evalscale `r` and eval vector
`b := combinedEvalVector (2 ^ σ.k) r x`. If `ξ` is injective and for each `s` there
is an opening witness `(a s, ρ s)` of the combined relation at polyscale `ξ s`, then
for every commitment `d` there is a witness `(A, P)` opening `C d` to
`∑ j, e d j * r ^ j`. -/
theorem perCommitment_separation (σ : SRS G) {n m : ℕ}
    (ξ : Fin n → F) (hξ : Function.Injective ξ) (r : F) (x : Fin m → F)
    (C : Fin n → G) (e : Fin n → Fin m → F)
    (a : Fin n → (Fin (2 ^ σ.k) → F)) (ρ : Fin n → F)
    (hcommit : ∀ s, commit σ (a s) (ρ s) = combinedCommitment (ξ s) C)
    (hvalue : ∀ s, innerProduct (a s) (combinedEvalVector (2 ^ σ.k) r x)
      = combinedInnerProduct (ξ s) r e)
    (d : Fin n) : ∃ (A : Fin (2 ^ σ.k) → F) (P : F),
      commit σ A P = C d
        ∧ innerProduct A (combinedEvalVector (2 ^ σ.k) r x)
            = ∑ j, e d j * r ^ (j : ℕ) := by
  classical
  obtain ⟨l, hl⟩ := vandermondeN ξ hξ d
  refine ⟨∑ s, l s • a s, ∑ s, l s * ρ s, ?_, ?_⟩
  · -- Commitment: Vandermonde combination collapses to C d.
    rw [commit_sum_smul]
    simp only [hcommit, combinedCommitment, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hl]
    simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · -- Value: linearity + Vandermonde in ξ.
    -- Keep the inner `∑ j` opaque (as `f`) so the ξ-distribution mirrors the
    -- commitment branch exactly.
    have key : ∀ f : Fin n → F,
        (∑ s, l s * ∑ i : Fin n, ξ s ^ (i : ℕ) * f i)
          = ∑ i : Fin n, (∑ s, l s * ξ s ^ (i : ℕ)) * f i := by
      intro f
      simp only [Finset.mul_sum, ← mul_assoc, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [innerProduct_sum_smul]
    simp only [hvalue, combinedInnerProduct]
    rw [key]
    simp only [hl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ## Per-point separation and the headline -/

/-- Batch Fiat–Shamir hypothesis: the single new trust assumption, the grid analogue
of `FiatShamirTree`. Given a grid of proofs, final challenges, and IPA challenge
vectors, an accepting batched run at each grid point `(s, t)` (polyscale `ξ s`,
evalscale `r t`) yields a de-blinded accepting tree over the combined eval vector. -/
def BatchFiatShamir (σ : SRS G) {n m : ℕ} (ξ : Fin n → F) (r : Fin m → F)
    (C : Fin n → G) (x : Fin m → F) (e : Fin n → Fin m → F)
    (proofs : Fin n → Fin m → OpeningProof F G σ.k)
    (c : Fin n → Fin m → F) (u : Fin n → Fin m → (Fin σ.k → F)) : Prop :=
  ∀ (s : Fin n) (t : Fin m),
    FiatShamirTreeB σ (combinedCommitment (ξ s) C)
      (combinedEvalVector (2 ^ σ.k) (r t) x)
      (combinedInnerProduct (ξ s) (r t) e)
      (BatchAccepts σ (proofs s t) (ξ s) (r t) (c s t) (u s t) C x e)

/-- **Batched opening soundness.** Let `ξ` and `r` be injective (pairwise-distinct
polyscales and evalscales). Under the batch Fiat–Shamir hypothesis, the no-DL-relation
binding hypothesis, and batched acceptance at every grid point, every individual
claimed evaluation is the true evaluation of the committed polynomial:
`∃ a ρ, ∀ i, commit σ (a i) (ρ i) = C i ∧ ∀ j, e i j = ⟨a i, evalVector N (x j)⟩`. -/
theorem batch_soundness (σ : SRS G) {n m : ℕ}
    (ξ : Fin n → F) (hξ : Function.Injective ξ)
    (r : Fin m → F) (hr : Function.Injective r) (hm : 0 < m)
    (C : Fin n → G) (x : Fin m → F) (e : Fin n → Fin m → F)
    (proofs : Fin n → Fin m → OpeningProof F G σ.k)
    (c : Fin n → Fin m → F) (u : Fin n → Fin m → (Fin σ.k → F))
    (hFS : BatchFiatShamir σ ξ r C x e proofs c u)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F),
      DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (hacc : ∀ s t, BatchAccepts σ (proofs s t) (ξ s) (r t) (c s t) (u s t) C x e) :
    ∃ (a : Fin n → Fin (2 ^ σ.k) → F) (ρ : Fin n → F), ∀ i,
      commit σ (a i) (ρ i) = C i
        ∧ ∀ j, e i j = innerProduct (a i) (evalVector (2 ^ σ.k) (x j)) := by
  classical
  -- **Step 1 (grid witnesses).** Extract a per-grid opening `(a1 s t, ρ1 s t)`.
  have h1 : ∀ (s : Fin n) (t : Fin m), ∃ (aw : Fin (2 ^ σ.k) → F) (ρw : F),
      commit σ aw ρw = combinedCommitment (ξ s) C
        ∧ combinedInnerProduct (ξ s) (r t) e
            = innerProduct aw (combinedEvalVector (2 ^ σ.k) (r t) x) := by
    intro s t
    exact ipa_soundnessB σ (proofs s t) (combinedCommitment (ξ s) C)
      (combinedEvalVector (2 ^ σ.k) (r t) x) (combinedB (u s t) (r t) x)
      (combinedInnerProduct (ξ s) (r t) e) (c s t) (u s t) (hFS s t) (hacc s t)
  choose a1 ρ1 hcommit1 hvalue1 using h1
  -- **Step 2 (per commitment).** Vandermonde in `ξ` separates each `C i`.
  have h2 : ∀ (i : Fin n) (t : Fin m), ∃ (A : Fin (2 ^ σ.k) → F) (P : F),
      commit σ A P = C i
        ∧ innerProduct A (combinedEvalVector (2 ^ σ.k) (r t) x)
            = ∑ j, e i j * (r t) ^ (j : ℕ) := by
    intro i t
    exact perCommitment_separation σ ξ hξ (r t) x C e (fun s => a1 s t) (fun s => ρ1 s t)
      (fun s => hcommit1 s t) (fun s => (hvalue1 s t).symm) i
  choose A2 P2 hAcommit hAvalue using h2
  -- Rewrite the combined-eval inner product into per-point evaluations (∗).
  have hstar : ∀ (i : Fin n) (t : Fin m),
      (∑ j : Fin m, (r t) ^ (j : ℕ) * innerProduct (A2 i t) (evalVector (2 ^ σ.k) (x j)))
        = ∑ j, e i j * (r t) ^ (j : ℕ) := by
    intro i t
    rw [← innerProduct_combinedEvalVector]
    exact hAvalue i t
  -- **Step 3 (binding).** One witness per commitment, at the base evalscale `t₀`.
  have hbd : CommitmentBinding (F := F) σ := (commitmentBinding_iff_no_relation σ).mpr hbind
  set t₀ : Fin m := ⟨0, hm⟩ with ht₀
  have hAeq : ∀ (i : Fin n) (t : Fin m), A2 i t = A2 i t₀ := by
    intro i t
    have hcol : commit σ (A2 i t) (P2 i t) = commit σ (A2 i t₀) (P2 i t₀) := by
      rw [hAcommit i t, hAcommit i t₀]
    have hpair := @hbd (A2 i t, P2 i t) (A2 i t₀, P2 i t₀) hcol
    exact congrArg Prod.fst hpair
  -- **Step 4 (per point).** Vandermonde in `r` pins every evaluation.
  refine ⟨fun i => A2 i t₀, fun i => P2 i t₀, ?_⟩
  intro i
  refine ⟨hAcommit i t₀, ?_⟩
  intro j0
  -- The vanishing sums `∀ t, ∑ j, (w i j - e i j) * (r t)^j = 0`.
  have hvan : ∀ t : Fin m,
      (∑ j : Fin m,
        (innerProduct (A2 i t₀) (evalVector (2 ^ σ.k) (x j)) - e i j)
          * (r t) ^ (j : ℕ)) = 0 := by
    intro t
    have h := hstar i t
    rw [hAeq i t] at h
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib, sub_eq_zero, ← h]
    exact Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨L, hL⟩ := vandermondeN r hr j0
  -- Reorder + factor the double sum, treating the coefficient function abstractly.
  have key3 : ∀ g : Fin m → F,
      (∑ t, L t * ∑ j : Fin m, g j * (r t) ^ (j : ℕ))
        = ∑ j : Fin m, g j * ∑ t, L t * (r t) ^ (j : ℕ) := by
    intro g
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => by ring
  have hzero : (∑ t, L t * ∑ j : Fin m,
      (innerProduct (A2 i t₀) (evalVector (2 ^ σ.k) (x j)) - e i j)
        * (r t) ^ (j : ℕ)) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    rw [hvan t, mul_zero]
  rw [key3 (fun j => innerProduct (A2 i t₀) (evalVector (2 ^ σ.k) (x j)) - e i j)] at hzero
  simp only [hL, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hzero
  exact (sub_eq_zero.mp hzero).symm


/-- **Acceptance-generalized batched opening soundness.** `batch_soundness` with the
grid acceptance abstracted to an arbitrary family `A`: the proof consumes acceptance only
through the modus ponens of the Fiat-Shamir hypothesis (`ipa_soundnessA`), so no
per-grid-point proof or challenge data appears. This is the form the deployed verifier's
acceptance (`Ipa.verify … = true`, whose challenges are sponge-derived rather than
carried) plugs into. -/
theorem batch_soundnessA (σ : SRS G) {n m : ℕ}
    (ξ : Fin n → F) (hξ : Function.Injective ξ)
    (r : Fin m → F) (hr : Function.Injective r) (hm : 0 < m)
    (C : Fin n → G) (x : Fin m → F) (e : Fin n → Fin m → F)
    (A : Fin n → Fin m → Prop)
    (hFS : ∀ s t, FiatShamirTreeB σ (combinedCommitment (ξ s) C)
      (combinedEvalVector (2 ^ σ.k) (r t) x) (combinedInnerProduct (ξ s) (r t) e) (A s t))
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F),
      DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (hacc : ∀ s t, A s t) :
    ∃ (a : Fin n → Fin (2 ^ σ.k) → F) (ρ : Fin n → F), ∀ i,
      commit σ (a i) (ρ i) = C i
        ∧ ∀ j, e i j = innerProduct (a i) (evalVector (2 ^ σ.k) (x j)) := by
  classical
  -- **Step 1 (grid witnesses).** Extract a per-grid opening from acceptance alone.
  have h1 : ∀ (s : Fin n) (t : Fin m), ∃ (aw : Fin (2 ^ σ.k) → F) (ρw : F),
      commit σ aw ρw = combinedCommitment (ξ s) C
        ∧ combinedInnerProduct (ξ s) (r t) e
            = innerProduct aw (combinedEvalVector (2 ^ σ.k) (r t) x) := by
    intro s t
    exact ipa_soundnessA σ (combinedCommitment (ξ s) C)
      (combinedEvalVector (2 ^ σ.k) (r t) x) (combinedInnerProduct (ξ s) (r t) e)
      (hFS s t) (hacc s t)
  choose a1 ρ1 hcommit1 hvalue1 using h1
  -- **Step 2 (per commitment).** Vandermonde in `ξ` separates each `C i`.
  have h2 : ∀ (i : Fin n) (t : Fin m), ∃ (A : Fin (2 ^ σ.k) → F) (P : F),
      commit σ A P = C i
        ∧ innerProduct A (combinedEvalVector (2 ^ σ.k) (r t) x)
            = ∑ j, e i j * (r t) ^ (j : ℕ) := by
    intro i t
    exact perCommitment_separation σ ξ hξ (r t) x C e (fun s => a1 s t) (fun s => ρ1 s t)
      (fun s => hcommit1 s t) (fun s => (hvalue1 s t).symm) i
  choose A2 P2 hAcommit hAvalue using h2
  -- Rewrite the combined-eval inner product into per-point evaluations (∗).
  have hstar : ∀ (i : Fin n) (t : Fin m),
      (∑ j : Fin m, (r t) ^ (j : ℕ) * innerProduct (A2 i t) (evalVector (2 ^ σ.k) (x j)))
        = ∑ j, e i j * (r t) ^ (j : ℕ) := by
    intro i t
    rw [← innerProduct_combinedEvalVector]
    exact hAvalue i t
  -- **Step 3 (binding).** One witness per commitment, at the base evalscale `t₀`.
  have hbd : CommitmentBinding (F := F) σ := (commitmentBinding_iff_no_relation σ).mpr hbind
  set t₀ : Fin m := ⟨0, hm⟩ with ht₀
  have hAeq : ∀ (i : Fin n) (t : Fin m), A2 i t = A2 i t₀ := by
    intro i t
    have hcol : commit σ (A2 i t) (P2 i t) = commit σ (A2 i t₀) (P2 i t₀) := by
      rw [hAcommit i t, hAcommit i t₀]
    have hpair := @hbd (A2 i t, P2 i t) (A2 i t₀, P2 i t₀) hcol
    exact congrArg Prod.fst hpair
  -- **Step 4 (per point).** Vandermonde in `r` pins every evaluation.
  refine ⟨fun i => A2 i t₀, fun i => P2 i t₀, ?_⟩
  intro i
  refine ⟨hAcommit i t₀, ?_⟩
  intro j0
  have hvan : ∀ t : Fin m,
      (∑ j : Fin m,
        (innerProduct (A2 i t₀) (evalVector (2 ^ σ.k) (x j)) - e i j)
          * (r t) ^ (j : ℕ)) = 0 := by
    intro t
    have h := hstar i t
    rw [hAeq i t] at h
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib, sub_eq_zero, ← h]
    exact Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨L, hL⟩ := vandermondeN r hr j0
  have key3 : ∀ g : Fin m → F,
      (∑ t, L t * ∑ j : Fin m, g j * (r t) ^ (j : ℕ))
        = ∑ j : Fin m, g j * ∑ t, L t * (r t) ^ (j : ℕ) := by
    intro g
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => by ring
  have hzero : (∑ t, L t * ∑ j : Fin m,
      (innerProduct (A2 i t₀) (evalVector (2 ^ σ.k) (x j)) - e i j)
        * (r t) ^ (j : ℕ)) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    rw [hvan t, mul_zero]
  rw [key3 (fun j => innerProduct (A2 i t₀) (evalVector (2 ^ σ.k) (x j)) - e i j)] at hzero
  simp only [hL, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hzero
  exact (sub_eq_zero.mp hzero).symm

end Kimchi.Commitment.IPA
