import Mathlib
import Bulletproof.Soundness.SingleOpening

/-!
# Batched and chunked soundness of the abstract kimchi IPA

Knowledge soundness of the openings the kimchi verifier actually runs — many polynomials,
two points, per-polynomial chunk counts — over the single-opening soundness of
`Bulletproof.Soundness.SingleOpening`. The `n`-point Vandermonde dual basis
(§ Vandermonde) drives the extraction: multi-polynomial / multi-point knowledge soundness
(§ batched opening soundness), single-chunk soundness (§ chunked opening), and the
chunked-batch headline (§ chunked batched opening). The two assumptions — the Fiat–Shamir
tree and binding — stay hypotheses; the instantiation at the deployed Poseidon-driven
verifier is `Bulletproof.Reflection`.
-/

/-!
## The `n`-point Vandermonde dual basis

The algebraic engine of the batched-opening extraction: reading off one coefficient
of a degree-`< n` polynomial from its values at `n` distinct nodes.

Given `n` pairwise-distinct nodes `ξ : Fin n → F` and a target index `d : Fin n`,
there is a coefficient vector `l : Fin n → F` such that the functional
`p ↦ ∑ s, l s * p (ξ s)` reads off the coefficient of `X ^ d`. Concretely,
`∑ s, l s * (ξ s) ^ i = [i = d]`.

This generalizes the three-node `vandermonde3` (Soundness/Linear.lean) to any
`n`. The engine is Mathlib's `Matrix.vandermonde` together with
`Matrix.det_vandermonde` (the determinant is `∏_{s < s'} (ξ s' - ξ s)`, nonzero
under injectivity, so the Vandermonde matrix is invertible over the field).
-/

namespace Bulletproof

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- **`n`-point Vandermonde dual basis.** For pairwise-distinct nodes
`ξ : Fin n → F` (injective) and a target index `d`, there exist coefficients
`l : Fin n → F` with `∑ s, l s * (ξ s) ^ i = [i = d]` for every `i`. Equivalently,
the functional `p ↦ ∑ s, l s * p (ξ s)` reads off the coefficient of `X ^ d` of any
polynomial of degree `< n`. Generalizes `vandermonde3`; the engine is
`Matrix.vandermonde` + `Matrix.det_vandermonde`. -/
private theorem vandermondeN {n : ℕ} (ξ : Fin n → F) (hξ : Function.Injective ξ)
    (d : Fin n) :
    ∃ l : Fin n → F,
      ∀ i : Fin n, ∑ s, l s * (ξ s) ^ (i : ℕ) = if i = d then 1 else 0 := by
  -- `M` is the transpose of Mathlib's Vandermonde matrix: `M i s = (ξ s) ^ i`.
  set M : Matrix (Fin n) (Fin n) F := (Matrix.vandermonde ξ).transpose with hM
  -- `M` is invertible: its determinant equals that of `Matrix.vandermonde ξ`,
  -- which is nonzero because `ξ` is injective.
  have hdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hξ
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  -- Take `l` as the preimage of the `d`-th standard basis vector under `M`.
  refine ⟨M⁻¹.mulVec (Pi.single d 1), fun i => ?_⟩
  have hmul : M.mulVec (M⁻¹.mulVec (Pi.single d 1)) = Pi.single d 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hunit, Matrix.one_mulVec]
  -- The functional `∑ s, l s * (ξ s) ^ i` is exactly `(M.mulVec l) i`.
  have hval : ∑ s, M⁻¹.mulVec (Pi.single d 1) s * (ξ s) ^ (i : ℕ)
      = (M.mulVec (M⁻¹.mulVec (Pi.single d 1))) i := by
    simp only [Matrix.mulVec, dotProduct, hM, Matrix.transpose_apply,
      Matrix.vandermonde_apply]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hval, hmul, Pi.single_apply]

end Bulletproof

/-!
## Knowledge soundness of the batched kimchi IPA opening

The headline of the batch development (`batch_soundnessA`): correct combined openings
at enough distinct `(polyscale ξ, evalscale r)` pairs imply that every individual
claimed evaluation is the true evaluation of the committed polynomial. Built on the
single-opening IPA stack (`Basic`/`Verify`/`Soundness`/`Soundness/{Linear,Tree,Binding}`)
and the batch definitions (`Batch`, `Soundness/Vandermonde`).

The extraction is the standard multi-poly/multi-point PCS reduction, specialized to
the kimchi IPA relation:

1. generalize the single-opening extractor to an arbitrary eval vector
   (`ipa_soundnessA`);
2. separate commitments by a Vandermonde combination in the polyscale
   (`perCommitment_separation`), using commitment linearity (`commit_sum_smul`);
3. use binding to force one witness per commitment, then a second Vandermonde in the
   evalscale to pin every individual evaluation (`batch_soundnessA`).

## Scope: what is proved, and what is assumed

The algebraic core is proved: accepting transcript trees, the special-soundness
extraction of the single-opening stack, the two Vandermonde separations, and
binding-uniqueness yield per-commitment witnesses with genuine evaluations. Two
hypotheses carry the cryptographic weight:

* **The Fiat–Shamir tree hypothesis** (`hFS` — a `FiatShamirTreeB` per grid point):
  an accepting run yields a de-blinded accepting transcript tree. This is the
  rewinding / Fiat–Shamir extraction, assumed rather than proved. It also carries the
  correspondence between the verifier's scalar acceptance equation (through
  `combinedB`, `bPoly`, `sg`) and the tree over `combinedEvalVector` — the equation is
  never exercised here, since `ipa_soundnessA` holds for any `b0`.

* **Binding** (`hbind`, no nontrivial discrete-log relation) — the idealization of
  computational DL-relation hardness. It is information-theoretically false for a real
  single-curve SRS (among `2 ^ k + 1` generators in a group of order `|F|` a nontrivial
  relation always exists), so the theorem is vacuous at real parameters; it is
  meaningful only as the computational assumption, discharged elsewhere.
-/

namespace Bulletproof

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

/-- **Single-opening soundness at an arbitrary eval vector, with abstract acceptance.**
Under the Fiat-Shamir tree hypothesis an accepting run yields an opening witness for
`openingRelationB`, with the acceptance proposition `A` fully abstract: the extraction
consumes only the modus ponens of the Fiat-Shamir hypothesis against acceptance, never the
shape of acceptance itself. This is the form the deployed verifier's acceptance
(`Ipa.verify … = true`) plugs into. -/
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
private theorem commit_sum_smul (σ : SRS G) {n : ℕ} (l : Fin n → F)
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
private theorem perCommitment_separation (σ : SRS G) {n m : ℕ}
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

/-- **Batched opening soundness**, with the grid acceptance abstracted to an arbitrary
family `A`: the proof consumes acceptance only through the modus ponens of the
Fiat-Shamir hypothesis (`ipa_soundnessA`), so no per-grid-point proof or challenge data
appears. This is the form the deployed verifier's acceptance (`Ipa.verify … = true`,
whose challenges are sponge-derived rather than carried) plugs into — the kernel of the
chunked batch (`Soundness/ChunkedBatch.lean`). -/
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

end Bulletproof

/-!
## Chunked opening soundness

Chunked-opening soundness over the chunk definitions of `Chunk.lean`: under commitment
binding, an accepting IPA run on the combined commitment of honestly committed chunks
forces the claimed value to be the *full* polynomial's evaluation, composing onto the
single-opening soundness of `Soundness.lean` in the verifier's own combine-then-open
order. The chunk count is the degree bound, entering as the hypothesis
`p.natDegree < c · 2^k`.
-/

namespace Bulletproof

open Polynomial

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

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

/-!
## Knowledge soundness of the chunked batched kimchi IPA opening

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

The trust boundary is that of `Soundness/Batch.lean` — the Fiat–Shamir tree hypothesis
per grid point and the no-DL-relation binding idealization.
The grid is `(∑ i, nc i) × m`: the polyscale Vandermonde must separate *segments*, so
the polyscale row count is the total chunk count, not the polynomial count.
-/

namespace Bulletproof

open Polynomial

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- **Chunked batched opening soundness.** Let `nc` be the per-polynomial chunk counts
(all positive), `ξ` injective over the segment count `∑ i, nc i`, and `r` injective over
the `m ≥ 1` evaluation points. Under the per-grid-point Fiat–Shamir hypothesis on the
chunked combiners, the no-DL-relation binding hypothesis, and acceptance at every grid
point, every polynomial of the batch is bound: there is a genuine `q i` of degree
`< nc i · 2^k` whose chunk windows are what the wire chunks commit to, whose
evaluations are the `x^(2^k)`-power recombinations of the claimed chunk evaluations,
and whose chunk windows REPRODUCE each per-chunk claim individually (the last clause —
consumers that pin per-chunk claims against fixed chunk commitments, like the chunked
kimchi reduction's verifier-key rows, read the claims off it directly). The evaluation
clause is the recombination corollary of the degree bound and the per-chunk clause
(through `eval_eq_sum_chunkPoly` and `chunkPoly_eval`), kept for direct consumers. -/
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
        ∧ (∀ j, (q i).eval (x j)
            = ∑ c : Fin (nc i), ((x j) ^ 2 ^ σ.k) ^ (c : ℕ) * e i c j)
        ∧ ∀ (c : Fin (nc i)) (j : Fin m),
            e i c j = innerProduct (chunkCoeffs (2 ^ σ.k) (q i) (c : ℕ))
              (evalVector (2 ^ σ.k) (x j)) := by
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
  refine ⟨hdeg, fun c => ⟨ρ (finSigmaFinEquiv ⟨i, c⟩), ?_⟩, fun j => ?_, fun c j => ?_⟩
  · rw [hwin c]
    exact hCseg i c
  -- **Step 4 (recombine).** The assembled polynomial evaluates as the chunk
  -- recombination of the claimed values.
  · rw [eval_eq_sum_chunkPoly _ hdeg (x j), ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [chunkPoly_eval, hwin c, ← hEseg i c j]
  -- The per-chunk claims, read off the assembled windows.
  · rw [hwin c]
    exact hEseg i c j

end Bulletproof
