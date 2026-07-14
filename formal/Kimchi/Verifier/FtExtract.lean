import Mathlib
import Kimchi.Verifier.KimchiSound

/-!
# t-uniformity discharged (milestone 4.6): `t_extraction` and `kimchiProof_sound_ft`

This file closes the one documented deferral of `kimchiProof_sound` (see `## The t
deferral` in `Kimchi/Verifier/KimchiSound.lean`): the per-`(β, γ, α)` quotient family
`(t, ht, hteq)` is no longer hypothesis data — it is *derived* from ft-row binding data,
using the wire-enforced fact that the seven `t`-chunk commitments are fixed across the
`ζ`-grid (production commits them before `ζ` is sampled). This is where the chunk kit of
`Kimchi/Commitment/IPA/Chunk.lean` (`assemblePoly`, `chunkCoeffs_assemblePoly`,
`eval_eq_sum_chunkPoly`) joins the main soundness path: the extracted per-chunk witness
vectors are assembled into one degree-`< 7·2^k` polynomial whose evaluations satisfy the
deployed scalar equation at *every* `ζ`-point of the grid.

**The extraction** (`t_extraction`). Per transcript prefix, the verifier's `ftComm`
combination reads `pS·Cσ6 − (ζ^{2^k} − 1)·∑ᵢ (ζ^{2^k})^i·TCᵢ` with the chunk commitments
`TC` independent of `ζ`. Seven designated `ζ`-points whose `ζ^{2^k}`-values are pairwise
distinct (and ≠ 1) let the `n`-point Vandermonde dual basis
(`Soundness/Vandermonde.lean`) invert the power combination: each `TC i` is exhibited as
a hiding commitment with an explicit witness — a `d`-combination of the bound ft-row
witnesses, by pure commit linearity (`commit_smul`/`commit_sub`/`commit_sum_smul`).
Binding then pins *every* point's ft row to the corresponding combination of `σ₆`'s
coefficients and the assembled chunks, and the claimed `ftEval0` value becomes the
deployed equation `pS·σ₆(ζ) − (ζ^{2^k} − 1)·t(ζ) = ftEval0` — the exact consumer shape
of `kimchiProof_sound`. `ft_equation` (`Sound.lean`) is the single-transcript version of
this identity; here the `ζ`-free-ness of `TC` upgrades it to the `p`-uniform family.

**The composed root** (`kimchiProof_sound_ft`). `kimchiProof_sound` with its
`(t, ht, hteq)` hypotheses replaced by per-prefix ft-row data: the `ζ`-free chunk
commitments `TC`, the bound ft witnesses with their `ftComm` commitment and `ftEval0`
evaluation families (stated verbatim at the claimed record, as `hteq` was), and seven
designated points per prefix with injective `ζ^n`-values. The `≠ 1` side condition comes
free from the existing grid hypothesis `hζn`.

**The trust story.** The `ζ`-free-ness of `TC` and the designated-points data are
transcript-prefix facts the Fiat–Shamir layer (milestone 5) supplies — `TC` is committed
after `α` and before `ζ`, and the seven points are sampled from the `ζ`-grid. Binding
(the no-DL-relation hypothesis) and the challenge grids remain the standing
idealizations, exactly as in `kimchiProof_sound`.
-/

namespace Kimchi.Verifier

open Polynomial Kimchi.Commitment.IPA Kimchi.Index Kimchi.Verifier.Linearization
  Kimchi.Verifier.Equation

variable {F G : Type*}

/-! ## Inner-product linearity

Two-term instances of the inner product's linearity in its first slot, mirroring
`commit_smul`/`commit_sub` (`Sound.lean`); `Chunk.lean` exposes only the `y`-power
combination `innerProduct_combine`. -/

private theorem innerProduct_sub [Field F] {n : ℕ} (u v w : Fin n → F) :
    innerProduct (u - v) w = innerProduct u w - innerProduct v w := by
  unfold innerProduct
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem innerProduct_smul [Field F] {n : ℕ} (c : F) (u w : Fin n → F) :
    innerProduct (c • u) w = c * innerProduct u w := by
  unfold innerProduct
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-! ## Chunk-witness recovery -/

/-- **One chunk commitment is a hiding commitment** — the Vandermonde recovery step.
The `ftComm` combinations at seven designated points whose `y = ζ^{2^k}` values are
pairwise distinct (and `≠ 1`) determine each chunk commitment `TC i` as a hiding
commitment with an explicit witness: the Vandermonde dual basis `l` at the `y`-values
reads off the `i`-th power coefficient, and dividing by the nonzero `y − 1` factors
turns the per-point combinations `(y − 1) • ∑ₘ yᵐ • TC m = pS • Cσ6 − commit (a, ρ)`
into `TC i` on the left and a commit-linearity combination on the right. -/
private theorem chunk_witnesses [Field F] [AddCommGroup G] [Module F G] (σ : SRS G)
    (σ₆ : Polynomial F) (Cσ6 : G) (hC : Cσ6 = commitPoly σ σ₆)
    (TC : Fin 7 → G) {P : Type*} (ζ pS : P → F)
    (a : P → Fin (2 ^ σ.k) → F) (ρ : P → F)
    (hcommit : ∀ p, commit σ (a p) (ρ p)
      = pS p • Cσ6
        - ((ζ p) ^ 2 ^ σ.k - 1) • ∑ i : Fin 7, ((ζ p) ^ 2 ^ σ.k) ^ (i : ℕ) • TC i)
    (q : Fin 7 → P) (hq : Function.Injective fun j => (ζ (q j)) ^ 2 ^ σ.k)
    (hq1 : ∀ j, (ζ (q j)) ^ 2 ^ σ.k ≠ 1) (i : Fin 7) :
    ∃ (τ : Fin (2 ^ σ.k) → F) (rb : F), TC i = commit σ τ rb := by
  obtain ⟨l, hl⟩ := vandermondeN (fun j => (ζ (q j)) ^ 2 ^ σ.k) hq i
  -- the per-point combination, rewritten as one hiding commitment by commit linearity
  have hAB : ∀ j : Fin 7,
      ((ζ (q j)) ^ 2 ^ σ.k - 1) • ∑ m : Fin 7, ((ζ (q j)) ^ 2 ^ σ.k) ^ (m : ℕ) • TC m
      = commit σ (pS (q j) • (fun m : Fin (2 ^ σ.k) => σ₆.coeff (m : ℕ)) - a (q j))
          (pS (q j) * 0 - ρ (q j)) := by
    intro j
    rw [commit_sub, commit_smul, ← commitPoly_eq_commit, ← hC, hcommit (q j)]
    abel
  -- dividing the dual-basis coefficients by the nonzero `y − 1` factors
  have key : ∀ j : Fin 7,
      ∑ m : Fin 7, (l j * ((ζ (q j)) ^ 2 ^ σ.k) ^ (m : ℕ)) • TC m
      = (l j / ((ζ (q j)) ^ 2 ^ σ.k - 1))
          • (((ζ (q j)) ^ 2 ^ σ.k - 1)
              • ∑ m : Fin 7, ((ζ (q j)) ^ 2 ^ σ.k) ^ (m : ℕ) • TC m) := by
    intro j
    rw [smul_smul, div_mul_cancel₀ _ (sub_ne_zero.mpr (hq1 j)), Finset.smul_sum]
    simp only [smul_smul]
  refine ⟨∑ j, (l j / ((ζ (q j)) ^ 2 ^ σ.k - 1))
      • (pS (q j) • (fun m : Fin (2 ^ σ.k) => σ₆.coeff (m : ℕ)) - a (q j)),
    ∑ j, (l j / ((ζ (q j)) ^ 2 ^ σ.k - 1)) * (pS (q j) * 0 - ρ (q j)), ?_⟩
  calc TC i
      = ∑ m : Fin 7, (∑ j, l j * ((ζ (q j)) ^ 2 ^ σ.k) ^ (m : ℕ)) • TC m := by
        simp [hl]
    _ = ∑ j, ∑ m : Fin 7, (l j * ((ζ (q j)) ^ 2 ^ σ.k) ^ (m : ℕ)) • TC m := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_smul
    _ = ∑ j, (l j / ((ζ (q j)) ^ 2 ^ σ.k - 1))
          • commit σ (pS (q j) • (fun m : Fin (2 ^ σ.k) => σ₆.coeff (m : ℕ)) - a (q j))
              (pS (q j) * 0 - ρ (q j)) :=
        Finset.sum_congr rfl fun j _ => by rw [key j, hAB j]
    _ = commit σ
          (∑ j, (l j / ((ζ (q j)) ^ 2 ^ σ.k - 1))
            • (pS (q j) • (fun m : Fin (2 ^ σ.k) => σ₆.coeff (m : ℕ)) - a (q j)))
          (∑ j, (l j / ((ζ (q j)) ^ 2 ^ σ.k - 1)) * (pS (q j) * 0 - ρ (q j))) :=
        (commit_sum_smul σ (fun j => l j / ((ζ (q j)) ^ 2 ^ σ.k - 1))
          (fun j => pS (q j) • (fun m : Fin (2 ^ σ.k) => σ₆.coeff (m : ℕ)) - a (q j))
          (fun j => pS (q j) * 0 - ρ (q j))).symm

/-! ## The extraction -/

/-- **The t extraction (milestone 4.6)** — the quotient data `(t, ht, hteq)` of
`kimchiProof_sound` derived from ft-row binding data, per transcript prefix. The seven
`t`-chunk commitments `TC` are `ζ`-free (committed before `ζ`); per `ζ`-point the bound
ft row commits to the verifier's `ftComm` combination (`hcommit`) and its claimed value
is `fte` (`heval`). Seven designated points with injective, `≠ 1` values of `ζ^{2^k}`
(`hq`/`hq1`) recover each chunk as a hiding commitment (`chunk_witnesses`); the chunks
assemble into one polynomial `t` of degree `< 7·2^k` (`assemblePoly`), and binding pins
*every* point's ft row to the matching combination, closing the deployed scalar
equation at every point by chunk-eval recombination (`eval_eq_sum_chunkPoly`). -/
theorem t_extraction [Field F] [AddCommGroup G] [Module F G] (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (σ₆ : Polynomial F) (hσ₆ : σ₆.natDegree < 2 ^ σ.k)
    (Cσ6 : G) (hC : Cσ6 = commitPoly σ σ₆)
    (TC : Fin 7 → G)
    {P : Type*} (ζ pS fte : P → F)
    (a : P → Fin (2 ^ σ.k) → F) (ρ : P → F)
    (hcommit : ∀ p, commit σ (a p) (ρ p)
      = pS p • Cσ6
        - ((ζ p) ^ 2 ^ σ.k - 1) • ∑ i : Fin 7, ((ζ p) ^ 2 ^ σ.k) ^ (i : ℕ) • TC i)
    (heval : ∀ p, innerProduct (a p) (evalVector (2 ^ σ.k) (ζ p)) = fte p)
    (q : Fin 7 → P)
    (hq : Function.Injective fun j => (ζ (q j)) ^ 2 ^ σ.k)
    (hq1 : ∀ j, (ζ (q j)) ^ 2 ^ σ.k ≠ 1) :
    ∃ t : Polynomial F, t.natDegree < 7 * 2 ^ σ.k
      ∧ ∀ p, pS p * σ₆.eval (ζ p) - ((ζ p) ^ 2 ^ σ.k - 1) * t.eval (ζ p) = fte p := by
  classical
  -- chunk recovery: each TC i is a hiding commitment
  choose τ rb hTC using fun i =>
    chunk_witnesses σ σ₆ Cσ6 hC TC ζ pS a ρ hcommit q hq hq1 i
  -- ℕ-indexed windows for the assembly kit
  set τn : ℕ → Fin (2 ^ σ.k) → F := fun ci => if h : ci < 7 then τ ⟨ci, h⟩ else 0
    with hτn
  set rbn : ℕ → F := fun ci => if h : ci < 7 then rb ⟨ci, h⟩ else 0 with hrbn
  have hTCn : ∀ m : Fin 7, TC m = commit σ (τn (m : ℕ)) (rbn (m : ℕ)) := by
    intro m
    rw [hTC m]
    simp [hτn, hrbn]
  refine ⟨assemblePoly (2 ^ σ.k) 7 τn,
    assemblePoly_natDegree_lt (Nat.two_pow_pos σ.k) (by norm_num) τn, fun p => ?_⟩
  have hdeg : (assemblePoly (2 ^ σ.k) 7 τn).natDegree < 7 * 2 ^ σ.k :=
    assemblePoly_natDegree_lt (Nat.two_pow_pos σ.k) (by norm_num) τn
  -- the combined chunk sum at this point is one hiding commitment
  have hcomb : ∑ i : Fin 7, ((ζ p) ^ 2 ^ σ.k) ^ (i : ℕ) • TC i
      = commit σ (∑ i ∈ Finset.range 7, ((ζ p) ^ 2 ^ σ.k) ^ i • τn i)
          (∑ i ∈ Finset.range 7, ((ζ p) ^ 2 ^ σ.k) ^ i • rbn i) :=
    calc ∑ i : Fin 7, ((ζ p) ^ 2 ^ σ.k) ^ (i : ℕ) • TC i
        = ∑ i : Fin 7, ((ζ p) ^ 2 ^ σ.k) ^ (i : ℕ) • commit σ (τn (i : ℕ)) (rbn (i : ℕ)) :=
          Finset.sum_congr rfl fun m _ => by rw [hTCn m]
      _ = ∑ i ∈ Finset.range 7, ((ζ p) ^ 2 ^ σ.k) ^ i • commit σ (τn i) (rbn i) :=
          Fin.sum_univ_eq_sum_range
            (fun i => ((ζ p) ^ 2 ^ σ.k) ^ i • commit σ (τn i) (rbn i)) 7
      _ = commit σ (∑ i ∈ Finset.range 7, ((ζ p) ^ 2 ^ σ.k) ^ i • τn i)
            (∑ i ∈ Finset.range 7, ((ζ p) ^ 2 ^ σ.k) ^ i • rbn i) :=
          commit_combine σ ((ζ p) ^ 2 ^ σ.k) 7 τn rbn
  -- binding pins this point's ft row to the matching combination
  have hpin : commit σ (a p) (ρ p)
      = commit σ (pS p • (fun m : Fin (2 ^ σ.k) => σ₆.coeff (m : ℕ))
            - ((ζ p) ^ 2 ^ σ.k - 1) • ∑ i ∈ Finset.range 7, ((ζ p) ^ 2 ^ σ.k) ^ i • τn i)
          (pS p * 0 - ((ζ p) ^ 2 ^ σ.k - 1)
            * ∑ i ∈ Finset.range 7, ((ζ p) ^ 2 ^ σ.k) ^ i • rbn i) := by
    rw [commit_sub, commit_smul, commit_smul, ← commitPoly_eq_commit, ← hC, ← hcomb]
    exact hcommit p
  have hrow := bound_unique σ hbind hpin
  -- the σ₆ side and the chunk side of the pinned row's evaluation
  have hσeval : innerProduct (fun m : Fin (2 ^ σ.k) => σ₆.coeff (m : ℕ))
      (evalVector (2 ^ σ.k) (ζ p)) = σ₆.eval (ζ p) := by
    rw [← rowPoly_eval, rowPoly_coeff_self hσ₆]
  have hAeval : innerProduct (∑ i ∈ Finset.range 7, ((ζ p) ^ 2 ^ σ.k) ^ i • τn i)
      (evalVector (2 ^ σ.k) (ζ p))
      = (assemblePoly (2 ^ σ.k) 7 τn).eval (ζ p) := by
    rw [innerProduct_combine,
      eval_eq_sum_chunkPoly (assemblePoly (2 ^ σ.k) 7 τn) hdeg (ζ p)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [chunkPoly_eval, chunkCoeffs_assemblePoly τn (Finset.mem_range.mp hi)]
  rw [← heval p, ← rowPoly_eval, hrow, rowPoly_eval, innerProduct_sub,
    innerProduct_smul, innerProduct_smul, hσeval, hAeval]

/-! ## The composed root -/

/-- **The composed kimchi soundness headline with the t deferral discharged
(milestone 4.6).** `kimchiProof_sound` with its quotient hypotheses `(t, ht, hteq)`
replaced by ft-row data: per `(a, c, s)`-prefix the seven `ζ`-free t-chunk commitments
`TC` (committed after `α`, before `ζ`), the bound ft-row witnesses with their `ftComm`
commitment (`hftC`) and claimed `ftEval0` evaluation (`hftE`) families — stated verbatim
at the claimed record and the Index-side `σ₆`, exactly as `hteq` was — and seven
designated points per prefix whose `ζ^n`-values are injective (`hq`; the `≠ 1` side is
the existing grid hypothesis `hζn`). `t_extraction` per prefix supplies the quotient
family, and `kimchiProof_sound` closes. The remaining hypotheses and the trust story are
those of `kimchiProof_sound`; the `TC`/designated-points data are the transcript-prefix
facts the Fiat–Shamir layer (milestone 5) supplies. -/
theorem kimchiProof_sound_ft [Field F] [AddCommGroup G] [Module F G]
    {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) (hk : 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms G) (hvk : VKCorresponds σ comms idx)
    (pub : Fin idx.publicCount → F)
    {M NN NNN : ℕ} (b : Fin M → F) (g : Fin NN → F)
    (hb : Function.Injective b) (hg : Function.Injective g)
    (hM : 7 * (n - idx.zkRows) < M) (hN : 7 * (n - idx.zkRows) < NN)
    (ζ : Fin M → Fin NN → Fin NNN → F) (hζ : ∀ a c, Function.Injective (ζ a c))
    (hζ₁ : ∀ a c p, ζ a c p ≠ 1)
    (hζb : ∀ a c p, ζ a c p ≠ idx.omega ^ (n - idx.zkRows))
    (hζn : ∀ a c p, (ζ a c p) ^ n ≠ 1)
    (α : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → F)
    (hα : ∀ a c, Function.Injective (α a c))
    (hD : Index.degreeBound n < NNN)
    (wC : Fin 15 → G) (zC : Fin M → Fin NN → G)
    (E : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
      → Fin 43 → Fin 2 → F)
    (ξ : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
      → Fin 43 → F)
    (hξ : ∀ a c s p, Function.Injective (ξ a c s p))
    (r : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
      → Fin 2 → F)
    (hr : ∀ a c s p, Function.Injective (r a c s p))
    (A : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
      → Fin 43 → Fin 2 → Prop)
    (hFS : ∀ a c s p (i : Fin 43) (j : Fin 2),
      FiatShamirTreeB σ (combinedCommitment (ξ a c s p i) (batchC wC (zC a c) comms))
        (combinedEvalVector (2 ^ σ.k) (r a c s p j) ![ζ a c p, idx.omega * ζ a c p])
        (combinedInnerProduct (ξ a c s p i) (r a c s p j) (E a c s p))
        (A a c s p i j))
    (hacc : ∀ a c s p i j, A a c s p i j)
    (TC : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount)
      → Fin 7 → G)
    (aft : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
      → Fin (2 ^ σ.k) → F)
    (ρft : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
      → F)
    (hftC : ∀ a c s p, commit σ (aft a c s p) (ρft a c s p)
      = permScalar (b a) (g c) (α a c s) (zkpmEval n idx.zkRows idx.omega (ζ a c p))
            (claimedEvals (E a c s p))
          • comms.sigma 6
        - ((ζ a c p) ^ n - 1) • ∑ i : Fin 7, ((ζ a c p) ^ n) ^ (i : ℕ) • TC a c s i)
    (hftE : ∀ a c s p, innerProduct (aft a c s p) (evalVector (2 ^ σ.k) (ζ a c p))
      = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase (α a c s) (b a) (g c)
          (ζ a c p) (-((idx.pubPoly pub).eval (ζ a c p))) (claimedEvals (E a c s p)))
    (q : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount)
      → Fin 7 → Fin NNN)
    (hq : ∀ a c s, Function.Injective fun j => (ζ a c (q a c s j)) ^ n) :
    ∃ wTab : Fin n → Fin 15 → F, Satisfies idx pub wTab := by
  subst hk
  have hvk' : comms = indexerOf σ idx := hvk
  subst hvk'
  have hC : (indexerOf σ idx).sigma 6 = commitPoly σ (idx.sigmaPoly 6) := rfl
  have hσ₆ : (idx.sigmaPoly 6).natDegree < 2 ^ σ.k :=
    columnPoly_natDegree_lt idx.omega_prim _
  choose t ht hteq using fun a c s =>
    t_extraction σ hbind (idx.sigmaPoly 6) hσ₆ ((indexerOf σ idx).sigma 6) hC
      (TC a c s) (ζ a c)
      (fun p => permScalar (b a) (g c) (α a c s)
        (zkpmEval (2 ^ σ.k) idx.zkRows idx.omega (ζ a c p)) (claimedEvals (E a c s p)))
      (fun p => ftEval0 (2 ^ σ.k) idx.zkRows idx.omega idx.shifts idx.endoBase
        (α a c s) (b a) (g c) (ζ a c p) (-((idx.pubPoly pub).eval (ζ a c p)))
        (claimedEvals (E a c s p)))
      (aft a c s) (ρft a c s) (hftC a c s) (hftE a c s) (q a c s) (hq a c s)
      (fun j => hζn a c (q a c s j))
  exact kimchiProof_sound σ idx rfl hbind (indexerOf σ idx) hvk pub b g hb hg hM hN
    ζ hζ hζ₁ hζb hζn α hα hD wC zC E ξ hξ r hr A hFS hacc t ht hteq

end Kimchi.Verifier
