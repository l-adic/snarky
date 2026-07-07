import Kimchi.Verifier.Ipa
import Kimchi.Commitment.IPA.Soundness.Batch
import Kimchi.Pasta

/-!
# Reflection: the executable verifier meets the soundness layer

The bridge between `Kimchi.Verifier.Ipa.verify` (executable, over wire data, challenges
derived by the Poseidon sponge) and the `Prop`-level acceptance `BatchAccepts` of the IPA
soundness development — and, through the Fiat-Shamir axiom, the batch knowledge-soundness
theorem itself.

Three strata:

* **The scalar action.** The Pasta point groups are `p`-torsion for their group orders
  (`CompElliptic.Curves.PastaOrder`, under the Hasse axioms), so each carries a
  `Module (ZMod p)` structure by `AddCommGroup.zmodModule`; its action is definitionally
  `z.val • _`, the ℕ-action the executable verifier computes with. This instantiates the
  abstract `[Module F G]` of the soundness layer at the executable types.

* **Reflection.** `verify` and `BatchAccepts` are the same equations in two spellings:
  the executable combiners equal the library combiners (`msm_eq_commitGen`,
  `combineCommitments_eq`), and an accepting run satisfies `BatchAccepts` at the
  sponge-derived challenges, against the SRS whose randomisation base is the derived `U`
  (`verify_reflects` — the `{σ with U := …}` substitution is the deployed protocol's
  transcript-derived base standing in for the abstract one). The wire data enters through
  the named views (`Input.commitmentFn`/`pointFn`/`evalFn`, `transcriptChallenges`), used
  identically on both sides.

* **The Fiat-Shamir axiom and the headline.** `poseidon_fiat_shamir_vesta` is the
  project's declared assumption, stated at the junction: a run accepted by the
  Poseidon-instantiated verifier admits a de-blinded accepting transcript tree over the
  combined eval vector (`FiatShamirTreeB`, with the deployed acceptance
  `verify … = true` as the antecedent). It packages the rewinding/forking extraction and
  the random-oracle behaviour of the sponge; everything downstream of it is proved.
  `ipaVesta_sound` composes the axiom and `batch_soundness`: a grid of accepting runs at
  pairwise-distinct combination scalars, under the no-DL-relation binding *hypothesis*,
  yields genuine openings for every commitment. Binding stays a hypothesis — it is
  information-theoretically false at real parameters and meaningful only computationally
  (see `Soundness/Batch.lean`).
-/

namespace Kimchi.Verifier

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Curves.Pasta
open CompElliptic.Curves.Pasta.Vesta renaming curve → vestaCurve
open CompElliptic.Curves.Pasta.Pallas renaming curve → pallasCurve
open CompElliptic.Fields.Pasta Kimchi.Commitment.IPA Kimchi.Verifier.Ipa

/-! ## The scalar action on the Pasta point groups -/

/-- The Vesta point group is `PALLAS_BASE_CARD`-torsion (its group order, under the Hasse
axiom), hence a module over its scalar field. The action is definitionally `z.val • _`. -/
instance vestaPointModule : Module Fp (SWPoint vestaCurve) :=
  AddCommGroup.zmodModule fun P => by
    rw [← Vesta.card_eq Kimchi.Pasta.vesta_hasse]
    exact card_nsmul_eq_zero'

/-- The Pallas point group is `PALLAS_SCALAR_CARD`-torsion (its group order, under the
Hasse axiom), hence a module over its scalar field. -/
instance pallasPointModule : Module Fq (SWPoint pallasCurve) :=
  AddCommGroup.zmodModule fun P => by
    rw [← Pallas.card_eq Kimchi.Pasta.pallas_hasse]
    exact card_nsmul_eq_zero'

/-- The module action is the ℕ-action at the canonical representative — the form the
executable verifier computes with. -/
theorem vesta_smul_val (z : Fp) (P : SWPoint vestaCurve) : z • P = z.val • P :=
  rfl

theorem pallas_smul_val (z : Fq) (P : SWPoint pallasCurve) : z • P = z.val • P :=
  rfl

/-! ## The wire proof as an abstract opening proof -/

/-- The wire proof, reindexed to the abstract `OpeningProof` at its round count. -/
def Ipa.Proof.toOpening {C : CommitmentCurve} (p : Ipa.Proof C) {k : ℕ}
    (hk : p.lr.size = k) : OpeningProof C.ScalarField C.Point k where
  lr := fun j => p.lr[j.val]'(by omega)
  delta := p.delta
  z1 := p.z1
  z2 := p.z2
  sg := p.sg

/-! ## Reflection: the executable combiners are the library combiners -/

section Reflection

variable {C : CommitmentCurve} [Module C.ScalarField C.Point]
  (hsmul : ∀ (z : C.ScalarField) (P : C.Point), z • P = z.val • P)

include hsmul in
/-- The executable MSM is `commitGen`. -/
theorem msm_eq_commitGen {n : ℕ} (g : Fin n → C.Point) (a : Fin n → C.ScalarField) :
    msm C g a = commitGen g a := by
  simp only [Ipa.msm, commitGen]
  exact Finset.sum_congr rfl (fun i _ => (hsmul (a i) (g i)).symm)

/-- Generalized-accumulator running-power fold over a list: from any starting
accumulator `acc` and running power `p`, the first component is `acc` plus the
`(p · ξ^i)`-scaled sum of the list entries. The engine behind `combineCommitments_eq`. -/
private theorem combineFoldl_aux (ξ : C.ScalarField) (l : List C.Point) (acc : C.Point)
    (p : C.ScalarField) :
    (l.foldl (fun (a : C.Point × C.ScalarField) P => (a.1 + a.2.val • P, a.2 * ξ))
        (acc, p)).1
      = acc + ∑ i : Fin l.length, (p * ξ ^ (i : ℕ)).val • l[i] := by
  induction l generalizing acc p with
  | nil => simp
  | cons P t ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
      Fin.val_succ]
    rw [← _root_.add_assoc]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    rw [pow_succ]; ring

include hsmul in
/-- The executable running-power combination is `combinedCommitment`. -/
theorem combineCommitments_eq (ξ : C.ScalarField) (cs : Array C.Point) :
    combineCommitments C ξ cs
      = combinedCommitment ξ (fun i : Fin cs.size => cs[i]) := by
  rw [combineCommitments, ← Array.foldl_toList, combineFoldl_aux]
  simp only [one_mul, _root_.zero_add]
  rw [combinedCommitment]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsmul]; congr 1

/-- A left fold that adds `g x` for each list element equals the start plus the sum of
`g` over the list. The engine behind the recombination bridge. -/
private theorem foldl_add_eq_sum {D : Type*} (g : D → C.Point) (l : List D)
    (init : C.Point) :
    l.foldl (fun acc x => acc + g x) init = init + ∑ i : Fin l.length, g l[i] := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih, _root_.add_assoc]
    simp [Fin.sum_univ_succ]

/-- The executable zip-fold recombination equals the abstract indexed sum: folding
`(L, R, u)` triples matches `∑ j, (uⱼ⁻¹ • Lⱼ + uⱼ • Rⱼ)` scaled through `val`. -/
private theorem zipFold_eq_recombine (init : C.Point)
    (lr : Array (C.Point × C.Point)) (ch : Array C.ScalarField) (k : ℕ)
    (hlr : lr.size = k) (hch : ch.size = k) :
    (lr.zip ch).foldl
        (fun (acc : C.Point) (LRu : (C.Point × C.Point) × C.ScalarField) =>
          acc + (LRu.2⁻¹.val • LRu.1.1 + LRu.2.val • LRu.1.2)) init
      = init + ∑ j : Fin k,
          ((ch[(j : ℕ)]'(by omega))⁻¹.val • (lr[(j : ℕ)]'(by omega)).1
            + (ch[(j : ℕ)]'(by omega)).val • (lr[(j : ℕ)]'(by omega)).2) := by
  rw [← Array.foldl_toList, foldl_add_eq_sum]
  congr 1
  have hlen : (lr.zip ch).toList.length = k := by
    rw [Array.length_toList, Array.size_zip, hlr, hch, min_self]
  refine Fintype.sum_equiv (finCongr hlen) _ _ (fun i => ?_)
  simp only [finCongr_apply, Fin.val_cast, Fin.getElem_fin, Array.getElem_toList,
    Array.getElem_zip]

include hsmul in
/-- **Reflection.** An accepting executable run satisfies the `Prop`-level batched
acceptance at the sponge-derived challenges, against the SRS whose randomisation base is
the transcript-derived `U`. With `(U, chal, c) := transcript C inp`:
`BatchAccepts {σ with U := U} proof ξ r c chal commitments xs evals`, the wire data
entering through its named views. -/
theorem verify_reflects (σ : SRS C.Point) (inp : Ipa.Input C)
    (hv : Ipa.verify C σ inp = true) :
    BatchAccepts { σ with U := (transcript C inp).1 }
      (inp.proof.toOpening (verify_shape C σ inp hv))
      inp.polyscale inp.evalscale
      (transcript C inp).2.2
      (transcriptChallenges C inp (transcript_size_of_verify C σ inp hv))
      inp.commitmentFn inp.pointFn inp.evalFn := by
  have hsize := verify_shape C σ inp hv
  have hchsz := transcript_size_of_verify C σ inp hv
  -- The two spelling bridges: the executable `getElem!` challenge and eval-point
  -- functions are the named views.
  have hchal : (fun i : Fin σ.k => (transcript C inp).2.1[i.val]!)
      = transcriptChallenges C inp hchsz := by
    funext i
    exact getElem!_pos (transcript C inp).2.1 i.val (by rw [hchsz]; exact i.isLt)
  have hpt : (fun j : Fin inp.xs.size => inp.xs[j.val]!) = inp.pointFn := by
    funext j
    exact getElem!_pos inp.xs j.val j.isLt
  simp only [Ipa.verify] at hv
  split at hv
  · exact absurd hv (by simp)
  · rw [Bool.and_eq_true] at hv
    obtain ⟨hsch, hsg⟩ := hv
    rw [decide_eq_true_eq] at hsch hsg
    rw [hchal] at hsch hsg
    rw [hpt] at hsch
    refine ⟨?_, ?_⟩
    · rw [zipFold_eq_recombine _ inp.proof.lr (transcript C inp).2.1 σ.k hsize hchsz]
        at hsch
      rw [combineCommitments_eq hsmul] at hsch
      unfold Kimchi.Commitment.IPA.recombine Ipa.Proof.toOpening
      simp only [hsmul, Ipa.transcriptChallenges, Ipa.Input.commitmentFn]
      exact hsch
    · exact hsg.trans (msm_eq_commitGen hsmul _ _)

end Reflection

/-! ## The Fiat-Shamir axiom -/

/-- **AXIOM (Fiat-Shamir, Poseidon instantiation, Vesta).** A run accepted by the
Poseidon-instantiated verifier admits a de-blinded accepting transcript tree over the
combined eval vector: `FiatShamirTreeB` with the deployed acceptance
`Ipa.verify … = true` as the antecedent. This is the project's declared assumption that
the Poseidon sponge provides a valid Fiat-Shamir transform — it packages the
rewinding/forking extraction and the random-oracle behaviour of the sponge. It is the
sole non-standard axiom of the headline `ipaVesta_sound`. -/
axiom poseidon_fiat_shamir_vesta (σ : SRS IpaVesta.Point) (inp : IpaVesta.Input) :
  FiatShamirTreeB σ
    (combinedCommitment inp.polyscale inp.commitmentFn)
    (combinedEvalVector (2 ^ σ.k) inp.evalscale inp.pointFn)
    (cipOf inp)
    (Ipa.verify IpaVesta.curve σ inp = true)

/-- **AXIOM (Fiat-Shamir, Poseidon instantiation, Pallas).** The Pallas-side twin of
`poseidon_fiat_shamir_vesta`. -/
axiom poseidon_fiat_shamir_pallas (σ : SRS IpaPallas.Point) (inp : IpaPallas.Input) :
  FiatShamirTreeB σ
    (combinedCommitment inp.polyscale inp.commitmentFn)
    (combinedEvalVector (2 ^ σ.k) inp.evalscale inp.pointFn)
    (cipOf inp)
    (Ipa.verify IpaPallas.curve σ inp = true)

/-! ## The headline -/

/-- **Soundness of the deployed Vesta verifier.** A grid of Poseidon-accepted runs of the
same claim — commitments `cs`, points `xs`, claimed evaluations `evals` — at
pairwise-distinct polyscales `ξ` and evalscales `r`, under the no-DL-relation binding
hypothesis, yields genuine openings: every commitment opens to a witness whose evaluation
at every point is the claimed one. Composes `poseidon_fiat_shamir_vesta` and
`batch_soundness`; binding remains a hypothesis (see the module docstring). -/
theorem ipaVesta_sound (σ : SRS IpaVesta.Point)
    (cs : Array IpaVesta.Point) (xs : Array Fp) (evals : Array (Array Fp))
    (hm : 0 < xs.size)
    (ξ : Fin cs.size → Fp) (hξ : Function.Injective ξ)
    (r : Fin xs.size → Fp) (hr : Function.Injective r)
    (proofs : Fin cs.size → Fin xs.size → IpaVesta.Proof)
    (hacc : ∀ s t, Ipa.verify IpaVesta.curve σ
      (mkInput IpaVesta.curve cs xs evals (ξ s) (r t) (proofs s t)) = true)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp),
      DLRelation σ w wh → w = 0 ∧ wh = 0) :
    ∃ (a : Fin cs.size → Fin (2 ^ σ.k) → Fp) (ρ : Fin cs.size → Fp),
      ∀ i, commit σ (a i) (ρ i) = cs[i]
        ∧ ∀ j : Fin xs.size,
            (evals[i.val]!)[j.val]! = innerProduct (a i) (evalVector (2 ^ σ.k) xs[j]) := by
  -- The grid input at combination scalars `(ξ s, r t)`.
  set inp : Fin cs.size → Fin xs.size → IpaVesta.Input := fun s t =>
    mkInput IpaVesta.curve cs xs evals (ξ s) (r t) (proofs s t) with hinp
  -- The Poseidon Fiat–Shamir axiom at every grid point: an accepting Poseidon run yields
  -- a de-blinded accepting tree over the combined eval vector, with the deployed
  -- acceptance `Ipa.verify … = true` as the antecedent.
  have hFS : ∀ (s : Fin cs.size) (t : Fin xs.size),
      FiatShamirTreeB σ
        (combinedCommitment (ξ s) (fun i : Fin cs.size => cs[i]))
        (combinedEvalVector (2 ^ σ.k) (r t) (fun j : Fin xs.size => xs[j]))
        (cipOf (inp s t))
        (Ipa.verify IpaVesta.curve σ (inp s t) = true) :=
    fun s t => poseidon_fiat_shamir_vesta σ (inp s t)
  -- `cipOf (inp s t)` is exactly the combined inner product of the claimed evaluations.
  have hcip : ∀ (s : Fin cs.size) (t : Fin xs.size),
      cipOf (inp s t)
        = combinedInnerProduct (ξ s) (r t)
            (fun (i : Fin cs.size) (j : Fin xs.size) => (evals[i.val]!)[j.val]!) :=
    fun s t => rfl
  simp only [hcip] at hFS
  obtain ⟨a, ρ, h⟩ := batch_soundnessA σ ξ hξ r hr hm
    (fun i : Fin cs.size => cs[i]) (fun j : Fin xs.size => xs[j])
    (fun (i : Fin cs.size) (j : Fin xs.size) => (evals[i.val]!)[j.val]!)
    (fun s t => Ipa.verify IpaVesta.curve σ (inp s t) = true)
    hFS hbind hacc
  exact ⟨a, ρ, fun i => ⟨(h i).1, fun j => (h i).2 j⟩⟩

/-- **Soundness of the deployed Pallas verifier.** A grid of Poseidon-accepted runs of the
same claim — commitments `cs`, points `xs`, claimed evaluations `evals` — at
pairwise-distinct polyscales `ξ` and evalscales `r`, under the no-DL-relation binding
hypothesis, yields genuine openings: every commitment opens to a witness whose evaluation
at every point is the claimed one. The Pallas-side twin of `ipaPallas_sound`. -/
theorem ipaPallas_sound (σ : SRS IpaPallas.Point)
    (cs : Array IpaPallas.Point) (xs : Array Fq) (evals : Array (Array Fq))
    (hm : 0 < xs.size)
    (ξ : Fin cs.size → Fq) (hξ : Function.Injective ξ)
    (r : Fin xs.size → Fq) (hr : Function.Injective r)
    (proofs : Fin cs.size → Fin xs.size → IpaPallas.Proof)
    (hacc : ∀ s t, Ipa.verify IpaPallas.curve σ
      (mkInput IpaPallas.curve cs xs evals (ξ s) (r t) (proofs s t)) = true)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq),
      DLRelation σ w wh → w = 0 ∧ wh = 0) :
    ∃ (a : Fin cs.size → Fin (2 ^ σ.k) → Fq) (ρ : Fin cs.size → Fq),
      ∀ i, commit σ (a i) (ρ i) = cs[i]
        ∧ ∀ j : Fin xs.size,
            (evals[i.val]!)[j.val]! = innerProduct (a i) (evalVector (2 ^ σ.k) xs[j]) := by
  -- The grid input at combination scalars `(ξ s, r t)`.
  set inp : Fin cs.size → Fin xs.size → IpaPallas.Input := fun s t =>
    mkInput IpaPallas.curve cs xs evals (ξ s) (r t) (proofs s t) with hinp
  -- The Poseidon Fiat–Shamir axiom at every grid point: an accepting Poseidon run yields
  -- a de-blinded accepting tree over the combined eval vector, with the deployed
  -- acceptance `Ipa.verify … = true` as the antecedent.
  have hFS : ∀ (s : Fin cs.size) (t : Fin xs.size),
      FiatShamirTreeB σ
        (combinedCommitment (ξ s) (fun i : Fin cs.size => cs[i]))
        (combinedEvalVector (2 ^ σ.k) (r t) (fun j : Fin xs.size => xs[j]))
        (cipOf (inp s t))
        (Ipa.verify IpaPallas.curve σ (inp s t) = true) :=
    fun s t => poseidon_fiat_shamir_pallas σ (inp s t)
  -- `cipOf (inp s t)` is exactly the combined inner product of the claimed evaluations.
  have hcip : ∀ (s : Fin cs.size) (t : Fin xs.size),
      cipOf (inp s t)
        = combinedInnerProduct (ξ s) (r t)
            (fun (i : Fin cs.size) (j : Fin xs.size) => (evals[i.val]!)[j.val]!) :=
    fun s t => rfl
  simp only [hcip] at hFS
  obtain ⟨a, ρ, h⟩ := batch_soundnessA σ ξ hξ r hr hm
    (fun i : Fin cs.size => cs[i]) (fun j : Fin xs.size => xs[j])
    (fun (i : Fin cs.size) (j : Fin xs.size) => (evals[i.val]!)[j.val]!)
    (fun s t => Ipa.verify IpaPallas.curve σ (inp s t) = true)
    hFS hbind hacc
  exact ⟨a, ρ, fun i => ⟨(h i).1, fun j => (h i).2 j⟩⟩

end Kimchi.Verifier
