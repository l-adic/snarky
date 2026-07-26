import Bulletproof.Wire
import Bulletproof.Soundness
import Pasta

/-!
# Reflection: the executable verifier meets the soundness layer

The bridge between `Bulletproof.Ipa.verify` (executable, over checked wire data,
challenges derived by the Poseidon sponge) and the `Prop`-level acceptance
`BatchAccepts` of the IPA soundness development — and, through the Fiat-Shamir axiom,
the batch knowledge-soundness theorem itself.

Three strata:

* **The scalar action.** The Pasta point-group module structure (`Pasta/Basic.lean`)
  instantiates the soundness layer's abstract `[Module F G]` at the executable types;
  the action is definitionally `z.val • _`, the ℕ-action the executable verifier
  computes with.

* **Reflection.** `verify` and `BatchAccepts` are the same equations in two spellings:
  the executable combiners equal the library combiners (`msm_eq_commitGen`,
  `combineCommitments_eq`), and an accepting run satisfies `BatchAccepts` at the
  sponge-derived challenges, against the SRS whose randomisation base is the derived
  `U` (`verify_reflects` — the `{σ with U := …}` substitution is the deployed
  protocol's transcript-derived base standing in for the abstract one). The checked
  input's shape lives in its type, so the wire data enters through TOTAL named views
  (`Input.commitmentFn`/`pointFn`/`evalFn`, and the sized challenge vector of
  `transcript`), used identically on both sides.

* **The Fiat-Shamir axiom and the headline.** `poseidon_fiat_shamir_vesta` is the
  project's declared assumption, stated at the junction: a run accepted by the
  Poseidon-instantiated verifier admits a de-blinded accepting transcript tree over the
  combined eval vector (`FiatShamirTreeB`, with the deployed acceptance
  `verify … = true` as the antecedent). It packages the rewinding/forking extraction and
  the random-oracle behaviour of the sponge; everything downstream of it is proved.
  `ipaVesta_sound` composes the axiom, the flattening lemmas, and
  `chunked_batch_soundness`: the claim declares its segment structure (`nc` chunks per
  polynomial), the verifier consumes the flattened segment stream
  (`segmentStream`), and a grid of accepting runs at pairwise-distinct combination
  scalars, under the no-DL-relation binding *hypothesis*, binds every commitment family
  to one genuine polynomial with its chunk windows and evaluations. Binding stays a
  hypothesis — it is information-theoretically false at real parameters and meaningful
  only computationally (see `Soundness/Batch.lean`).
-/

namespace Bulletproof

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Curves.Pasta
open CompElliptic.Curves.Pasta.Vesta renaming curve → vestaCurve
open CompElliptic.Curves.Pasta.Pallas renaming curve → pallasCurve
open CompElliptic.Fields.Pasta Bulletproof Bulletproof.Ipa

/-! ## The checked proof as an abstract opening proof -/

/-- The checked proof as the abstract `OpeningProof` at its round count — total. -/
private def Ipa.Proof.toOpening {C : CommitmentCurve} {k : ℕ} (p : Ipa.Proof C k) :
    OpeningProof C.ScalarField C.Point k where
  lr := fun j => p.lr[j]
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
private theorem msm_eq_commitGen {n : ℕ} (g : Fin n → C.Point) (a : Fin n → C.ScalarField) :
    msm C g a = commitGen g a := by
  simp only [Ipa.msm, commitGen]
  exact Finset.sum_congr rfl (fun i _ => (hsmul (a i) (g i)).symm)

omit [Module C.ScalarField C.Point] in
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

include hsmul in
/-- The executable combination of a checked commitment vector is `combinedCommitment`
of its indexed function. -/
private theorem combineCommitments_toArray_eq (ξ : C.ScalarField) {m : ℕ}
    (cs : Vector C.Point m) :
    combineCommitments C ξ cs.toArray
      = combinedCommitment ξ (fun i : Fin m => cs[i]) := by
  rw [combineCommitments_eq hsmul, combinedCommitment, combinedCommitment]
  exact Fintype.sum_equiv (finCongr (by simp)) _ _ fun i => rfl

omit [Module C.ScalarField C.Point] in
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

omit [Module C.ScalarField C.Point] in
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
`BatchAccepts {σ with U := U} proof ξ r c chal commitments xs evals`, the checked data
entering through its total named views. -/
theorem verify_reflects (σ : SRS C.Point) {m p : ℕ} (inp : Ipa.Input C σ.k m p)
    (hv : Ipa.verify C σ inp = true) :
    BatchAccepts { σ with U := (transcript C inp).1 }
      inp.proof.toOpening
      inp.polyscale inp.evalscale
      (transcript C inp).2.2
      (fun i => (transcript C inp).2.1[i])
      inp.commitmentFn inp.pointFn inp.evalFn := by
  simp only [Ipa.transcript]
  simp only [Ipa.verify, Ipa.verifyFrom, Ipa.verifyWith] at hv
  rw [Bool.and_eq_true] at hv
  obtain ⟨hsch, hsg⟩ := hv
  rw [decide_eq_true_eq] at hsch hsg
  refine ⟨?_, ?_⟩
  · rw [zipFold_eq_recombine _ inp.proof.lr.toArray
        (transcriptFrom C Poseidon.FqSponge.init inp).2.1.toArray σ.k
        (by simp) (by simp)] at hsch
    rw [combineCommitments_toArray_eq hsmul] at hsch
    unfold Bulletproof.recombine Ipa.Proof.toOpening
    simp only [hsmul]
    simpa using hsch
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
axiom poseidon_fiat_shamir_vesta (σ : SRS IpaVesta.Point) {m p : ℕ}
    (inp : IpaVesta.Input σ.k m p) :
  FiatShamirTreeB σ
    (combinedCommitment inp.polyscale inp.commitmentFn)
    (combinedEvalVector (2 ^ σ.k) inp.evalscale inp.pointFn)
    (cipOf inp)
    (Ipa.verify IpaVesta.curve σ inp = true)

/-- **AXIOM (Fiat-Shamir, Poseidon instantiation, Pallas).** The Pallas-side twin of
`poseidon_fiat_shamir_vesta`. -/
axiom poseidon_fiat_shamir_pallas (σ : SRS IpaPallas.Point) {m p : ℕ}
    (inp : IpaPallas.Input σ.k m p) :
  FiatShamirTreeB σ
    (combinedCommitment inp.polyscale inp.commitmentFn)
    (combinedEvalVector (2 ^ σ.k) inp.evalscale inp.pointFn)
    (cipOf inp)
    (Ipa.verify IpaPallas.curve σ inp = true)

/-! ## The headline -/

/-- The flattened segment stream of a chunked family, as the checked vector:
polynomial-outer, chunk-inner (`finSigmaFinEquiv`), the deployed `combine_commitments`
order. -/
def segmentStream {α : Type*} {n : ℕ} {nc : Fin n → ℕ}
    (f : (i : Fin n) → Fin (nc i) → α) : Vector α (∑ i, nc i) :=
  Vector.ofFn fun s => f (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2

section ChunkedHeadline

variable {Cc : CommitmentCurve} [Module Cc.ScalarField Cc.Point]

/-- The Fiat-Shamir axiom's flat tree, reshaped to the chunked combiners of the segment
stream through the flattening lemmas. Generic over the curve bundle; the per-curve
headlines instantiate it at their axiom. -/
private theorem fs_tree_chunked
    (ax : ∀ (σ : SRS Cc.Point) {m p : ℕ} (inp : Ipa.Input Cc σ.k m p),
      FiatShamirTreeB σ
        (combinedCommitment inp.polyscale inp.commitmentFn)
        (combinedEvalVector (2 ^ σ.k) inp.evalscale inp.pointFn)
        (cipOf inp)
        (Ipa.verify Cc σ inp = true))
    (σ : SRS Cc.Point) {n : ℕ} {nc : Fin n → ℕ}
    (C : (i : Fin n) → Fin (nc i) → Cc.Point)
    {p : ℕ} (xs : Vector Cc.ScalarField p)
    (e : (i : Fin n) → Fin (nc i) → Fin p → Cc.ScalarField)
    (ξ rr : Cc.ScalarField) (proof : Ipa.Proof Cc σ.k) :
    FiatShamirTreeB σ (chunkedCombinedCommitment ξ C)
      (combinedEvalVector (2 ^ σ.k) rr fun j : Fin p => xs[j])
      (chunkedCombinedInnerProduct ξ rr e)
      (Ipa.verify Cc σ
        (mkInput (segmentStream C) xs
          (segmentStream fun i c => Vector.ofFn (e i c)) ξ rr proof) = true) := by
  set inp : Ipa.Input Cc σ.k (∑ i, nc i) p :=
    mkInput (segmentStream C) xs
      (segmentStream fun i c => Vector.ofFn (e i c)) ξ rr proof with hinp
  have h := ax σ inp
  have hC : combinedCommitment inp.polyscale inp.commitmentFn
      = chunkedCombinedCommitment ξ C := by
    rw [chunkedCombinedCommitment_eq_flat, combinedCommitment, combinedCommitment]
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    simp [hinp, Ipa.Input.commitmentFn, Ipa.mkInput, segmentStream]
  have hcip : cipOf inp = chunkedCombinedInnerProduct ξ rr e := by
    rw [chunkedCombinedInnerProduct_eq_flat, cipOf, combinedInnerProduct,
      combinedInnerProduct]
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp [hinp, Ipa.Input.evalFn, Ipa.mkInput, segmentStream]
  rw [hC, hcip] at h
  exact h

end ChunkedHeadline

