import Bulletproof.Wire
import Bulletproof.Soundness
import Pasta

/-!
# Reflection: the executable verifier meets the soundness layer

The bridge between `Bulletproof.Ipa.verify` (executable, over wire data, challenges
derived by the Poseidon sponge) and the `Prop`-level acceptance `BatchAccepts` of the IPA
soundness development — and, through the Fiat-Shamir axiom, the batch knowledge-soundness
theorem itself.

Three strata:

* **The scalar action.** The Pasta point-group module structure (`Pasta/Basic.lean`)
  instantiates the soundness layer's abstract `[Module F G]` at the executable types;
  the action is definitionally `z.val • _`, the ℕ-action the executable verifier
  computes with.

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
  `ipaVesta_sound` composes the axiom, the flattening lemmas, and
  `chunked_batch_soundness`: the claim declares its segment structure (`nc` chunks per
  polynomial), the wire verifier consumes the flattened segment stream
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

/-! ## The wire proof as an abstract opening proof -/

/-- The wire proof, reindexed to the abstract `OpeningProof` at its round count. -/
private def Ipa.Proof.toOpening {C : CommitmentCurve} (p : Ipa.Proof C) {k : ℕ}
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
      unfold Bulletproof.recombine Ipa.Proof.toOpening
      simp only [hsmul, Ipa.transcriptChallenges]
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

/-- The flattened segment stream of a chunked family, as the wire array:
polynomial-outer, chunk-inner (`finSigmaFinEquiv`), the deployed `combine_commitments`
order. -/
private def segmentStream {α : Type*} {n : ℕ} {nc : Fin n → ℕ}
    (f : (i : Fin n) → Fin (nc i) → α) : Array α :=
  Array.ofFn fun s : Fin (∑ i, nc i) =>
    f (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2

section ChunkedHeadline

variable {Cc : CommitmentCurve} [Module Cc.ScalarField Cc.Point]

/-- The Fiat-Shamir axiom's flat tree, reshaped to the chunked combiners of the segment
stream through the flattening lemmas. Generic over the curve bundle; the per-curve
headlines instantiate it at their axiom. -/
private theorem fs_tree_chunked
    (ax : ∀ (σ : SRS Cc.Point) (inp : Ipa.Input Cc),
      FiatShamirTreeB σ
        (combinedCommitment inp.polyscale inp.commitmentFn)
        (combinedEvalVector (2 ^ σ.k) inp.evalscale inp.pointFn)
        (cipOf inp)
        (Ipa.verify Cc σ inp = true))
    (σ : SRS Cc.Point) {n : ℕ} {nc : Fin n → ℕ}
    (C : (i : Fin n) → Fin (nc i) → Cc.Point)
    (xs : Array Cc.ScalarField)
    (e : (i : Fin n) → Fin (nc i) → Fin xs.size → Cc.ScalarField)
    (ξ rr : Cc.ScalarField) (proof : Ipa.Proof Cc) :
    FiatShamirTreeB σ (chunkedCombinedCommitment ξ C)
      (combinedEvalVector (2 ^ σ.k) rr fun j : Fin xs.size => xs[j])
      (chunkedCombinedInnerProduct ξ rr e)
      (Ipa.verify Cc σ
        (mkInput Cc (segmentStream C) xs
          (segmentStream fun i c => Array.ofFn (e i c)) ξ rr proof) = true) := by
  set inp : Ipa.Input Cc :=
    mkInput Cc (segmentStream C) xs
      (segmentStream fun i c => Array.ofFn (e i c)) ξ rr proof with hinp
  have hsz : inp.commitments.size = ∑ i, nc i := Array.size_ofFn ..
  have h := ax σ inp
  have hC : combinedCommitment inp.polyscale inp.commitmentFn
      = chunkedCombinedCommitment ξ C := by
    rw [chunkedCombinedCommitment_eq_flat, combinedCommitment, combinedCommitment]
    refine Finset.sum_equiv (finCongr hsz) (by simp) fun v _ => ?_
    simp only [hinp, Ipa.Input.commitmentFn, Ipa.mkInput, segmentStream,
      finCongr_apply, Fin.val_cast]
    congr 1
    rw [Fin.getElem_fin, Array.getElem_ofFn]
    exact congrArg (fun p : (i : Fin n) × Fin (nc i) => C p.1 p.2)
      (congrArg finSigmaFinEquiv.symm (Fin.ext rfl))
  have hcip : cipOf inp = chunkedCombinedInnerProduct ξ rr e := by
    rw [chunkedCombinedInnerProduct_eq_flat, cipOf, combinedInnerProduct,
      combinedInnerProduct]
    refine Finset.sum_equiv (finCongr hsz) (by simp) fun v _ => ?_
    simp only [hinp, Ipa.Input.evalFn, Ipa.mkInput, segmentStream, finCongr_apply,
      Fin.val_cast]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have hv : (v : ℕ) < ∑ i, nc i := hsz ▸ v.isLt
    have h1 : (Array.ofFn fun s : Fin (∑ i, nc i) =>
          Array.ofFn (e (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2))[(v : ℕ)]!
        = Array.ofFn (e (finSigmaFinEquiv.symm (Fin.cast hsz v)).1
            (finSigmaFinEquiv.symm (Fin.cast hsz v)).2) := by
      rw [getElem!_pos (Array.ofFn _) _ (by simp only [Array.size_ofFn]; exact hv),
        Array.getElem_ofFn]
      exact congrArg (fun p : (i : Fin n) × Fin (nc i) => Array.ofFn (e p.1 p.2))
        (congrArg finSigmaFinEquiv.symm (Fin.ext rfl))
    rw [h1, getElem!_pos (Array.ofFn _) _ (by simp only [Array.size_ofFn]; exact j.isLt),
      Array.getElem_ofFn]
    exact congrArg _ (Fin.ext rfl)
  rw [hC, hcip] at h
  exact h

end ChunkedHeadline

/-- **Soundness of the deployed Vesta verifier, at the declared chunk structure.** The
claim carries its segment structure: `n` polynomials with chunk counts `nc`, chunk
commitments `C i c`, and claimed chunk evaluations `e i c j`; the wire verifier consumes
the flattened segment stream. A grid of Poseidon-accepted runs at pairwise-distinct
polyscales `ξ` and evalscales `r`, under the no-DL-relation binding hypothesis, binds
every commitment family to one genuine polynomial: `q i` of degree `< nc i · 2^k`, whose
chunk windows are the committed chunks, whose evaluations recombine the claimed chunk
values, and whose chunk windows reproduce each per-chunk claim individually. Composes
`poseidon_fiat_shamir_vesta`, the flattening lemmas, and
`chunked_batch_soundness`; binding remains a hypothesis (see the module docstring). -/
theorem ipaVesta_sound (σ : SRS IpaVesta.Point) {n : ℕ} {nc : Fin n → ℕ}
    (hnc : ∀ i, 0 < nc i)
    (C : (i : Fin n) → Fin (nc i) → IpaVesta.Point)
    (xs : Array Fp) (hm : 0 < xs.size)
    (e : (i : Fin n) → Fin (nc i) → Fin xs.size → Fp)
    (ξ : Fin (∑ i, nc i) → Fp) (hξ : Function.Injective ξ)
    (r : Fin xs.size → Fp) (hr : Function.Injective r)
    (proofs : Fin (∑ i, nc i) → Fin xs.size → IpaVesta.Proof)
    (hacc : ∀ s t, Ipa.verify IpaVesta.curve σ
      (mkInput IpaVesta.curve (segmentStream C) xs
        (segmentStream fun i c => Array.ofFn (e i c))
        (ξ s) (r t) (proofs s t)) = true)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp),
      DLRelation σ w wh → w = 0 ∧ wh = 0) :
    ∃ q : Fin n → Polynomial Fp, ∀ i,
      (q i).natDegree < nc i * 2 ^ σ.k
        ∧ (∀ c : Fin (nc i), ∃ ρ,
            commit σ (chunkCoeffs (2 ^ σ.k) (q i) (c : ℕ)) ρ = C i c)
        ∧ (∀ j : Fin xs.size, (q i).eval xs[j]
            = ∑ c : Fin (nc i), (xs[j] ^ 2 ^ σ.k) ^ (c : ℕ) * e i c j)
        ∧ ∀ (c : Fin (nc i)) (j : Fin xs.size),
            e i c j = innerProduct (chunkCoeffs (2 ^ σ.k) (q i) (c : ℕ))
              (evalVector (2 ^ σ.k) xs[j]) :=
  chunked_batch_soundness σ hnc ξ hξ r hr hm C (fun j : Fin xs.size => xs[j]) e
    (fun s t => Ipa.verify IpaVesta.curve σ
      (mkInput IpaVesta.curve (segmentStream C) xs
        (segmentStream fun i c => Array.ofFn (e i c)) (ξ s) (r t) (proofs s t)) = true)
    (fun s t => fs_tree_chunked poseidon_fiat_shamir_vesta σ C xs e (ξ s) (r t)
      (proofs s t))
    hbind hacc

/-- **Soundness of the deployed Pallas verifier, at the declared chunk structure.** The
Pallas-side twin of `ipaVesta_sound`. -/
theorem ipaPallas_sound (σ : SRS IpaPallas.Point) {n : ℕ} {nc : Fin n → ℕ}
    (hnc : ∀ i, 0 < nc i)
    (C : (i : Fin n) → Fin (nc i) → IpaPallas.Point)
    (xs : Array Fq) (hm : 0 < xs.size)
    (e : (i : Fin n) → Fin (nc i) → Fin xs.size → Fq)
    (ξ : Fin (∑ i, nc i) → Fq) (hξ : Function.Injective ξ)
    (r : Fin xs.size → Fq) (hr : Function.Injective r)
    (proofs : Fin (∑ i, nc i) → Fin xs.size → IpaPallas.Proof)
    (hacc : ∀ s t, Ipa.verify IpaPallas.curve σ
      (mkInput IpaPallas.curve (segmentStream C) xs
        (segmentStream fun i c => Array.ofFn (e i c))
        (ξ s) (r t) (proofs s t)) = true)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq),
      DLRelation σ w wh → w = 0 ∧ wh = 0) :
    ∃ q : Fin n → Polynomial Fq, ∀ i,
      (q i).natDegree < nc i * 2 ^ σ.k
        ∧ (∀ c : Fin (nc i), ∃ ρ,
            commit σ (chunkCoeffs (2 ^ σ.k) (q i) (c : ℕ)) ρ = C i c)
        ∧ (∀ j : Fin xs.size, (q i).eval xs[j]
            = ∑ c : Fin (nc i), (xs[j] ^ 2 ^ σ.k) ^ (c : ℕ) * e i c j)
        ∧ ∀ (c : Fin (nc i)) (j : Fin xs.size),
            e i c j = innerProduct (chunkCoeffs (2 ^ σ.k) (q i) (c : ℕ))
              (evalVector (2 ^ σ.k) xs[j]) :=
  chunked_batch_soundness σ hnc ξ hξ r hr hm C (fun j : Fin xs.size => xs[j]) e
    (fun s t => Ipa.verify IpaPallas.curve σ
      (mkInput IpaPallas.curve (segmentStream C) xs
        (segmentStream fun i c => Array.ofFn (e i c)) (ξ s) (r t) (proofs s t)) = true)
    (fun s t => fs_tree_chunked poseidon_fiat_shamir_pallas σ C xs e (ξ s) (r t)
      (proofs s t))
    hbind hacc

end Bulletproof
