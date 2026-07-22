import Mathlib
import Kimchi.Verifier.Reduction.Soundness
import Kimchi.Verifier.Capstone.Algebraic
import Kimchi.Verifier.Kimchi
import Kimchi.Verifier.Reflect

/-!
# The concrete Fiat–Shamir capstones (standard model)

The special-soundness grid `KimchiBatchAcc` accumulates deployed acceptances of the
batch — the wire commitment array pinned SEGMENT-wise to the flat stream of the
44-row chunked assembly (`flatten (batchC …)`, the order the deployed verifier's
`combined_inner_product` walks), one grid node per flat segment × eval point. Each
node's `FiatShamirTreeB` family is derived from the node's own deployed acceptance via
the per-node `poseidon_fiat_shamir_*` axiom, transported to the chunk combiners
through the `_eq_flat` flattening lemmas — the same `hcip` move as `ipaVesta_sound`.

Trust story: the grid is a HYPOTHESIS (the forking/rewinding idiom, posited outright),
one FS axiom per node, everything else proved. The run-level corollaries live in the
reflection layer (they instantiate the consumer at the deployed verifier's own sponge
challenges).
-/

open Bulletproof

namespace Kimchi.Verifier

open Polynomial Bulletproof Kimchi.Index Kimchi.Protocol.Linearization
  Kimchi.Protocol.Equation CompElliptic.Fields.Pasta Kimchi.Verifier

/-! ## Reindexing congruences for the batched combiners -/

/-- `combinedCommitment` congruence across an index-count equality. -/
private theorem combinedCommitment_reindex {F G : Type*} [Field F] [AddCommGroup G]
    [Module F G] (ξ : F) {n m : ℕ} (h : n = m) (Cn : Fin n → G) (Cm : Fin m → G)
    (hC : ∀ i : Fin n, Cn i = Cm (Fin.cast h i)) :
    combinedCommitment ξ Cn = combinedCommitment ξ Cm := by
  unfold combinedCommitment
  refine Fintype.sum_equiv (finCongr h) _ _ fun i => ?_
  simp only [finCongr_apply, Fin.val_cast]
  rw [hC i]

/-- `combinedInnerProduct` congruence across a first-index-count equality. -/
private theorem combinedInnerProduct_reindex {F : Type*} [Field F] (ξ r : F)
    {n n' m : ℕ} (h : n = n') (e : Fin n → Fin m → F) (e' : Fin n' → Fin m → F)
    (he : ∀ (i : Fin n) (j : Fin m), e i j = e' (Fin.cast h i) j) :
    combinedInnerProduct ξ r e = combinedInnerProduct ξ r e' := by
  unfold combinedInnerProduct
  refine Fintype.sum_equiv (finCongr h) _ _ fun i => ?_
  simp only [finCongr_apply, Fin.val_cast]
  refine congrArg (ξ ^ (i : ℕ) * ·) ?_
  exact Finset.sum_congr rfl fun j _ => by rw [he i j]

/-! ## The accumulated grid — the special-soundness hypothesis -/

/-- **The chunked accumulated grid**: per `(ξ₀ s, r₀ j)`-node a deployed `Ipa.verify`
acceptance of the SAME chunked batched claim — the opaque wire commitment array pinned
segment-by-segment to the flat stream of `batchC wC zC pubC comms`, the wire evaluation
matrix carrying the flat per-chunk claims, the two eval points `(ζ₀, ω·ζ₀)`. Posited
outright, never derived from one run (the forking/rewinding idiom). -/
structure KimchiBatchAcc (C : Ipa.CommitmentCurve) [Module C.ScalarField C.Point]
    {n : ℕ} [NeZero n] (σ : SRS C.Point) (idx : Index C.ScalarField n) (nc : ℕ)
    (comms : IndexComms (Fin nc → C.Point)) (wC : Fin 15 → Fin nc → C.Point) where
  /-- The accumulator (`z`) commitment chunks of the reference transcript. -/
  zC : Fin nc → C.Point
  /-- The public commitment chunks of the reference transcript. -/
  pubC : Fin nc → C.Point
  /-- The reference evaluation point. -/
  ζ₀ : C.ScalarField
  /-- The per-chunk claimed evaluations of the 44-row batch at `ζ₀` and `ω·ζ₀`. -/
  E₀ : Fin 44 → Fin nc → Fin 2 → C.ScalarField
  /-- The segment-combination challenges of the grid. -/
  ξ₀ : Fin (segTotal nc) → C.ScalarField
  /-- Distinctness of the segment-combination challenges. -/
  hξ₀ : Function.Injective ξ₀
  /-- The point-combination challenges of the grid. -/
  r₀ : Fin 2 → C.ScalarField
  /-- Distinctness of the point-combination challenges. -/
  hr₀ : Function.Injective r₀
  /-- The checked commitment vector of the batch — opaque. -/
  cs : Vector C.Point (segTotal nc)
  /-- Segment-by-segment, the checked vector is the flat stream of the chunked
  assembly. -/
  hcs : ∀ s : Fin (segTotal nc), cs[s] = flatSeg (batchC wC zC pubC comms) s
  /-- The checked evaluation matrix of the batch — opaque. -/
  es : Vector (Vector C.ScalarField 2) (segTotal nc)
  /-- Entry-by-entry, the checked matrix carries the flat claims. -/
  hes : ∀ (s : Fin (segTotal nc)) (j : Fin 2), (es[s])[j] = flatSeg E₀ s j
  /-- Per grid node, the node's IPA opening proof at the SRS's round count. -/
  prf : Fin (segTotal nc) → Fin 2 → Ipa.Proof C σ.k
  /-- The deployed verifier accepts every node's batched input. -/
  hacc : ∀ (s : Fin (segTotal nc)) (j : Fin 2),
    Ipa.verify C σ (Ipa.mkInput cs ⟨#[ζ₀, idx.omega * ζ₀], rfl⟩ es (ξ₀ s) (r₀ j)
      (prf s j)) = true

section BatchOfAcc

variable {C : Ipa.CommitmentCurve} [Module C.ScalarField C.Point] {n : ℕ} [NeZero n]
  {σ : SRS C.Point} {idx : Index C.ScalarField n} {nc : ℕ}
  {comms : IndexComms (Fin nc → C.Point)} {wC : Fin 15 → Fin nc → C.Point}

/-- The checked input of one grid node. -/
def KimchiBatchAcc.nodeInput (T : KimchiBatchAcc C σ idx nc comms wC)
    (s : Fin (segTotal nc)) (j : Fin 2) : Ipa.Input C σ.k (segTotal nc) 2 :=
  Ipa.mkInput T.cs ⟨#[T.ζ₀, idx.omega * T.ζ₀], rfl⟩ T.es (T.ξ₀ s) (T.r₀ j)
    (T.prf s j)

/-- **Per-node Fiat–Shamir transport, chunked**: the IPA-axiom-shaped transcript-tree
family at a node's wire input, re-expressed over the CHUNKED combiners of the abstract
batch data — the wire array collapses to the flat segment stream (`hcs`), the flat
combination to the chunked combiner (`_eq_flat`), the wire cip to the chunked one
(`hes`). -/
private theorem KimchiBatchAcc.nodeFS (T : KimchiBatchAcc C σ idx nc comms wC)
    (s : Fin (segTotal nc)) (j : Fin 2)
    (hax : FiatShamirTreeB σ
      (combinedCommitment (T.ξ₀ s) (T.nodeInput s j).commitmentFn)
      (combinedEvalVector (2 ^ σ.k) (T.r₀ j) (T.nodeInput s j).pointFn)
      (Ipa.cipOf (T.nodeInput s j))
      (Ipa.verify C σ (T.nodeInput s j) = true)) :
    FiatShamirTreeB σ
      (chunkedCombinedCommitment (T.ξ₀ s) (batchC wC T.zC T.pubC comms))
      (combinedEvalVector (2 ^ σ.k) (T.r₀ j) ![T.ζ₀, idx.omega * T.ζ₀])
      (chunkedCombinedInnerProduct (T.ξ₀ s) (T.r₀ j) T.E₀)
      (Ipa.verify C σ (T.nodeInput s j) = true) := by
  have hsz : segTotal nc = ∑ _ : Fin 44, nc := segTotal_eq_sum nc
  have hP : combinedCommitment (T.ξ₀ s) (T.nodeInput s j).commitmentFn
      = chunkedCombinedCommitment (T.ξ₀ s) (batchC wC T.zC T.pubC comms) := by
    rw [chunkedCombinedCommitment_eq_flat]
    refine combinedCommitment_reindex _ hsz _ _ fun t => ?_
    show T.cs[t] = flatten (batchC wC T.zC T.pubC comms) (Fin.cast hsz t)
    rw [T.hcs t, flatSeg]
    have hidx : finCongr (segTotal_eq_sum nc) t = Fin.cast hsz t := Fin.ext rfl
    rw [hidx]
  have hx : ∀ t : Fin 2, (T.nodeInput s j).pointFn t
      = ![T.ζ₀, idx.omega * T.ζ₀] t := by
    intro t
    fin_cases t <;> rfl
  have hb : combinedEvalVector (2 ^ σ.k) (T.r₀ j) (T.nodeInput s j).pointFn
      = combinedEvalVector (2 ^ σ.k) (T.r₀ j) ![T.ζ₀, idx.omega * T.ζ₀] :=
    congrArg (fun x : Fin 2 → C.ScalarField =>
      combinedEvalVector (2 ^ σ.k) (T.r₀ j) x) (funext hx)
  have hv : Ipa.cipOf (T.nodeInput s j)
      = chunkedCombinedInnerProduct (T.ξ₀ s) (T.r₀ j) T.E₀ := by
    rw [chunkedCombinedInnerProduct_eq_flat]
    show combinedInnerProduct (T.ξ₀ s) (T.r₀ j) (T.nodeInput s j).evalFn
      = combinedInnerProduct (T.ξ₀ s) (T.r₀ j) (flatten T.E₀)
    refine combinedInnerProduct_reindex _ _ hsz _ _ fun t u => ?_
    show (T.es[t])[u] = flatten T.E₀ (Fin.cast hsz t) u
    rw [T.hes t u, flatSeg]
    have hidx : finCongr (segTotal_eq_sum nc) t = Fin.cast hsz t := Fin.ext rfl
    rw [hidx]
  rw [hP, hb, hv] at hax
  exact hax

end BatchOfAcc

/-! ## The concrete capstones -/

/-- **Chunked soundness of the deployed Vesta kimchi verifier**: a chunked
special-soundness grid at the wire key's committed chunk columns (`vk.comms nc`) yields
the bad sets and the guarded consumer implication of the chunked
`kimchiProof_sound` — each node's `FiatShamirTreeB` derived from
`poseidon_fiat_shamir_vesta` at the node's own deployed input. -/
theorem kimchiVesta_sound (σ : SRS IpaVesta.Point)
    (pub : Array Fp) {n : ℕ} [NeZero n] (idx : Index Fp n)
    {nc : ℕ} (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n)
    (cvk : KimchiVK IpaVesta.curve nc)
    (hvk : VKCorresponds σ nc cvk.comms idx)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → Fin nc → IpaVesta.Point)
    (T : KimchiBatchAcc IpaVesta.curve σ idx nc cvk.comms wC)
    (hpubC : ∀ c : Fin nc,
      T.pubC c = commitPolyMaskedChunk σ (-(idx.pubPoly (pubView idx pub))) (c : ℕ)) :
    ∃ (badB : Finset Fp) (badG : Fp → Finset Fp) (badA : Fp → Fp → Finset Fp)
        (badZ : Fp → Fp → Fp → Polynomial Fp → Finset Fp)
        (wTab : Fin n → Fin 15 → Fp),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fp), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ∀ (β γ α : Fp) (t : Polynomial Fp) (ζ : Fp)
          (E : Fin 44 → Fin nc → Fin 2 → Fp)
          (ξ : Fin (segTotal nc) → Fp) (r : Fin 2 → Fp)
          (A : Fin (segTotal nc) → Fin 2 → Prop),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          Function.Injective ξ → Function.Injective r →
          (∀ s j,
            FiatShamirTreeB σ
              (chunkedCombinedCommitment (ξ s) (batchC wC T.zC T.pubC cvk.comms))
              (combinedEvalVector (2 ^ σ.k) (r j) ![ζ, idx.omega * ζ])
              (chunkedCombinedInnerProduct (ξ s) (r j) E) (A s j)) →
          (∀ s j, A s j) →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ)
              (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds α β γ
                ζ (claimedPub (ζ ^ 2 ^ σ.k) E)
                (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)) →
          Satisfies idx (pubView idx pub) wTab :=
  kimchiProof_sound σ idx hnc hk hbind cvk.comms hvk (pubView idx pub) wC
    T.zC T.pubC hpubC T.ζ₀ T.E₀ T.ξ₀ T.hξ₀ T.r₀ T.hr₀
    (fun s j => Ipa.verify IpaVesta.curve σ (T.nodeInput s j) = true)
    (fun s j => T.nodeFS s j (poseidon_fiat_shamir_vesta σ (T.nodeInput s j)))
    (fun s j => T.hacc s j)

/-- **Chunked soundness of the deployed Pallas kimchi verifier.** The Pallas twin. -/
theorem kimchiPallas_sound (σ : SRS IpaPallas.Point)
    (pub : Array Fq) {n : ℕ} [NeZero n] (idx : Index Fq n)
    {nc : ℕ} (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n)
    (cvk : KimchiVK IpaPallas.curve nc)
    (hvk : VKCorresponds σ nc cvk.comms idx)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → Fin nc → IpaPallas.Point)
    (T : KimchiBatchAcc IpaPallas.curve σ idx nc cvk.comms wC)
    (hpubC : ∀ c : Fin nc,
      T.pubC c = commitPolyMaskedChunk σ (-(idx.pubPoly (pubView idx pub))) (c : ℕ)) :
    ∃ (badB : Finset Fq) (badG : Fq → Finset Fq) (badA : Fq → Fq → Finset Fq)
        (badZ : Fq → Fq → Fq → Polynomial Fq → Finset Fq)
        (wTab : Fin n → Fin 15 → Fq),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fq), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ∀ (β γ α : Fq) (t : Polynomial Fq) (ζ : Fq)
          (E : Fin 44 → Fin nc → Fin 2 → Fq)
          (ξ : Fin (segTotal nc) → Fq) (r : Fin 2 → Fq)
          (A : Fin (segTotal nc) → Fin 2 → Prop),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          Function.Injective ξ → Function.Injective r →
          (∀ s j,
            FiatShamirTreeB σ
              (chunkedCombinedCommitment (ξ s) (batchC wC T.zC T.pubC cvk.comms))
              (combinedEvalVector (2 ^ σ.k) (r j) ![ζ, idx.omega * ζ])
              (chunkedCombinedInnerProduct (ξ s) (r j) E) (A s j)) →
          (∀ s j, A s j) →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ)
              (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds α β γ
                ζ (claimedPub (ζ ^ 2 ^ σ.k) E)
                (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)) →
          Satisfies idx (pubView idx pub) wTab :=
  kimchiProof_sound σ idx hnc hk hbind cvk.comms hvk (pubView idx pub) wC
    T.zC T.pubC hpubC T.ζ₀ T.E₀ T.ξ₀ T.hξ₀ T.r₀ T.hr₀
    (fun s j => Ipa.verify IpaPallas.curve σ (T.nodeInput s j) = true)
    (fun s j => T.nodeFS s j (poseidon_fiat_shamir_pallas σ (T.nodeInput s j)))
    (fun s j => T.hacc s j)

/-! ## The run-level corollaries — the standard-model finale -/

/-- **Chunked run-level soundness of the deployed Vesta kimchi verifier**: the grid
capstone's consumer implication instantiated at a real chunked run's own sponge
challenges — the literal `runOracles` fields — over the run's own commitment
chunks. The consumer grid `T'` shares the accumulator and public commitments and sits
at the run's own `ζ`; its Fiat–Shamir trees, acceptances, and challenge injectivity
discharge the capstone's transcript antecedents. The quotient residue
`(t, hdeg, heq)` stays the one undischarged antecedent, exactly as at `nc = 1` (its
dissolution is the `_ft` terminal's job). -/
theorem kimchiVesta_run_sound (σ : SRS IpaVesta.Point) {nc : ℕ} (hnc : 0 < nc)
    (pub : Array Fp) {n : ℕ} [NeZero n]
    (idx : Index Fp n)
    (hk : nc * 2 ^ σ.k = n)
    (cvk : KimchiVK IpaVesta.curve (nc))
    (cp : KimchiProof IpaVesta.curve nc σ.k)
    (hvk : VKCorresponds σ (nc) cvk.comms idx)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (T : KimchiBatchAcc IpaVesta.curve σ idx (nc)
      cvk.comms
      (fun i c => (cp.wComm[i])[c]))
    (T' : KimchiBatchAcc IpaVesta.curve σ idx (nc)
      cvk.comms
      (fun i c => (cp.wComm[i])[c]))
    (hzC : T'.zC = T.zC) (hpC : T'.pubC = T.pubC)
    (hpubC : ∀ c, T.pubC c
      = commitPolyMaskedChunk σ (-(idx.pubPoly (pubView idx pub))) (c : ℕ))
    (hζ' : T'.ζ₀ = (runOracles IpaVesta.curve σ cvk cp pub).zeta)
    (hζ1 : (runOracles IpaVesta.curve σ cvk cp pub).zeta ≠ 1)
    (hζb : (runOracles IpaVesta.curve σ cvk cp pub).zeta
      ≠ idx.omega ^ (n - idx.zkRows))
    (t : Polynomial Fp) (hdeg : t.natDegree < 7 * n)
    (heq :
      permScalar (runOracles IpaVesta.curve σ cvk cp pub).beta
          (runOracles IpaVesta.curve σ cvk cp pub).gamma
          (runOracles IpaVesta.curve σ cvk cp pub).alpha
          (zkpmEval n idx.zkRows idx.omega (runOracles IpaVesta.curve σ cvk cp pub).zeta)
          (claimedEvals ((runOracles IpaVesta.curve σ cvk cp pub).zeta ^ 2 ^ σ.k)
            ((idx.omega * (runOracles IpaVesta.curve σ cvk cp pub).zeta) ^ 2 ^ σ.k)
            T'.E₀)
          * (idx.sigmaPoly 6).eval (runOracles IpaVesta.curve σ cvk cp pub).zeta
        - ((runOracles IpaVesta.curve σ cvk cp pub).zeta ^ n - 1)
            * t.eval (runOracles IpaVesta.curve σ cvk cp pub).zeta
        = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds
            (runOracles IpaVesta.curve σ cvk cp pub).alpha
            (runOracles IpaVesta.curve σ cvk cp pub).beta
            (runOracles IpaVesta.curve σ cvk cp pub).gamma
            (runOracles IpaVesta.curve σ cvk cp pub).zeta
            (claimedPub ((runOracles IpaVesta.curve σ cvk cp pub).zeta ^ 2 ^ σ.k) T'.E₀)
            (claimedEvals ((runOracles IpaVesta.curve σ cvk cp pub).zeta ^ 2 ^ σ.k)
              ((idx.omega * (runOracles IpaVesta.curve σ cvk cp pub).zeta) ^ 2 ^ σ.k)
              T'.E₀)) :
    ∃ (badB : Finset Fp) (badG : Fp → Finset Fp) (badA : Fp → Fp → Finset Fp)
        (badZ : Fp → Fp → Fp → Polynomial Fp → Finset Fp)
        (wTab : Fin n → Fin 15 → Fp),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fp), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ((runOracles IpaVesta.curve σ cvk cp pub).beta ∉ badB →
          (runOracles IpaVesta.curve σ cvk cp pub).gamma
            ∉ badG (runOracles IpaVesta.curve σ cvk cp pub).beta →
          (runOracles IpaVesta.curve σ cvk cp pub).alpha
            ∉ badA (runOracles IpaVesta.curve σ cvk cp pub).beta
                (runOracles IpaVesta.curve σ cvk cp pub).gamma →
          (runOracles IpaVesta.curve σ cvk cp pub).zeta
            ∉ badZ (runOracles IpaVesta.curve σ cvk cp pub).beta
                (runOracles IpaVesta.curve σ cvk cp pub).gamma
                (runOracles IpaVesta.curve σ cvk cp pub).alpha t →
          Satisfies idx (pubView idx pub) wTab) := by
  obtain ⟨badB, badG, badA, badZ, wTab, hbounds, himp⟩ :=
    kimchiVesta_sound σ pub idx hnc hk cvk hvk hbind
      (fun i c => (cp.wComm[i])[c]) T hpubC
  refine ⟨badB, badG, badA, badZ, wTab, hbounds, fun hβ hγ hα hζ => ?_⟩
  refine himp (runOracles IpaVesta.curve σ cvk cp pub).beta
    (runOracles IpaVesta.curve σ cvk cp pub).gamma
    (runOracles IpaVesta.curve σ cvk cp pub).alpha t
    (runOracles IpaVesta.curve σ cvk cp pub).zeta
    T'.E₀ T'.ξ₀ T'.r₀
    (fun s j => Ipa.verify IpaVesta.curve σ (T'.nodeInput s j) = true)
    hβ hγ hα hζ hζ1 hζb hdeg T'.hξ₀ T'.hr₀ ?_ T'.hacc heq
  intro s j
  have h := T'.nodeFS s j (poseidon_fiat_shamir_vesta σ (T'.nodeInput s j))
  simp only [hzC, hpC, hζ'] at h
  exact h

/-- **Chunked run-level soundness of the deployed Pallas kimchi verifier.** The Pallas
twin of `kimchiVesta_run_sound`. -/
theorem kimchiPallas_run_sound (σ : SRS IpaPallas.Point) {nc : ℕ} (hnc : 0 < nc)
    (pub : Array Fq) {n : ℕ} [NeZero n]
    (idx : Index Fq n)
    (hk : nc * 2 ^ σ.k = n)
    (cvk : KimchiVK IpaPallas.curve (nc))
    (cp : KimchiProof IpaPallas.curve nc σ.k)
    (hvk : VKCorresponds σ (nc) cvk.comms idx)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (T : KimchiBatchAcc IpaPallas.curve σ idx (nc)
      cvk.comms
      (fun i c => (cp.wComm[i])[c]))
    (T' : KimchiBatchAcc IpaPallas.curve σ idx (nc)
      cvk.comms
      (fun i c => (cp.wComm[i])[c]))
    (hzC : T'.zC = T.zC) (hpC : T'.pubC = T.pubC)
    (hpubC : ∀ c, T.pubC c
      = commitPolyMaskedChunk σ (-(idx.pubPoly (pubView idx pub))) (c : ℕ))
    (hζ' : T'.ζ₀ = (runOracles IpaPallas.curve σ cvk cp pub).zeta)
    (hζ1 : (runOracles IpaPallas.curve σ cvk cp pub).zeta ≠ 1)
    (hζb : (runOracles IpaPallas.curve σ cvk cp pub).zeta
      ≠ idx.omega ^ (n - idx.zkRows))
    (t : Polynomial Fq) (hdeg : t.natDegree < 7 * n)
    (heq :
      permScalar (runOracles IpaPallas.curve σ cvk cp pub).beta
          (runOracles IpaPallas.curve σ cvk cp pub).gamma
          (runOracles IpaPallas.curve σ cvk cp pub).alpha
          (zkpmEval n idx.zkRows idx.omega
            (runOracles IpaPallas.curve σ cvk cp pub).zeta)
          (claimedEvals ((runOracles IpaPallas.curve σ cvk cp pub).zeta ^ 2 ^ σ.k)
            ((idx.omega * (runOracles IpaPallas.curve σ cvk cp pub).zeta) ^ 2 ^ σ.k)
            T'.E₀)
          * (idx.sigmaPoly 6).eval (runOracles IpaPallas.curve σ cvk cp pub).zeta
        - ((runOracles IpaPallas.curve σ cvk cp pub).zeta ^ n - 1)
            * t.eval (runOracles IpaPallas.curve σ cvk cp pub).zeta
        = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds
            (runOracles IpaPallas.curve σ cvk cp pub).alpha
            (runOracles IpaPallas.curve σ cvk cp pub).beta
            (runOracles IpaPallas.curve σ cvk cp pub).gamma
            (runOracles IpaPallas.curve σ cvk cp pub).zeta
            (claimedPub ((runOracles IpaPallas.curve σ cvk cp pub).zeta ^ 2 ^ σ.k)
              T'.E₀)
            (claimedEvals ((runOracles IpaPallas.curve σ cvk cp pub).zeta ^ 2 ^ σ.k)
              ((idx.omega * (runOracles IpaPallas.curve σ cvk cp pub).zeta) ^ 2 ^ σ.k)
              T'.E₀)) :
    ∃ (badB : Finset Fq) (badG : Fq → Finset Fq) (badA : Fq → Fq → Finset Fq)
        (badZ : Fq → Fq → Fq → Polynomial Fq → Finset Fq)
        (wTab : Fin n → Fin 15 → Fq),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial Fq), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ((runOracles IpaPallas.curve σ cvk cp pub).beta ∉ badB →
          (runOracles IpaPallas.curve σ cvk cp pub).gamma
            ∉ badG (runOracles IpaPallas.curve σ cvk cp pub).beta →
          (runOracles IpaPallas.curve σ cvk cp pub).alpha
            ∉ badA (runOracles IpaPallas.curve σ cvk cp pub).beta
                (runOracles IpaPallas.curve σ cvk cp pub).gamma →
          (runOracles IpaPallas.curve σ cvk cp pub).zeta
            ∉ badZ (runOracles IpaPallas.curve σ cvk cp pub).beta
                (runOracles IpaPallas.curve σ cvk cp pub).gamma
                (runOracles IpaPallas.curve σ cvk cp pub).alpha t →
          Satisfies idx (pubView idx pub) wTab) := by
  obtain ⟨badB, badG, badA, badZ, wTab, hbounds, himp⟩ :=
    kimchiPallas_sound σ pub idx hnc hk cvk hvk hbind
      (fun i c => (cp.wComm[i])[c]) T hpubC
  refine ⟨badB, badG, badA, badZ, wTab, hbounds, fun hβ hγ hα hζ => ?_⟩
  refine himp (runOracles IpaPallas.curve σ cvk cp pub).beta
    (runOracles IpaPallas.curve σ cvk cp pub).gamma
    (runOracles IpaPallas.curve σ cvk cp pub).alpha t
    (runOracles IpaPallas.curve σ cvk cp pub).zeta
    T'.E₀ T'.ξ₀ T'.r₀
    (fun s j => Ipa.verify IpaPallas.curve σ (T'.nodeInput s j) = true)
    hβ hγ hα hζ hζ1 hζb hdeg T'.hξ₀ T'.hr₀ ?_ T'.hacc heq
  intro s j
  have h := T'.nodeFS s j (poseidon_fiat_shamir_pallas σ (T'.nodeInput s j))
  simp only [hzC, hpC, hζ'] at h
  exact h

end Kimchi.Verifier
