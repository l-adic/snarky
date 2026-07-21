import Mathlib
import Kimchi.Verifier.Reduction.Chunked
import Kimchi.Verifier.Capstone.Standard
import Kimchi.Verifier.Capstone.AlgebraicChunked
import Kimchi.Verifier.Chunked

/-!
# The concrete Fiat–Shamir capstones, chunked (standard model)

The chunked generalization of `Capstone/Standard.lean`'s grid capstones: the
special-soundness grid `KimchiBatchAcc` now accumulates deployed acceptances of the
chunked batch — the wire commitment array pinned SEGMENT-wise to the flat stream of the
44-row chunked assembly (`flatten (batchC …)`, the order the deployed verifier's
`combined_inner_product` walks), one grid node per flat segment × eval point. Each
node's `FiatShamirTreeB` family is derived from the node's own deployed acceptance via
the per-node `poseidon_fiat_shamir_*` axiom, transported to the CHUNKED combiners
through the `_eq_flat` flattening lemmas — the same `hcip` move as `ipaVesta_sound`.

The trust story is verbatim the `nc = 1` module's (grid = hypothesis, FS axiom per
node, everything else proved); see its preamble. The run-level corollaries move to the
chunked reflection layer (they instantiate the consumer at the CHUNKED verifier's own
sponge challenges).
-/

open Bulletproof

namespace Kimchi.Verifier.Chunked

open Polynomial Bulletproof Kimchi.Index Kimchi.Protocol.Linearization
  Kimchi.Protocol.Equation CompElliptic.Fields.Pasta Kimchi.Verifier

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
  /-- The wire commitment array of the batch — opaque. -/
  cs : Array C.Point
  /-- The wire commitment array has the flat segment count. -/
  hcsSize : cs.size = segTotal nc
  /-- Segment-by-segment, the wire array is the flat stream of the chunked assembly. -/
  hcs : ∀ s : Fin (segTotal nc),
    cs.getD (s : ℕ) 0 = flatSeg (batchC wC zC pubC comms) s
  /-- The wire evaluation matrix of the batch — opaque. -/
  es : Array (Array C.ScalarField)
  /-- Entry-by-entry, the wire matrix carries the flat claims. -/
  hes : ∀ (s : Fin (segTotal nc)) (j : Fin 2),
    (es[(s : ℕ)]!)[(j : ℕ)]! = flatSeg E₀ s j
  /-- Per grid node, the node's IPA opening proof. -/
  prf : Fin (segTotal nc) → Fin 2 → Ipa.Proof C
  /-- The deployed verifier accepts every node's batched input. -/
  hacc : ∀ (s : Fin (segTotal nc)) (j : Fin 2),
    Ipa.verify C σ (Ipa.mkInput C cs #[ζ₀, idx.omega * ζ₀] es (ξ₀ s) (r₀ j) (prf s j))
      = true

section BatchOfAcc

variable {C : Ipa.CommitmentCurve} [Module C.ScalarField C.Point] {n : ℕ} [NeZero n]
  {σ : SRS C.Point} {idx : Index C.ScalarField n} {nc : ℕ}
  {comms : IndexComms (Fin nc → C.Point)} {wC : Fin 15 → Fin nc → C.Point}

/-- The wire input of one grid node. -/
def KimchiBatchAcc.nodeInput (T : KimchiBatchAcc C σ idx nc comms wC)
    (s : Fin (segTotal nc)) (j : Fin 2) : Ipa.Input C :=
  Ipa.mkInput C T.cs #[T.ζ₀, idx.omega * T.ζ₀] T.es (T.ξ₀ s) (T.r₀ j) (T.prf s j)

/-- **Per-node Fiat–Shamir transport, chunked**: the IPA-axiom-shaped transcript-tree
family at a node's wire input, re-expressed over the CHUNKED combiners of the abstract
batch data — the wire array collapses to the flat segment stream (`hcs`), the flat
combination to the chunked combiner (`_eq_flat`), the wire cip to the chunked one
(`hes`). -/
private theorem KimchiBatchAcc.nodeFS (T : KimchiBatchAcc C σ idx nc comms wC)
    (s : Fin (segTotal nc)) (j : Fin 2)
    (hax : FiatShamirTreeB σ
      (combinedCommitment (T.ξ₀ s) (fun t : Fin T.cs.size => T.cs[t]))
      (combinedEvalVector (2 ^ σ.k) (T.r₀ j) (T.nodeInput s j).pointFn)
      (Ipa.cipOf (T.nodeInput s j))
      (Ipa.verify C σ (T.nodeInput s j) = true)) :
    FiatShamirTreeB σ
      (chunkedCombinedCommitment (T.ξ₀ s) (batchC wC T.zC T.pubC comms))
      (combinedEvalVector (2 ^ σ.k) (T.r₀ j) ![T.ζ₀, idx.omega * T.ζ₀])
      (chunkedCombinedInnerProduct (T.ξ₀ s) (T.r₀ j) T.E₀)
      (Ipa.verify C σ (T.nodeInput s j) = true) := by
  have hgetD : ∀ (m : ℕ) (hm : m < T.cs.size), T.cs.getD m 0 = T.cs[m] := by
    intro m hm
    simp [Array.getD, hm]
  have hsz : T.cs.size = ∑ _ : Fin 44, nc := T.hcsSize.trans (segTotal_eq_sum nc)
  have hP : combinedCommitment (T.ξ₀ s) (fun t : Fin T.cs.size => T.cs[t])
      = chunkedCombinedCommitment (T.ξ₀ s) (batchC wC T.zC T.pubC comms) := by
    rw [chunkedCombinedCommitment_eq_flat]
    refine combinedCommitment_reindex _ hsz _ _ fun t => ?_
    show T.cs[(t : ℕ)] = flatten (batchC wC T.zC T.pubC comms) (Fin.cast hsz t)
    rw [← hgetD (t : ℕ) t.isLt]
    have h1 := T.hcs (Fin.cast T.hcsSize t)
    simp only [Fin.val_cast] at h1
    rw [h1, flatSeg]
    have hidx : finCongr (segTotal_eq_sum nc) (Fin.cast T.hcsSize t)
        = Fin.cast hsz t := Fin.ext rfl
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
    show combinedInnerProduct (T.ξ₀ s) (T.r₀ j)
        (fun (t : Fin T.cs.size) (u : Fin 2) => (T.es[(t : ℕ)]!)[(u : ℕ)]!)
      = combinedInnerProduct (T.ξ₀ s) (T.r₀ j) (flatten T.E₀)
    refine combinedInnerProduct_reindex _ _ hsz _ _ fun t u => ?_
    have h1 := T.hes (Fin.cast T.hcsSize t) u
    simp only [Fin.val_cast] at h1
    rw [h1, flatSeg]
    have hidx : finCongr (segTotal_eq_sum nc) (Fin.cast T.hcsSize t)
        = Fin.cast hsz t := Fin.ext rfl
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
theorem kimchiVesta_sound (σ : SRS IpaVesta.Point) (vk : Chunked.KimchiVesta.VK)
    (pub : Array Fp) {n : ℕ} [NeZero n] (idx : Index Fp n)
    {nc : ℕ} (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n)
    (hvk : VKCorresponds σ nc (vk.comms nc) idx)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → Fin nc → IpaVesta.Point)
    (T : KimchiBatchAcc IpaVesta.curve σ idx nc (vk.comms nc) wC)
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
              (chunkedCombinedCommitment (ξ s) (batchC wC T.zC T.pubC (vk.comms nc)))
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
  kimchiProof_sound σ idx hnc hk hbind (vk.comms nc) hvk (pubView idx pub) wC
    T.zC T.pubC hpubC T.ζ₀ T.E₀ T.ξ₀ T.hξ₀ T.r₀ T.hr₀
    (fun s j => Ipa.verify IpaVesta.curve σ (T.nodeInput s j) = true)
    (fun s j => T.nodeFS s j (poseidon_fiat_shamir_vesta σ (T.nodeInput s j)))
    (fun s j => T.hacc s j)

/-- **Chunked soundness of the deployed Pallas kimchi verifier.** The Pallas twin. -/
theorem kimchiPallas_sound (σ : SRS IpaPallas.Point) (vk : Chunked.KimchiPallas.VK)
    (pub : Array Fq) {n : ℕ} [NeZero n] (idx : Index Fq n)
    {nc : ℕ} (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n)
    (hvk : VKCorresponds σ nc (vk.comms nc) idx)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (wC : Fin 15 → Fin nc → IpaPallas.Point)
    (T : KimchiBatchAcc IpaPallas.curve σ idx nc (vk.comms nc) wC)
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
              (chunkedCombinedCommitment (ξ s) (batchC wC T.zC T.pubC (vk.comms nc)))
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
  kimchiProof_sound σ idx hnc hk hbind (vk.comms nc) hvk (pubView idx pub) wC
    T.zC T.pubC hpubC T.ζ₀ T.E₀ T.ξ₀ T.hξ₀ T.r₀ T.hr₀
    (fun s j => Ipa.verify IpaPallas.curve σ (T.nodeInput s j) = true)
    (fun s j => T.nodeFS s j (poseidon_fiat_shamir_pallas σ (T.nodeInput s j)))
    (fun s j => T.hacc s j)

end Kimchi.Verifier.Chunked
