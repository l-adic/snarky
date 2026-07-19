import Kimchi.Protocol.Soundness

/-!
# The idealized composition: `KimchiBundle` and `kimchiBundle_sound`

Repackages the transcript-side hypotheses of `kimchiProof_sound` as one structure
(`KimchiBundle`) and restates the core as `kimchiBundle_sound` — the idealized
soundness statement in the special-soundness idiom: the bundle is the accepting-
transcripts HYPOTHESIS, discharged later by the concrete Fiat–Shamir capstone.
-/

open Bulletproof

namespace Kimchi.Protocol

open Polynomial Bulletproof Kimchi.Index Kimchi.Protocol.Linearization

/-! ## The transcript bundle -/

/-- The transcript-side hypothesis bundle of `kimchiProof_sound`: the accumulator
commitment `zC` and the single accepting reference transcript at the reference point
`ζ₀` — its claimed evaluations `E₀`, its injective batch challenges `ξ₀`/`r₀`, its
acceptance predicates `A₀`, the per-point `FiatShamirTreeB` family `hFS₀`, and the
acceptances `hacc₀`. Field types are verbatim from the binder list of
`kimchiProof_sound`; the witness commitments `wC` are a structure PARAMETER (fixed
across the whole bundle, as across the whole challenge grid of the core). Project-local:
this is the packaging the concrete capstone instantiates. -/
structure KimchiBundle {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    {n : ℕ} [NeZero n] (σ : SRS G) (idx : Index F n) (pub : Fin idx.publicCount → F)
    (comms : IndexComms G) (wC : Fin 15 → G) where
  /-- The accumulator (`z`) commitment of the reference transcript. -/
  zC : G
  /-- The reference evaluation point. -/
  ζ₀ : F
  /-- The claimed evaluations of the 43-row batch at `ζ₀` and `ω·ζ₀`. -/
  E₀ : Fin 43 → Fin 2 → F
  /-- The row-combination challenges of the reference batch. -/
  ξ₀ : Fin 43 → F
  /-- Distinctness of the row-combination challenges. -/
  hξ₀ : Function.Injective ξ₀
  /-- The point-combination challenges of the reference batch. -/
  r₀ : Fin 2 → F
  /-- Distinctness of the point-combination challenges. -/
  hr₀ : Function.Injective r₀
  /-- The acceptance predicates of the reference batch, per challenge pair. -/
  A₀ : Fin 43 → Fin 2 → Prop
  /-- The per-point Fiat–Shamir transcript-tree family of the reference batch. -/
  hFS₀ : ∀ (i : Fin 43) (j : Fin 2),
    FiatShamirTreeB σ (combinedCommitment (ξ₀ i) (batchC wC zC comms))
      (combinedEvalVector (2 ^ σ.k) (r₀ j) ![ζ₀, idx.omega * ζ₀])
      (combinedInnerProduct (ξ₀ i) (r₀ j) E₀) (A₀ i j)
  /-- The verifier accepts at every challenge pair. -/
  hacc₀ : ∀ i j, A₀ i j

/-! ## The idealized composition -/

/-- **The bundle closes the circuit** (idealized composition): a `KimchiBundle`,
DL-binding (`hbind`), the SRS-width pin (`hk`), and the verifier-key correspondence
(`hvk`) yield the four bad sets and the guarded consumer implication of
`kimchiProof_sound` — byte-identical, ending in `∃ wTab, Satisfies idx pub wTab`. The
proof is one application of the core through the bundle's projections. Project-local:
the idealized soundness statement the concrete Fiat–Shamir capstone consumes. -/
theorem kimchiBundle_sound {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) (hk : 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms G) (hvk : VKCorresponds σ comms idx)
    (pub : Fin idx.publicCount → F) (wC : Fin 15 → G)
    (T : KimchiBundle σ idx pub comms wC) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F)
        (badZ : F → F → F → Polynomial F → Finset F),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial F), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n))
      ∧ ∀ (β γ α : F) (t : Polynomial F) (ζ : F)
          (E : Fin 43 → Fin 2 → F) (ξ : Fin 43 → F) (r : Fin 2 → F)
          (A : Fin 43 → Fin 2 → Prop),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          Function.Injective ξ → Function.Injective r →
          (∀ (i : Fin 43) (j : Fin 2),
            FiatShamirTreeB σ (combinedCommitment (ξ i) (batchC wC T.zC comms))
              (combinedEvalVector (2 ^ σ.k) (r j) ![ζ, idx.omega * ζ])
              (combinedInnerProduct (ξ i) (r j) E) (A i j)) →
          (∀ i j, A i j) →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly pub).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → F, Satisfies idx pub wTab :=
  kimchiProof_sound σ idx hk hbind comms hvk pub wC T.zC T.ζ₀ T.E₀ T.ξ₀ T.hξ₀ T.r₀
    T.hr₀ T.A₀ T.hFS₀ T.hacc₀

end Kimchi.Protocol
