import Kimchi.Verifier.Forking.Escape
import Kimchi.Verifier.Capstone.Reflection

/-!
# W3 · The run-level guard-escape bounds

`RunGuardImp`'s antecedents exclude the run's challenges from the canonical bad sets; the
terminal roots also take the batch guards `hξ`/`hr`. This module states those guard *failures*
as events over a uniform challenge vector — the antecedents verbatim, with the challenge reads
replaced by vector coordinates — and bounds their measure by `Forking.Escape`'s sequential
escape lemmas plus the existing cardinality facts (`RunBounds`, `card_badXiOf_le`,
`card_badROf_le`).

These events are exactly the `S`-families W4 hands to
`Zcash.Snark.uniformOfFintype_fresh_read_bound`: its `O ∘ φ` instantiation at the transcript
prefixes reconnects the coordinates to `runOracles`/`runVU` through `Forking.RunLink`, turning
each bound below into "the deployed run's guards fail with probability ≤ ε" in the
random-oracle model.
-/

namespace Kimchi.Verifier.Forking

open Bulletproof
open scoped ENNReal

variable {C : Ipa.CommitmentCurve} {nc : ℕ}

/-- The fq-side guard-failure event: coordinate `0/1/2/3` is `β/γ/α/ζ`, and each tests the
corresponding `RunGuardImp` antecedent's set — with the two `ζ` boundary points folded into the
`ζ` set. -/
noncomputable def runGuardsFailFq (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) {n : ℕ} [NeZero n]
    (idx : Index C.ScalarField n)
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size → Fin (2 ^ σ.k) → C.ScalarField)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → C.ScalarField) :
    Set (Fin 4 → C.ScalarField) :=
  {χ | χ 0 ∈ Protocol.soundBadB idx (runW σ cvk cp pub aRef)
    ∨ χ 1 ∈ Protocol.soundBadG idx (runW σ cvk cp pub aRef) (χ 0)
    ∨ χ 2 ∈ Protocol.soundBadA idx (pubView idx pub) (runW σ cvk cp pub aRef)
        (runZ σ cvk cp pub aRef) (χ 0) (χ 1)
    ∨ χ 3 ∈ Protocol.soundBadZ idx (pubView idx pub) (runW σ cvk cp pub aRef)
        (runZ σ cvk cp pub aRef) (χ 0) (χ 1) (χ 2)
        (ftChunkAssembly σ.k cp.tComm.size aT)
        ∪ {1, idx.omega ^ (n - idx.zkRows)}}

/-- **The fq escape bound.** Under `RunBounds` (the terminal roots' own cardinality
conclusions) and the chunking side conditions, a uniform `(β, γ, α, ζ)` vector fails some fq
guard with probability at most the summed set bounds (the `+ 2` is the two `ζ` boundary
points) over `|F|`. -/
theorem runGuardsFailFq_measure_le (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) {n : ℕ} [NeZero n]
    (idx : Index C.ScalarField n)
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size → Fin (2 ^ σ.k) → C.ScalarField)
    (aT : Fin cp.tComm.size → Fin (2 ^ σ.k) → C.ScalarField)
    (hB : RunBounds σ cvk cp pub idx aRef)
    (htpos : 0 < cp.tComm.size) (hk : nc * 2 ^ σ.k = n) :
    (PMF.uniformOfFintype (Fin 4 → C.ScalarField)).toOuterMeasure
        (runGuardsFailFq σ cvk cp pub idx aRef aT)
      ≤ (7 * (n - idx.zkRows) + 7 * (n - idx.zkRows)
          + n * (Index.gateAlphaCount + Index.permAlphaCount - 1)
          + (Index.degreeBound n + 2) : ℝ≥0∞) / Fintype.card C.ScalarField := by
  have htdeg : (ftChunkAssembly σ.k cp.tComm.size aT).natDegree < 7 * n := by
    refine lt_of_lt_of_le (ftChunkAssembly_natDegree_lt σ.k htpos aT) ?_
    calc cp.tComm.size * 2 ^ σ.k
        ≤ 7 * nc * 2 ^ σ.k := Nat.mul_le_mul_right _ cp.tComm_le
      _ = 7 * n := by rw [mul_assoc, hk]
  have h := escape4 (b₄ := Index.degreeBound n + 2)
    (Protocol.soundBadB idx (runW σ cvk cp pub aRef))
    (fun β => Protocol.soundBadG idx (runW σ cvk cp pub aRef) β)
    (fun β γ => Protocol.soundBadA idx (pubView idx pub) (runW σ cvk cp pub aRef)
      (runZ σ cvk cp pub aRef) β γ)
    (fun β γ α => Protocol.soundBadZ idx (pubView idx pub) (runW σ cvk cp pub aRef)
      (runZ σ cvk cp pub aRef) β γ α (ftChunkAssembly σ.k cp.tComm.size aT)
      ∪ {1, idx.omega ^ (n - idx.zkRows)})
    hB.1 (fun β => hB.2.1 β) (fun β γ => hB.2.2.1 β γ)
    (fun β γ α => le_trans (Finset.card_union_le _ _)
      (add_le_add (hB.2.2.2 β γ α _ htdeg)
        (le_trans (Finset.card_insert_le _ _) (by simp))))
  refine le_trans h (le_of_eq ?_)
  congr 1
  push_cast [ENNReal.natCast_sub]
  ring

/-- The fr-side guard-failure event: coordinate `0/1` is `v/u` (polyscale/evalscale), testing
the terminal roots' `hξ`/`hr` sets at the run's own batch data. The `ζ`-derived inputs
(`pointFn`/`evalFn`) enter as fixed parameters — the fr sponge runs after `ζ`. -/
noncomputable def runVUFail (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size → Fin (2 ^ σ.k) → C.ScalarField) :
    Set (Fin 2 → C.ScalarField) :=
  {χ | χ 0 ∈ badXiOf σ aRef (runInput C σ cvk cp pub).pointFn
        (runInput C σ cvk cp pub).evalFn
    ∨ χ 1 ∈ badROf σ aRef (runInput C σ cvk cp pub).pointFn
        (runInput C σ cvk cp pub).evalFn (χ 0)}

/-- **The fr escape bound.** A uniform `(v, u)` vector fails `hξ` or `hr` with probability at
most `(2(m − 1) + 1)/|F|` at `m` = the run's flattened batch width. -/
theorem runVUFail_measure_le (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (aRef : Fin (runInput C σ cvk cp pub).commitments.size → Fin (2 ^ σ.k) → C.ScalarField) :
    (PMF.uniformOfFintype (Fin 2 → C.ScalarField)).toOuterMeasure
        (runVUFail σ cvk cp pub aRef)
      ≤ (2 * ((runInput C σ cvk cp pub).commitments.size - 1) + 1 : ℝ≥0∞)
        / Fintype.card C.ScalarField := by
  have h := escape2
    (badXiOf σ aRef (runInput C σ cvk cp pub).pointFn (runInput C σ cvk cp pub).evalFn)
    (fun ξ => badROf σ aRef (runInput C σ cvk cp pub).pointFn
      (runInput C σ cvk cp pub).evalFn ξ)
    (card_badXiOf_le σ aRef _ _) (card_badROf_le σ aRef _ _)
  refine le_trans h (le_of_eq ?_)
  congr 1
  push_cast [ENNReal.natCast_sub]
  ring

end Kimchi.Verifier.Forking
