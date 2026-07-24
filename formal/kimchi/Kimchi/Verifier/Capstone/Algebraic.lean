import Mathlib
import Kimchi.Verifier.Reduction.Soundness

/-!
# The algebraic-prover corollary and the algebraic quotient (the AGM reading)

The algebraic-group-model reading of `kimchiProof_sound`
(`Kimchi/Verifier/Reduction/Soundness.lean`),
the sibling of the standard-model capstones in `Capstone/Standard.lean`.

The **algebraic-prover corollary** `kimchiProof_sound_algebraic` quantifies over provers
that SUPPLY SRS-basis representations `aw₀`/`ρw₀` of their committed rows (the
algebraic-group-model idiom), so a SINGLE accepted IPA opening suffices — no grid, no
density. The content delivered here: representations + ONE accepted opening ⟹ the per-row
eval pins (`eval_pins_of_opening`), replacing the special-soundness grid; the pins land in
`kimchiProof_sound_of_openings`' consumer verbatim. Two new bad axes appear — the
combination challenges `(ξ, r)` — with proved-small bad sets (`badXiOf`/`badROf`,
≤ `2·(44·nc − 1)` and ≤ 1, counting SZ via `SZ.badComb`), curried by the consumer data
`(E, ζ)`/`(E, ζ, ξ)` so they are quantified BEFORE `(ξ, r)`. Honest scope note: this
corollary KEEPS the
ft/quotient identity `hteq` (and `t`, `t.natDegree`) as a hypothesis — the same residue as
the run-level capstones.

The **algebraic quotient** dissolves that residue: `kimchiProof_sound_algebraic_ft`. The
algebraic prover additionally supplies the 7 `tComm`-chunk representations, and the quotient
`t` — the genuine degree-`< 7n` assembly `ftChunkAssembly` of the committed chunks — and
the Maller/ft identity `hteq` are DERIVED from a checked ft opening via
`ft_identity_of_chunks`; the residue hypotheses disappear from the statement. What stays
hypothetical is unchanged from the AGM corollary: the ft opening itself (discharged for
the deployed verifier by `ft_opening_of_reflected_{vesta,pallas}` in
`Capstone/Reflection.lean`, from the `kimchi_fiat_shamir_{vesta,pallas}` axioms),
DL-binding, the key correspondence, and the per-transcript Fiat–Shamir families.

The five workhorses the Fiat–Shamir-reflection roots reuse across the module boundary —
`badXiOf`, `badROf`, `eval_pins_of_opening`, `ftChunkAssembly`, `ft_identity_of_chunks` —
are module-public here (consumed by `Capstone/Reflection.lean`); the counting and
degree lemmas that only support them stay `private`.
-/

open Bulletproof

namespace Kimchi.Verifier

open Polynomial Bulletproof Kimchi.Index Kimchi.Protocol.Linearization
  Kimchi.Protocol.Equation CompElliptic.Fields.Pasta

/-! ## The algebraic-prover corollary (the AGM reading)

An ALGEBRAIC prover carries, with each commitment it sends, an SRS-basis representation
of the committed data — here the witness pairs `aw₀`/`ρw₀` with
`commit σ (aw₀ i) (ρw₀ i) = batchC wC zC comms i`. Those representations discharge the
REFERENCE side of `kimchiProof_sound_of_openings` outright, and the bridge below
(`eval_pins_of_opening`) discharges its CONSUMER side from ONE accepted batch opening:
by commitment linearity the combined commitment is the commitment of the ξ-combined
representation; by binding the opened witness IS that combination; substituting into the
opening's value equation leaves the single field identity
`∑ i, ξ^i · (∑ j, D i j · r^j) = 0` in the discrepancies
`D i j = E i j − ⟨aw₀ i, evalVector (x j)⟩`, and two counting-Schwartz–Zippel steps
(`SZ.badComb`, first at `r`, then at `ξ`) kill every `D i j` — the eval pins. The bad
`(ξ, r)` sets are COUNTED, never assumed: `badXiOf` (≤ `2·(m − 1)` at `m` flat segments)
depends only on `(σ, aw₀, x, E)`, `badROf` (≤ 1 = 2−1) additionally on `ξ` — neither
mentions the challenge it guards, which is what lets the capstones quantify them
BEFORE `(ξ, r)`. -/

/-- The bad row-combination challenges of one claimed-vs-represented evaluation matrix:
the union over the two eval points of the counting-SZ bad sets of the discrepancy
columns `i ↦ E i j − ⟨aw₀ i, evalVector (x j)⟩`. Depends only on `(σ, aw₀, x, E)` —
never on `ξ` or `r` (anti-vacuity: the capstone quantifies it before both). Arity-generic
(`Fin m` rows): the AGM capstones use it at the flattened 44-row `batchC` (`44·nc`
segments), the FS-reflection layer at the reflected run's own `44·nc + 1`-segment flat
batch (45 at `nc = 1`). -/
noncomputable def badXiOf {F G : Type*} [Field F] [DecidableEq F]
    (σ : SRS G) {m : ℕ} (aw₀ : Fin m → Fin (2 ^ σ.k) → F)
    (x : Fin evalPts → F) (E : Fin m → Fin evalPts → F) : Finset F :=
  Kimchi.SZ.badComb
      (fun i : Fin m => E i 0 - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x 0)))
    ∪ Kimchi.SZ.badComb
      (fun i : Fin m => E i 1 - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x 1)))

/-- The bad point-combination challenges at a fixed `ξ`: the counting-SZ bad set of the
two ξ-combined discrepancy columns. Depends on `(σ, aw₀, x, E, ξ)` — never on `r`. -/
noncomputable def badROf {F G : Type*} [Field F] [DecidableEq F]
    (σ : SRS G) {m : ℕ} (aw₀ : Fin m → Fin (2 ^ σ.k) → F)
    (x : Fin evalPts → F) (E : Fin m → Fin evalPts → F) (ξ : F) : Finset F :=
  Kimchi.SZ.badComb (fun j : Fin evalPts => ∑ i : Fin m,
    ξ ^ (i : ℕ) * (E i j - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j))))

/-- `badXiOf` counts at most `2 · (m − 1)` challenges (at the flattened batch's `44·nc`
segments: `2·(44·nc − 1)`): a union of two counting-SZ bad sets over `Fin m`. -/
theorem card_badXiOf_le {F G : Type*} [Field F] [DecidableEq F]
    (σ : SRS G) {m : ℕ} (aw₀ : Fin m → Fin (2 ^ σ.k) → F)
    (x : Fin evalPts → F) (E : Fin m → Fin evalPts → F) :
    (badXiOf σ aw₀ x E).card ≤ 2 * (m - 1) := by
  unfold badXiOf
  refine le_trans (Finset.card_union_le _ _) ?_
  have h0 := Kimchi.SZ.card_badComb_le
    (fun i : Fin m => E i 0 - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x 0)))
  have h1 := Kimchi.SZ.card_badComb_le
    (fun i : Fin m => E i 1 - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x 1)))
  omega

/-- `badROf` counts at most `1 = 2 − 1` challenge: one counting-SZ bad set over
`Fin evalPts`. -/
theorem card_badROf_le {F G : Type*} [Field F] [DecidableEq F]
    (σ : SRS G) {m : ℕ} (aw₀ : Fin m → Fin (2 ^ σ.k) → F)
    (x : Fin evalPts → F) (E : Fin m → Fin evalPts → F) (ξ : F) :
    (badROf σ aw₀ x E ξ).card ≤ 1 := by
  unfold badROf
  exact Kimchi.SZ.card_badComb_le _

/-- **The eval pins from one opening** (the AGM bridge): SRS-basis representations of
the `m` batch rows plus ONE accepted batch opening at good `(ξ, r)` pin every claimed
evaluation to the represented row's true evaluation. Linearity collapses the combined
commitment to one commitment of the ξ-combined representation (`commitₗ`, `map_sum`);
binding (`hbind`, through `commitmentBinding_iff_no_relation`) forces the opened witness
to BE that combination; the opening's value equation then reduces to
`∑ j, r^j · (∑ i, ξ^i · D i j) = 0` in the discrepancies `D`, and
`SZ.eq_zero_of_comb_eq_zero` — first at `r`, then per point at `ξ` — kills every
`D i j`. Arity-generic: the AGM capstones consume it at the flattened 44-row `batchC`
(`44·nc` segments), the FS-reflection layer at the reflected run's own
`44·nc + 1`-segment flat batch (45 at `nc = 1`). -/
theorem eval_pins_of_opening {F G : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (wh : F), DLRelation σ w wh → w = 0 ∧ wh = 0)
    {m : ℕ} (C : Fin m → G) (x : Fin evalPts → F)
    (aw₀ : Fin m → Fin (2 ^ σ.k) → F) (ρw₀ : Fin m → F)
    (hrep : ∀ i, commit σ (aw₀ i) (ρw₀ i) = C i)
    (E : Fin m → Fin evalPts → F) (ξ r : F)
    (hξ : ξ ∉ badXiOf σ aw₀ x E) (hr : r ∉ badROf σ aw₀ x E ξ)
    (a : Fin (2 ^ σ.k) → F) (ρ : F)
    (hopen : openingRelationB σ (combinedCommitment ξ C)
      (combinedEvalVector (2 ^ σ.k) r x) (combinedInnerProduct ξ r E) a ρ) :
    ∀ (i : Fin m) (j : Fin evalPts),
      E i j = innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j)) := by
  -- Step A (linearity): the combined commitment is ONE commitment of the ξ-combined
  -- representation — `map_sum` of `commitₗ` at `Fin m`, mirroring `commit_combine`.
  have hpair : (∑ i : Fin m, ξ ^ (i : ℕ)
        • ((aw₀ i, ρw₀ i) : (Fin (2 ^ σ.k) → F) × F))
      = (∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i, ∑ i : Fin m, ξ ^ (i : ℕ) • ρw₀ i) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      exact Finset.sum_congr rfl fun i _ => rfl
    · rw [Prod.snd_sum]
      exact Finset.sum_congr rfl fun i _ => rfl
  have hA : combinedCommitment ξ C
      = commit σ (∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i)
          (∑ i : Fin m, ξ ^ (i : ℕ) • ρw₀ i) := by
    calc combinedCommitment ξ C
        = ∑ i : Fin m, ξ ^ (i : ℕ) • commit σ (aw₀ i) (ρw₀ i) := by
          unfold combinedCommitment
          exact Finset.sum_congr rfl fun i _ => by rw [hrep i]
      _ = commitₗ σ (∑ i : Fin m, ξ ^ (i : ℕ)
            • ((aw₀ i, ρw₀ i) : (Fin (2 ^ σ.k) → F) × F)) := by
          rw [map_sum]
          simp only [map_smul]
          rfl
      _ = commit σ (∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i)
            (∑ i : Fin m, ξ ^ (i : ℕ) • ρw₀ i) := by rw [hpair]; rfl
  -- Step B (binding): the opened witness IS the ξ-combined representation — the
  -- interior of `bound_unique`, kept at witness level via `congrArg Prod.fst`.
  have hbd : CommitmentBinding (F := F) σ :=
    (commitmentBinding_iff_no_relation σ).mpr hbind
  have hcommit : commit σ a ρ
      = commit σ (∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i)
          (∑ i : Fin m, ξ ^ (i : ℕ) • ρw₀ i) := hopen.1.trans hA
  have ha : a = ∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i :=
    congrArg Prod.fst (@hbd (a, ρ)
      (∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i, ∑ i : Fin m, ξ ^ (i : ℕ) • ρw₀ i) hcommit)
  -- Step C (substitute + expand): the value equation becomes the double-sum identity
  -- `∑ j, r^j · (∑ i, ξ^i · D i j) = 0` in the discrepancies `D`.
  have hip : ∀ b : Fin (2 ^ σ.k) → F,
      innerProduct (∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i) b
        = ∑ i : Fin m, ξ ^ (i : ℕ) * innerProduct (aw₀ i) b := by
    intro b
    unfold innerProduct
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  have h1 : combinedInnerProduct ξ r E
      = ∑ j : Fin evalPts, r ^ (j : ℕ)
          * ∑ i : Fin m, ξ ^ (i : ℕ)
              * innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j)) := by
    rw [hopen.2, ha, innerProduct_combinedEvalVector]
    exact Finset.sum_congr rfl fun j _ => by rw [hip]
  have h2 : combinedInnerProduct ξ r E
      = ∑ j : Fin evalPts, r ^ (j : ℕ) * ∑ i : Fin m, ξ ^ (i : ℕ) * E i j := by
    unfold combinedInnerProduct
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hsum : ∑ j : Fin evalPts, r ^ (j : ℕ) * (∑ i : Fin m, ξ ^ (i : ℕ)
      * (E i j - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j)))) = 0 := by
    calc ∑ j : Fin evalPts, r ^ (j : ℕ) * (∑ i : Fin m, ξ ^ (i : ℕ)
          * (E i j - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j))))
        = (∑ j : Fin evalPts, r ^ (j : ℕ) * ∑ i : Fin m, ξ ^ (i : ℕ) * E i j)
          - ∑ j : Fin evalPts, r ^ (j : ℕ) * ∑ i : Fin m, ξ ^ (i : ℕ)
              * innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← mul_sub, ← Finset.sum_sub_distrib]
          refine congrArg (r ^ (j : ℕ) * ·)
            (Finset.sum_congr rfl fun i _ => ?_)
          ring
      _ = 0 := by rw [← h2, ← h1, sub_self]
  -- Step D (iterated counting SZ): first at `r` (the two point-columns), then per
  -- point at `ξ` (the `m` row-discrepancies).
  simp only [badROf] at hr
  have hcol : ∀ j : Fin evalPts, ∑ i : Fin m, ξ ^ (i : ℕ)
      * (E i j - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j))) = 0 :=
    Kimchi.SZ.eq_zero_of_comb_eq_zero _ r hr hsum
  simp only [badXiOf, Finset.notMem_union] at hξ
  intro i j
  have hj : ξ ∉ Kimchi.SZ.badComb (fun i : Fin m =>
      E i j - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j))) := by
    fin_cases j
    · exact hξ.1
    · exact hξ.2
  exact sub_eq_zero.mp (Kimchi.SZ.eq_zero_of_comb_eq_zero _ ξ hj (hcol j) i)

end Kimchi.Verifier

/-!
# The algebraic-prover corollaries, over the 44-row reduction

The AGM corollaries over the 44-row reduction (`Reduction/Soundness.lean`): the
algebraic prover supplies SRS-basis representations of every batch row's CHUNKS, one
accepted opening of the combined claim discharges the consumer side, and the
counting-SZ bad sets live at the FLAT segment arity `∑ _ : Fin batchRows, nc`
(`badXiOf`/`badROf` are arity-generic — the flattening equiv `finSigmaFinEquiv`
carries the chunk families to the flat batch the opening actually combines, exactly
as inside `chunked_batch_soundness`).

The algebraic quotient (verifier.rs:960–965): the ft row's commitment collapses BOTH
sides at `ζ^{2^σ.k}` — the `f_comm` side is `pScalar` times the `nc`-chunk `σ₆`
commitment chunk-combined (at `nc = 1` this collapse is the identity), and the
quotient side is the `nt ≤ 7·nc`-chunk `t_comm` combination. `ftChunkAssembly` takes
the chunk count as a parameter; `ft_identity_of_chunks` derives the degree bound
`< 7n` and the Maller identity with the `σ₆`-side collapse resolved through per-chunk
binding.
-/

open Bulletproof

namespace Kimchi.Verifier

open Polynomial Bulletproof Kimchi.Index Kimchi.Protocol.Linearization
  Kimchi.Protocol.Equation Kimchi.Verifier

variable {F G : Type*}

/-! ## Flattening the chunk families -/

/-- The chunked combined commitment is the flat combination of the flattened family. -/
private theorem chunkedCommitment_eq_flatten [Field F] [AddCommGroup G] [Module F G]
    {m nc : ℕ} (ξ : F) (C : Fin m → Fin nc → G) :
    chunkedCombinedCommitment ξ C = combinedCommitment ξ (flatten C) :=
  chunkedCombinedCommitment_eq_flat ξ C

/-- The chunked combined inner product is the flat combination of the flattened
claims. -/
private theorem chunkedInnerProduct_eq_flatten [Field F] {m nc mm : ℕ} (ξ r : F)
    (e : Fin m → Fin nc → Fin mm → F) :
    chunkedCombinedInnerProduct ξ r e = combinedInnerProduct ξ r (flatten e) :=
  chunkedCombinedInnerProduct_eq_flat ξ r e

/-! ## The algebraic-prover corollary -/

/-- **Chunked algebraic-prover soundness from ONE transcript**: representations of the
44 batch rows' chunks discharge the chunked openings interface on both sides — the
reference side outright, the consumer side from a single accepted opening of the
chunked combined claim via `ipa_soundnessA` + `eval_pins_of_opening` at the FLAT
segment family. The `(ξ, r)` bad sets are counted at the flat arity:
`badXi ≤ 2·(∑ nc − 1)`, `badR ≤ 1`. The quotient identity `hteq` remains a
hypothesis — dissolved by the `_ft` variant below. -/
theorem kimchiProof_sound_algebraic [Field F] [AddCommGroup G]
    [Module F G] {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) {nc : ℕ} (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms (Fin nc → G)) (hvk : VKCorresponds σ nc comms idx)
    (pub : Fin idx.publicCount → F)
    (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (hpubC : ∀ c : Fin nc,
      pubC c = commitPolyMaskedChunk σ (-(idx.pubPoly pub)) (c : ℕ))
    (aw₀ : Fin batchRows → Fin nc → Fin (2 ^ σ.k) → F) (ρw₀ : Fin batchRows → Fin nc → F)
    (hrep : ∀ i c, commit σ (aw₀ i c) (ρw₀ i c) = batchC wC zC pubC comms i c) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F)
        (badZ : F → F → F → Polynomial F → Finset F)
        (badXi : (Fin batchRows → Fin nc → Fin evalPts → F) → F → Finset F)
        (badR : (Fin batchRows → Fin nc → Fin evalPts → F) → F → F → Finset F),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial F), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n)
        ∧ (∀ (E : Fin batchRows → Fin nc → Fin evalPts → F) (ζ : F),
            (badXi E ζ).card ≤ 2 * ((∑ _ : Fin batchRows, nc) - 1))
        ∧ (∀ (E : Fin batchRows → Fin nc → Fin evalPts → F) (ζ ξ : F), (badR E ζ ξ).card ≤ 1))
      ∧ ∀ (β γ α : F) (t : Polynomial F) (ζ : F)
          (E : Fin batchRows → Fin nc → Fin evalPts → F) (ξ r : F) (A : Prop),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          ξ ∉ badXi E ζ → r ∉ badR E ζ ξ →
          FiatShamirTreeB σ
            (chunkedCombinedCommitment ξ (batchC wC zC pubC comms))
            (combinedEvalVector (2 ^ σ.k) r ![ζ, idx.omega * ζ])
            (chunkedCombinedInnerProduct ξ r E) A →
          A →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ)
              (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds α β γ
                ζ (claimedPub (ζ ^ 2 ^ σ.k) E)
                (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)) →
          Satisfies idx pub
            (extractTable idx.omega fun col => assembledRow σ.k nc (aw₀ (wRow col))) := by
  obtain ⟨⟨hB, hG, hA, hZ⟩, himp⟩ :=
    kimchiProof_sound_of_openings σ idx hnc hk hbind comms hvk pub wC zC pubC hpubC
      aw₀ ρw₀ hrep
  refine ⟨_, _, _, _,
    fun E ζ => badXiOf σ (flatten aw₀) ![ζ, idx.omega * ζ] (flatten E),
    fun E ζ ξ => badROf σ (flatten aw₀) ![ζ, idx.omega * ζ] (flatten E) ξ,
    ⟨hB, hG, hA, hZ,
      fun E ζ => card_badXiOf_le σ (flatten aw₀) ![ζ, idx.omega * ζ] (flatten E),
      fun E ζ ξ => card_badROf_le σ (flatten aw₀) ![ζ, idx.omega * ζ] (flatten E) ξ⟩,
    ?_⟩
  intro β γ α t ζ E ξ r A hβ hγ hα hζ hζ1 hζb ht hξ hr hFS hAcc hteq
  rw [chunkedCommitment_eq_flatten, chunkedInnerProduct_eq_flatten] at hFS
  obtain ⟨a, ρ, hopen⟩ := ipa_soundnessA σ _ _ _ hFS hAcc
  have hpins := eval_pins_of_opening σ hbind (flatten (batchC wC zC pubC comms))
    ![ζ, idx.omega * ζ] (flatten aw₀) (flatten ρw₀)
    (fun s => hrep (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2)
    (flatten E) ξ r hξ hr a ρ hopen
  refine himp β γ α t ζ E aw₀ ρw₀ hβ hγ hα hζ hζ1 hζb ht (fun i c => ⟨hrep i c, ?_⟩)
    hteq
  intro j
  have h := hpins (finSigmaFinEquiv ⟨i, c⟩) j
  simpa only [flatten, Equiv.symm_apply_apply] using h

/-! ## The algebraic quotient, chunked -/

/-- **The assembled quotient** at `nt` committed chunks (the deployed `t_comm` carries
up to `7·nc`): chunk `j` contributes its row polynomial shifted by `X^(j·2^k)`. -/
noncomputable def ftChunkAssembly [Field F] (k nt : ℕ)
    (aT : Fin nt → Fin (2 ^ k) → F) : Polynomial F :=
  ∑ j : Fin nt, rowPoly (aT j) * Polynomial.X ^ ((j : ℕ) * 2 ^ k)

/-- The assembly meets the chunk-count degree bound `nt · 2^k`. -/
theorem ftChunkAssembly_natDegree_lt [Field F] (k : ℕ) {nt : ℕ} (hnt : 0 < nt)
    (aT : Fin nt → Fin (2 ^ k) → F) :
    (ftChunkAssembly k nt aT).natDegree < nt * 2 ^ k := by
  have h2k : 0 < 2 ^ k := Nat.two_pow_pos k
  have hle : (ftChunkAssembly k nt aT).natDegree ≤ nt * 2 ^ k - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    refine le_trans (natDegree_mul_le) ?_
    rw [natDegree_X_pow]
    have hrow := rowPoly_natDegree_lt_two_pow (aT j)
    have hj : (j : ℕ) ≤ nt - 1 := by have := j.isLt; omega
    have hjm : (j : ℕ) * 2 ^ k ≤ (nt - 1) * 2 ^ k := Nat.mul_le_mul_right _ hj
    have : (nt - 1) * 2 ^ k + 2 ^ k = nt * 2 ^ k := by
      have hnt1 : nt - 1 + 1 = nt := by omega
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, hnt1]
    omega
  have hpos : 0 < nt * 2 ^ k := Nat.mul_pos hnt h2k
  omega

/-- The assembly evaluates as the `(ζ^(2^k))`-power combination of the chunk-row
evaluations. -/
private theorem ftChunkAssembly_eval [Field F] (k nt : ℕ)
    (aT : Fin nt → Fin (2 ^ k) → F) (ζ : F) :
    (ftChunkAssembly k nt aT).eval ζ
      = ∑ j : Fin nt, (ζ ^ 2 ^ k) ^ (j : ℕ) * (rowPoly (aT j)).eval ζ := by
  unfold ftChunkAssembly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_pow, eval_X, mul_comm ((j : ℕ)) (2 ^ k), pow_mul]
  ring

/-- A chunk commitment is the hiding commitment of the chunk's coefficient window at
blinder `0` — the shape binding consumes. -/
private theorem commitPolyChunk_eq_commit [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) (p : Polynomial F) (c : ℕ) :
    commitPolyChunk σ p c = commit σ (chunkCoeffs (2 ^ σ.k) p c) 0 := by
  rw [commitPolyChunk, commitPoly_eq_commit]
  congr 1
  funext i
  show (chunkPoly (2 ^ σ.k) p c).coeff (i : ℕ) = p.coeff (c * 2 ^ σ.k + (i : ℕ))
  unfold chunkPoly
  simp only [finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single (i : ℕ)]
  · rw [if_pos rfl]
  · intro j _ hj
    exact if_neg fun h => hj h
  · intro h
    exact absurd (Finset.mem_range.mpr i.isLt) h

/-- **The Maller/ft identity from the chunk representations, chunked**
(verifier.rs:960–965): the deployed ft row's commitment collapses BOTH sides at
`ζ^{2^σ.k}` — `pScalar` times the chunk-combined `nc`-chunk `σ₆` commitment (real
algebra at `nc > 1`; at `nc = 1` the collapse is the identity), minus `(ζ^n − 1)` times
the chunk-combined `nt`-chunk quotient commitment. Representations of the `nt` chunks
plus the opened ft row pin, via binding, the opened witness to the pointwise
combination; reading it through `rowPoly` yields the assembled quotient's degree bound
`< 7n` (from `nt ≤ 7·nc` and `nc · 2^σ.k = n`) and the ft equation at
`t = ftChunkAssembly σ.k nt aT`. The `σ₆` side needs no representations: its chunk
commitments are unblinded fixed columns, so their combination is the commitment of the
chunk-combined coefficient windows outright. -/
theorem ft_identity_of_chunks [Field F] [AddCommGroup G]
    [Module F G] (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {nc : ℕ}
    (σ₆ : Polynomial F) (hσ₆ : σ₆.natDegree < nc * 2 ^ σ.k)
    (Cσ6 : Fin nc → G) (hC : ∀ c : Fin nc, Cσ6 c = commitPolyChunk σ σ₆ (c : ℕ))
    {nt : ℕ} (hnt0 : 0 < nt) (hnt : nt ≤ 7 * nc)
    (TC : Fin nt → G) (aT : Fin nt → Fin (2 ^ σ.k) → F) (ρT : Fin nt → F)
    (htc : ∀ j, commit σ (aT j) (ρT j) = TC j)
    (pScalar ζ v0 : F) (n : ℕ) (hk : nc * 2 ^ σ.k = n)
    (a : Fin (2 ^ σ.k) → F) (ρ : F)
    (hcommit : commit σ a ρ
      = pScalar • ∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ) • Cσ6 c
        - (ζ ^ n - 1) • ∑ j : Fin nt, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • TC j)
    (heval : innerProduct a (evalVector (2 ^ σ.k) ζ) = v0) :
    (ftChunkAssembly σ.k nt aT).natDegree < 7 * n
      ∧ pScalar * σ₆.eval ζ - (ζ ^ n - 1) * (ftChunkAssembly σ.k nt aT).eval ζ = v0 := by
  -- Step A: σ₆'s per-chunk commitment witnesses — the coefficient windows at blinder 0.
  set w6 : Fin nc → Fin (2 ^ σ.k) → F :=
    fun c => chunkCoeffs (2 ^ σ.k) σ₆ (c : ℕ) with hw6
  have hC6 : ∀ c : Fin nc, Cσ6 c = commit σ (w6 c) 0 := fun c =>
    (hC c).trans (commitPolyChunk_eq_commit σ σ₆ (c : ℕ))
  have hip6 : ∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ)
      * innerProduct (w6 c) (evalVector (2 ^ σ.k) ζ) = σ₆.eval ζ := by
    rw [eval_eq_sum_chunkPoly _ hσ₆ ζ, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun c _ => by rw [chunkPoly_eval]
  -- Step B: the ft commitment as ONE commitment of the pointwise-combined witness.
  set b : Fin (2 ^ σ.k) → F :=
    pScalar • ∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ) • w6 c
      - (ζ ^ n - 1) • ∑ j : Fin nt, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • aT j with hb
  set ρb : F :=
    -((ζ ^ n - 1) • ∑ j : Fin nt, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • ρT j) with hρb
  have hpair : ((b, ρb) : (Fin (2 ^ σ.k) → F) × F)
      = pScalar • ∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ)
            • ((w6 c, 0) : (Fin (2 ^ σ.k) → F) × F)
        - (ζ ^ n - 1) • ∑ j : Fin nt, (ζ ^ 2 ^ σ.k) ^ (j : ℕ)
            • ((aT j, ρT j) : (Fin (2 ^ σ.k) → F) × F) := by
    refine Prod.ext ?_ ?_
    · simp only [hb, Prod.fst_sub, Prod.smul_fst, Prod.fst_sum]
    · simp only [hρb, Prod.snd_sub, Prod.smul_snd, Prod.snd_sum, smul_zero,
        Finset.sum_const_zero, smul_zero, zero_sub]
  have hB : commit σ b ρb
      = pScalar • ∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ) • Cσ6 c
        - (ζ ^ n - 1) • ∑ j : Fin nt, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • TC j := by
    have h0 : commit σ b ρb = commitₗ σ (b, ρb) := rfl
    rw [h0, hpair, map_sub, map_smul, map_smul, map_sum, map_sum]
    congr 2
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smul]
      refine congrArg _ ?_
      show commit σ (w6 c) 0 = Cσ6 c
      exact (hC6 c).symm
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      exact congrArg _ (htc j)
  -- Step C: binding — the opened row IS the combination.
  have hbd : CommitmentBinding (F := F) σ :=
    (commitmentBinding_iff_no_relation σ).mpr hbind
  have hab : a = b :=
    congrArg Prod.fst (@hbd (a, ρ) (b, ρb) (hcommit.trans hB.symm))
  have hdeg : (ftChunkAssembly σ.k nt aT).natDegree < 7 * n := by
    have h := ftChunkAssembly_natDegree_lt σ.k hnt0 aT
    have h2 : nt * 2 ^ σ.k ≤ 7 * (nc * 2 ^ σ.k) := by
      rw [← mul_assoc]
      exact Nat.mul_le_mul_right _ hnt
    rw [hk] at h2
    omega
  refine ⟨hdeg, ?_⟩
  -- Step D: expand the inner product of `b` linearly and conclude.
  have hipL : ∀ {m : ℕ} (u : Fin m → Fin (2 ^ σ.k) → F),
      innerProduct (∑ j : Fin m, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • u j)
        (evalVector (2 ^ σ.k) ζ)
      = ∑ j : Fin m, (ζ ^ 2 ^ σ.k) ^ (j : ℕ)
          * innerProduct (u j) (evalVector (2 ^ σ.k) ζ) := by
    intro m u
    unfold innerProduct
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  have hsub : innerProduct b (evalVector (2 ^ σ.k) ζ)
      = pScalar * innerProduct (∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ) • w6 c)
            (evalVector (2 ^ σ.k) ζ)
        - (ζ ^ n - 1)
          * innerProduct (∑ j : Fin nt, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • aT j)
              (evalVector (2 ^ σ.k) ζ) := by
    rw [hb]
    unfold innerProduct
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [← heval, hab, hsub, hipL, hipL, hip6, ftChunkAssembly_eval]
  simp only [rowPoly_eval]

/-- **Chunked algebraic-prover soundness, residue-free**: the algebraic prover
additionally supplies the `nt ≤ 7·nc` `tComm`-chunk representations, and the quotient
and Maller identity are DERIVED from the checked ft opening via
`ft_identity_of_chunks` — the deployed ft row's double collapse at `ζ^{2^σ.k}`. The
`σ₆` chunk commitments come straight from the corresponding key columns
(`hCσ6 = comms.sigma 6`, discharged by `hvk` at the honest chunked indexer). The
residue-free chunked AGM root. -/
theorem kimchiProof_sound_algebraic_ft [Field F] [AddCommGroup G]
    [Module F G] {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) {nc : ℕ} (hnc : 0 < nc) (hk : nc * 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms (Fin nc → G)) (hvk : VKCorresponds σ nc comms idx)
    (pub : Fin idx.publicCount → F)
    (wC : Fin wCols → Fin nc → G) (zC pubC : Fin nc → G)
    (hpubC : ∀ c : Fin nc,
      pubC c = commitPolyMaskedChunk σ (-(idx.pubPoly pub)) (c : ℕ))
    (aw₀ : Fin batchRows → Fin nc → Fin (2 ^ σ.k) → F) (ρw₀ : Fin batchRows → Fin nc → F)
    (hrep : ∀ i c, commit σ (aw₀ i c) (ρw₀ i c) = batchC wC zC pubC comms i c)
    {nt : ℕ} (hnt0 : 0 < nt) (hnt : nt ≤ 7 * nc)
    (TC : Fin nt → G) (aT : Fin nt → Fin (2 ^ σ.k) → F) (ρT : Fin nt → F)
    (hTC : ∀ j, commit σ (aT j) (ρT j) = TC j) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F)
        (badZ : F → F → F → Polynomial F → Finset F)
        (badXi : (Fin batchRows → Fin nc → Fin evalPts → F) → F → Finset F)
        (badR : (Fin batchRows → Fin nc → Fin evalPts → F) → F → F → Finset F),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial F), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n)
        ∧ (∀ (E : Fin batchRows → Fin nc → Fin evalPts → F) (ζ : F),
            (badXi E ζ).card ≤ 2 * ((∑ _ : Fin batchRows, nc) - 1))
        ∧ (∀ (E : Fin batchRows → Fin nc → Fin evalPts → F) (ζ ξ : F), (badR E ζ ξ).card ≤ 1))
      ∧ ∀ (β γ α ζ : F)
          (E : Fin batchRows → Fin nc → Fin evalPts → F) (ξ r : F) (A : Prop)
          (aft : Fin (2 ^ σ.k) → F) (ρft : F),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ →
          ζ ∉ badZ β γ α (ftChunkAssembly σ.k nt aT) →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          ξ ∉ badXi E ζ → r ∉ badR E ζ ξ →
          FiatShamirTreeB σ
            (chunkedCombinedCommitment ξ (batchC wC zC pubC comms))
            (combinedEvalVector (2 ^ σ.k) r ![ζ, idx.omega * ζ])
            (chunkedCombinedInnerProduct ξ r E) A →
          A →
          (commit σ aft ρft
            = permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ)
                (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)
                • ∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ) • comms.sigma 6 c
              - (ζ ^ n - 1) • ∑ j : Fin nt, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • TC j) →
          (innerProduct aft (evalVector (2 ^ σ.k) ζ)
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds α β γ
                ζ (claimedPub (ζ ^ 2 ^ σ.k) E)
                (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)) →
          Satisfies idx pub
            (extractTable idx.omega fun col => assembledRow σ.k nc (aw₀ (wRow col))) := by
  obtain ⟨badB, badG, badA, badZ, badXi, badR, hbounds, himp⟩ :=
    kimchiProof_sound_algebraic σ idx hnc hk hbind comms hvk pub wC zC pubC hpubC
      aw₀ ρw₀ hrep
  refine ⟨badB, badG, badA, badZ, badXi, badR, hbounds, ?_⟩
  intro β γ α ζ E ξ r A aft ρft hβ hγ hα hζ hζ1 hζb hξ hr hFS hAcc hftc hftv
  have hσ₆ : (idx.sigmaPoly 6).natDegree < nc * 2 ^ σ.k := by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  have hCσ6 : ∀ c : Fin nc,
      comms.sigma 6 c = commitPolyChunk σ (idx.sigmaPoly 6) (c : ℕ) := by
    intro c
    have h : comms = indexerOf σ nc idx := hvk
    rw [h]
    rfl
  obtain ⟨htdeg, hteq⟩ := ft_identity_of_chunks σ hbind (idx.sigmaPoly 6) hσ₆
    (comms.sigma 6) hCσ6 hnt0 hnt TC aT ρT hTC
    (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ)
      (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)) ζ
    (ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase idx.mds α β γ ζ
      (claimedPub (ζ ^ 2 ^ σ.k) E)
      (claimedEvals (ζ ^ 2 ^ σ.k) ((idx.omega * ζ) ^ 2 ^ σ.k) E)) n hk aft ρft
    hftc hftv
  exact himp β γ α (ftChunkAssembly σ.k nt aT) ζ E ξ r A hβ hγ hα hζ hζ1 hζb htdeg
    hξ hr hFS hAcc hteq

end Kimchi.Verifier
