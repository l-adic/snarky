import Mathlib
import Kimchi.Verifier.Reduction.Soundness
import Kimchi.Verifier.Kimchi
import Bulletproof.Reflection
import Kimchi.Verifier.Reflect

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
combination challenges `(ξ, r)` — with proved-small bad sets (`badXiOf`/`badROf`, ≤ 84 and
≤ 1, counting SZ via `SZ.badComb`), curried by the consumer data `(E, ζ)`/`(E, ζ, ξ)` so
they are quantified BEFORE `(ξ, r)`. Honest scope note: this corollary KEEPS the
ft/quotient identity `hteq` (and `t`, `t.natDegree`) as a hypothesis — the same residue as
the run-level capstones.

The **algebraic quotient** dissolves that residue: `kimchiProof_sound_algebraic_ft`. The
algebraic prover additionally supplies the 7 `tComm`-chunk representations, and the quotient
`t` — now the genuine degree-`< 7n` assembly `ftChunkAssembly` of the committed chunks — and
the Maller/ft identity `hteq` are DERIVED from a checked ft opening via
`ft_identity_of_chunks`; the residue hypotheses disappear from the statement. What stays
hypothetical is unchanged from the AGM corollary: the ft opening itself (which a fully
deployed variant would derive from `poseidon_fiat_shamir` on the ft row), DL-binding, the
key correspondence, and the per-transcript Fiat–Shamir families.

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
`(ξ, r)` sets are COUNTED, never assumed: `badXiOf` (≤ 84 = 2·(43−1)) depends only on
`(σ, aw₀, x, E)`, `badROf` (≤ 1 = 2−1) additionally on `ξ` — neither mentions the
challenge it guards, which is what lets the capstones quantify them BEFORE `(ξ, r)`. -/

/-- The bad row-combination challenges of one claimed-vs-represented evaluation matrix:
the union over the two eval points of the counting-SZ bad sets of the discrepancy
columns `i ↦ E i j − ⟨aw₀ i, evalVector (x j)⟩`. Depends only on `(σ, aw₀, x, E)` —
never on `ξ` or `r` (anti-vacuity: the capstone quantifies it before both). Arity-generic
(`Fin m` rows): the AGM capstones use it at the 43-row `batchC`, the FS-reflection layer
at the reflected run's own 45-row batch. -/
noncomputable def badXiOf {F G : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] (σ : SRS G) {m : ℕ} (aw₀ : Fin m → Fin (2 ^ σ.k) → F)
    (x : Fin 2 → F) (E : Fin m → Fin 2 → F) : Finset F :=
  Kimchi.SZ.badComb
      (fun i : Fin m => E i 0 - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x 0)))
    ∪ Kimchi.SZ.badComb
      (fun i : Fin m => E i 1 - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x 1)))

/-- The bad point-combination challenges at a fixed `ξ`: the counting-SZ bad set of the
two ξ-combined discrepancy columns. Depends on `(σ, aw₀, x, E, ξ)` — never on `r`. -/
noncomputable def badROf {F G : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] (σ : SRS G) {m : ℕ} (aw₀ : Fin m → Fin (2 ^ σ.k) → F)
    (x : Fin 2 → F) (E : Fin m → Fin 2 → F) (ξ : F) : Finset F :=
  Kimchi.SZ.badComb (fun j : Fin 2 => ∑ i : Fin m,
    ξ ^ (i : ℕ) * (E i j - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j))))

/-- `badXiOf` counts at most `2 · (m − 1)` challenges (at the 43-row batch: `84`): a
union of two counting-SZ bad sets over `Fin m`. -/
private theorem card_badXiOf_le {F G : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] (σ : SRS G) {m : ℕ} (aw₀ : Fin m → Fin (2 ^ σ.k) → F)
    (x : Fin 2 → F) (E : Fin m → Fin 2 → F) : (badXiOf σ aw₀ x E).card ≤ 2 * (m - 1) := by
  unfold badXiOf
  refine le_trans (Finset.card_union_le _ _) ?_
  have h0 := Kimchi.SZ.card_badComb_le
    (fun i : Fin m => E i 0 - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x 0)))
  have h1 := Kimchi.SZ.card_badComb_le
    (fun i : Fin m => E i 1 - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x 1)))
  omega

/-- `badROf` counts at most `1 = 2 − 1` challenge: one counting-SZ bad set over
`Fin 2`. -/
private theorem card_badROf_le {F G : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] (σ : SRS G) {m : ℕ} (aw₀ : Fin m → Fin (2 ^ σ.k) → F)
    (x : Fin 2 → F) (E : Fin m → Fin 2 → F) (ξ : F) :
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
`D i j`. Arity-generic: the AGM capstones consume it at the 43-row `batchC`, the
FS-reflection layer at the reflected run's own 45-row batch. -/
theorem eval_pins_of_opening {F G : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (wh : F), DLRelation σ w wh → w = 0 ∧ wh = 0)
    {m : ℕ} (C : Fin m → G) (x : Fin 2 → F)
    (aw₀ : Fin m → Fin (2 ^ σ.k) → F) (ρw₀ : Fin m → F)
    (hrep : ∀ i, commit σ (aw₀ i) (ρw₀ i) = C i)
    (E : Fin m → Fin 2 → F) (ξ r : F)
    (hξ : ξ ∉ badXiOf σ aw₀ x E) (hr : r ∉ badROf σ aw₀ x E ξ)
    (a : Fin (2 ^ σ.k) → F) (ρ : F)
    (hopen : openingRelationB σ (combinedCommitment ξ C)
      (combinedEvalVector (2 ^ σ.k) r x) (combinedInnerProduct ξ r E) a ρ) :
    ∀ (i : Fin m) (j : Fin 2),
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
      = ∑ j : Fin 2, r ^ (j : ℕ)
          * ∑ i : Fin m, ξ ^ (i : ℕ)
              * innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j)) := by
    rw [hopen.2, ha, innerProduct_combinedEvalVector]
    exact Finset.sum_congr rfl fun j _ => by rw [hip]
  have h2 : combinedInnerProduct ξ r E
      = ∑ j : Fin 2, r ^ (j : ℕ) * ∑ i : Fin m, ξ ^ (i : ℕ) * E i j := by
    unfold combinedInnerProduct
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hsum : ∑ j : Fin 2, r ^ (j : ℕ) * (∑ i : Fin m, ξ ^ (i : ℕ)
      * (E i j - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j)))) = 0 := by
    calc ∑ j : Fin 2, r ^ (j : ℕ) * (∑ i : Fin m, ξ ^ (i : ℕ)
          * (E i j - innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j))))
        = (∑ j : Fin 2, r ^ (j : ℕ) * ∑ i : Fin m, ξ ^ (i : ℕ) * E i j)
          - ∑ j : Fin 2, r ^ (j : ℕ) * ∑ i : Fin m, ξ ^ (i : ℕ)
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
  have hcol : ∀ j : Fin 2, ∑ i : Fin m, ξ ^ (i : ℕ)
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

/-- **Algebraic-prover soundness from ONE transcript** (the AGM corollary): the
representations `aw₀`/`ρw₀` of the 43 batch rows discharge the openings interface of
`kimchiProof_sound_of_openings` on BOTH sides — the reference side outright (`hrep` IS
its `hbound₀`), the consumer side from a single accepted opening via
`ipa_soundnessA` + `eval_pins_of_opening`. The four bad-set bounds and the
ft-equation/`Satisfies` tail are verbatim `of_openings`'; the only new axis is the
combination-challenge pair `(ξ, r)`, guarded by the counted sets `badXi` (≤ 84) and
`badR` (≤ 1), curried by the consumer data `(E, ζ)`/`(E, ζ, ξ)` and quantified BEFORE
`(ξ, r)` — anti-vacuity exactly as for the four challenge axes. Honest scope note: the
quotient identity `hteq` (with `t` and its degree bound) REMAINS a hypothesis — the same
residue as the run-level capstones; dissolving it from the `tComm` representation via
the Maller relation is the follow-on "algebraic quotient" step. Model note: this theorem
quantifies over provers that SUPPLY representations (the AGM idiom). the
general AGM root. -/
theorem kimchiProof_sound_algebraic {F G : Type*} [Field F] [AddCommGroup G]
    [Module F G] {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) (hk : 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms G) (hvk : VKCorresponds σ comms idx)
    (pub : Fin idx.publicCount → F)
    (wC : Fin 15 → G) (zC : G)
    (aw₀ : Fin 43 → Fin (2 ^ σ.k) → F) (ρw₀ : Fin 43 → F)
    (hrep : ∀ i, commit σ (aw₀ i) (ρw₀ i) = batchC wC zC comms i) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F)
        (badZ : F → F → F → Polynomial F → Finset F)
        (badXi : (Fin 43 → Fin 2 → F) → F → Finset F)
        (badR : (Fin 43 → Fin 2 → F) → F → F → Finset F),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial F), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n)
        ∧ (∀ (E : Fin 43 → Fin 2 → F) (ζ : F), (badXi E ζ).card ≤ 84)
        ∧ (∀ (E : Fin 43 → Fin 2 → F) (ζ ξ : F), (badR E ζ ξ).card ≤ 1))
      ∧ ∀ (β γ α : F) (t : Polynomial F) (ζ : F)
          (E : Fin 43 → Fin 2 → F) (ξ r : F) (A : Prop),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ → ζ ∉ badZ β γ α t →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) →
          t.natDegree < 7 * n →
          ξ ∉ badXi E ζ → r ∉ badR E ζ ξ →
          FiatShamirTreeB σ (combinedCommitment ξ (batchC wC zC comms))
            (combinedEvalVector (2 ^ σ.k) r ![ζ, idx.omega * ζ])
            (combinedInnerProduct ξ r E) A →
          A →
          (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
              * (idx.sigmaPoly 6).eval ζ
            - (ζ ^ n - 1) * t.eval ζ
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly pub).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → F, Satisfies idx pub wTab := by
  obtain ⟨badB, badG, badA, badZ, ⟨hB, hG, hA, hZ⟩, himp⟩ :=
    kimchiProof_sound_of_openings σ idx hk hbind comms hvk pub wC zC aw₀ ρw₀ hrep
  refine ⟨badB, badG, badA, badZ,
    fun E ζ => badXiOf σ aw₀ ![ζ, idx.omega * ζ] E,
    fun E ζ ξ => badROf σ aw₀ ![ζ, idx.omega * ζ] E ξ,
    ⟨hB, hG, hA, hZ, fun E ζ => card_badXiOf_le σ aw₀ ![ζ, idx.omega * ζ] E,
      fun E ζ ξ => card_badROf_le σ aw₀ ![ζ, idx.omega * ζ] E ξ⟩, ?_⟩
  intro β γ α t ζ E ξ r A hβ hγ hα hζ hζ1 hζb ht hξ hr hFS hAcc hteq
  obtain ⟨a, ρ, hopen⟩ := ipa_soundnessA σ _ _ _ hFS hAcc
  have hpins := eval_pins_of_opening σ hbind (batchC wC zC comms)
    ![ζ, idx.omega * ζ] aw₀ ρw₀ hrep E ξ r hξ hr a ρ hopen
  exact ⟨_, himp β γ α t ζ E aw₀ ρw₀ hβ hγ hα hζ hζ1 hζb ht
    (fun i => ⟨hrep i, fun j => hpins i j⟩) hteq⟩

/-! ## The algebraic quotient — the ft residue dissolved from the chunk representations -/

/-- **The assembled quotient** — the genuine degree-`< 7·2^k` polynomial the 7 committed
`tComm` chunk rows represent: chunk `j` contributes its row polynomial shifted by
`X^(j·2^k)`, exactly kimchi's `t = ∑ⱼ X^(j·n) · tⱼ` chunking (`Chunk.lean`'s
`assemblePoly` at width `2^k`, phrased over `rowPoly` so the capstone statements read at
the committed vectors directly). The named `t` of the residue-free
capstones — the `badZ` antecedent and the derived Maller identity are stated against THIS
polynomial, never an opaque existential witness. -/
noncomputable def ftChunkAssembly {F : Type*} [Field F] (k : ℕ)
    (aT : Fin 7 → Fin (2 ^ k) → F) : Polynomial F :=
  ∑ j : Fin 7, rowPoly (aT j) * Polynomial.X ^ ((j : ℕ) * 2 ^ k)

/-- The assembly meets the 7-chunk degree bound: each summand has degree
`≤ (2^k − 1) + j·2^k ≤ 7·2^k − 1`. -/
private theorem ftChunkAssembly_natDegree_lt {F : Type*} [Field F] (k : ℕ)
    (aT : Fin 7 → Fin (2 ^ k) → F) :
    (ftChunkAssembly k aT).natDegree < 7 * 2 ^ k := by
  have h2k : 0 < 2 ^ k := Nat.two_pow_pos k
  have hle : (ftChunkAssembly k aT).natDegree ≤ 7 * 2 ^ k - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    refine le_trans (natDegree_mul_le) ?_
    rw [natDegree_X_pow]
    have hrow := rowPoly_natDegree_lt_two_pow (aT j)
    have hj : (j : ℕ) ≤ 6 := by omega
    have hjm : (j : ℕ) * 2 ^ k ≤ 6 * 2 ^ k := Nat.mul_le_mul_right _ hj
    omega
  omega

/-- The assembly evaluates as the `(ζ^(2^k))`-power combination of the chunk-row
evaluations — kimchi's `combined_inner_product` recombination, at the assembly. -/
private theorem ftChunkAssembly_eval {F : Type*} [Field F] (k : ℕ)
    (aT : Fin 7 → Fin (2 ^ k) → F) (ζ : F) :
    (ftChunkAssembly k aT).eval ζ
      = ∑ j : Fin 7, (ζ ^ 2 ^ k) ^ (j : ℕ) * (rowPoly (aT j)).eval ζ := by
  unfold ftChunkAssembly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_pow, eval_X, mul_comm ((j : ℕ)) (2 ^ k), pow_mul]
  ring

/-- **The Maller/ft identity from the chunk representations** (the algebraic-quotient
engine): representations of the 7 `tComm` chunks plus ONE accepted ft opening — the
commitment equation `hcommit` (the verifier's ft row: `pScalar • Cσ6` minus the
`(ζ^n − 1)`-scaled `(ζ^n)`-power combination of the chunk commitments) and its value
equation `heval` — pin the opened row, via binding (`commitₗ`-linearity collapses the
combination to ONE commitment, exactly as in `eval_pins_of_opening`), to the
corresponding pointwise combination of the represented rows; reading that combination
through `rowPoly` yields BOTH residue facts at once: the assembled quotient's degree
bound `< 7n` and the ft equation `pScalar · σ₆(ζ) − (ζ^n − 1) · t(ζ) = v0` with
`t = ftChunkAssembly σ.k aT`. This is `ft_equation` (`Sound.lean`) generalized from its
`nc = 1` degenerate case (degree `< 2^k`, vacuous for the deployed 7-chunk
configuration) to the genuine chunked quotient. -/
theorem ft_identity_of_chunks {F G : Type*} [Field F] [AddCommGroup G]
    [Module F G] (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (σ₆ : Polynomial F) (hσ₆ : σ₆.natDegree < 2 ^ σ.k)
    (Cσ6 : G) (hC : Cσ6 = commitPoly σ σ₆)
    (TC : Fin 7 → G) (aT : Fin 7 → Fin (2 ^ σ.k) → F) (ρT : Fin 7 → F)
    (htc : ∀ j, commit σ (aT j) (ρT j) = TC j)
    (pScalar ζ v0 : F) (n : ℕ) (hk : 2 ^ σ.k = n)
    (a : Fin (2 ^ σ.k) → F) (ρ : F)
    (hcommit : commit σ a ρ
      = pScalar • Cσ6 - (ζ ^ n - 1) • ∑ j : Fin 7, (ζ ^ n) ^ (j : ℕ) • TC j)
    (heval : innerProduct a (evalVector (2 ^ σ.k) ζ) = v0) :
    (ftChunkAssembly σ.k aT).natDegree < 7 * n
      ∧ pScalar * σ₆.eval ζ - (ζ ^ n - 1) * (ftChunkAssembly σ.k aT).eval ζ = v0 := by
  subst hk
  -- Step A: σ₆'s commitment witness — the coefficient vector at blinder `0`.
  set w6 : Fin (2 ^ σ.k) → F := fun i => σ₆.coeff (i : ℕ) with hw6
  have hC6 : Cσ6 = commit σ w6 0 := hC.trans (commitPoly_eq_commit σ σ₆)
  have hip6 : innerProduct w6 (evalVector (2 ^ σ.k) ζ) = σ₆.eval ζ := by
    rw [← rowPoly_eval, rowPoly_coeff_self hσ₆]
  -- Step B: the ft commitment as ONE commitment of the pointwise-combined witness —
  -- `commitₗ`-linearity at the pair family, mirroring `eval_pins_of_opening` Step A.
  set b : Fin (2 ^ σ.k) → F :=
    pScalar • w6 - (ζ ^ 2 ^ σ.k - 1)
      • ∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • aT j with hb
  set ρb : F :=
    -((ζ ^ 2 ^ σ.k - 1) • ∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • ρT j) with hρb
  have hpair : ((b, ρb) : (Fin (2 ^ σ.k) → F) × F)
      = pScalar • ((w6, 0) : (Fin (2 ^ σ.k) → F) × F)
        - (ζ ^ 2 ^ σ.k - 1) • ∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ)
            • ((aT j, ρT j) : (Fin (2 ^ σ.k) → F) × F) := by
    refine Prod.ext ?_ ?_
    · simp only [hb, Prod.fst_sub, Prod.smul_fst, Prod.fst_sum]
    · simp only [hρb, Prod.snd_sub, Prod.smul_snd, Prod.snd_sum, smul_zero, zero_sub]
  have hB : commit σ b ρb
      = pScalar • Cσ6
        - (ζ ^ 2 ^ σ.k - 1) • ∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • TC j := by
    have h0 : commit σ b ρb = commitₗ σ (b, ρb) := rfl
    have h1 : commitₗ σ ((w6, 0) : (Fin (2 ^ σ.k) → F) × F) = commit σ w6 0 := rfl
    rw [h0, hpair, map_sub, map_smul, map_smul, map_sum, h1, ← hC6]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    exact congrArg _ (htc j)
  -- Step C: binding, at witness level — the opened row IS the combination.
  have hbd : CommitmentBinding (F := F) σ :=
    (commitmentBinding_iff_no_relation σ).mpr hbind
  have hab : a = b :=
    congrArg Prod.fst (@hbd (a, ρ) (b, ρb) (hcommit.trans hB.symm))
  refine ⟨ftChunkAssembly_natDegree_lt σ.k aT, ?_⟩
  -- Step E: expand the inner product of `b` linearly and conclude.
  have hsub : innerProduct b (evalVector (2 ^ σ.k) ζ)
      = pScalar * innerProduct w6 (evalVector (2 ^ σ.k) ζ)
        - (ζ ^ 2 ^ σ.k - 1)
          * innerProduct (∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • aT j)
              (evalVector (2 ^ σ.k) ζ) := by
    rw [hb]
    unfold innerProduct
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hipS : innerProduct (∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • aT j)
      (evalVector (2 ^ σ.k) ζ)
      = ∑ j : Fin 7, (ζ ^ 2 ^ σ.k) ^ (j : ℕ)
          * innerProduct (aT j) (evalVector (2 ^ σ.k) ζ) := by
    unfold innerProduct
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  rw [← heval, hab, hsub, hipS, hip6, ftChunkAssembly_eval]
  simp only [rowPoly_eval]

/-- **Algebraic-prover soundness, residue-free** (the algebraic quotient):
`kimchiProof_sound_algebraic` with the ft/quotient residue DISSOLVED — the algebraic
prover additionally supplies the 7 `tComm`-chunk representations (`aT`/`ρT`, tied to the
chunk commitments by `hTC`), and the quotient `t` and the Maller identity `hteq` are
DERIVED, no longer hypotheses. The trade is honest: `hteq` was an unchecked "∃ valid
`t`"; here it is replaced by a CHECKED fact — the ft opening (the two antecedents after
`A`), which the deployed verifier's ft-row acceptance provides — fed to
`ft_identity_of_chunks`. The ft opening is a hypothesis because this abstract capstone
does not reflect a deployed run; a fully deployed AGM variant would derive it from
`poseidon_fiat_shamir` on the ft row. The quotient is now the genuine degree-`< 7n`
polynomial `ftChunkAssembly σ.k aT` assembled from the committed chunks — NOT the
degree-`< 2^k` `ftQuotient` of `ft_equation` (`Sound.lean`), whose `nc = 1` shortcut is
vacuous for the deployed 7-chunk configuration. No-vacuity: an honest 7-chunk prover
satisfies every antecedent — `hCσ6` is discharged by `hvk` (`VKCorresponds` is
`indexerOf`, whose `sigma i` IS `commitPoly σ (idx.sigmaPoly i)`, `Correspond.lean`),
and the honest chunk vectors make `ftChunkAssembly` the real quotient. The six bad-set
bounds and the FS/acceptance/`Satisfies` consumer tail are verbatim
`kimchiProof_sound_algebraic`'s; `ζ ^ n ≠ 1` is the ft non-degeneracy pin.
The residue-free AGM root. -/
theorem kimchiProof_sound_algebraic_ft {F G : Type*} [Field F] [AddCommGroup G]
    [Module F G] {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) (hk : 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms G) (hvk : VKCorresponds σ comms idx)
    (pub : Fin idx.publicCount → F)
    (wC : Fin 15 → G) (zC : G)
    (aw₀ : Fin 43 → Fin (2 ^ σ.k) → F) (ρw₀ : Fin 43 → F)
    (hrep : ∀ i, commit σ (aw₀ i) (ρw₀ i) = batchC wC zC comms i)
    (TC : Fin 7 → G) (aT : Fin 7 → Fin (2 ^ σ.k) → F) (ρT : Fin 7 → F)
    (hTC : ∀ j, commit σ (aT j) (ρT j) = TC j)
    (Cσ6 : G) (hCσ6 : Cσ6 = commitPoly σ (idx.sigmaPoly 6)) :
    ∃ (badB : Finset F) (badG : F → Finset F) (badA : F → F → Finset F)
        (badZ : F → F → F → Polynomial F → Finset F)
        (badXi : (Fin 43 → Fin 2 → F) → F → Finset F)
        (badR : (Fin 43 → Fin 2 → F) → F → F → Finset F),
      (badB.card ≤ 7 * (n - idx.zkRows)
        ∧ (∀ β, (badG β).card ≤ 7 * (n - idx.zkRows))
        ∧ (∀ β γ,
            (badA β γ).card ≤ n * (Index.gateAlphaCount + Index.permAlphaCount - 1))
        ∧ (∀ β γ α (t : Polynomial F), t.natDegree < 7 * n →
            (badZ β γ α t).card ≤ Index.degreeBound n)
        ∧ (∀ (E : Fin 43 → Fin 2 → F) (ζ : F), (badXi E ζ).card ≤ 84)
        ∧ (∀ (E : Fin 43 → Fin 2 → F) (ζ ξ : F), (badR E ζ ξ).card ≤ 1))
      ∧ ∀ (β γ α ζ : F)
          (E : Fin 43 → Fin 2 → F) (ξ r : F) (A : Prop)
          (aft : Fin (2 ^ σ.k) → F) (ρft : F),
          β ∉ badB → γ ∉ badG β → α ∉ badA β γ →
          ζ ∉ badZ β γ α (ftChunkAssembly σ.k aT) →
          ζ ≠ 1 → ζ ≠ idx.omega ^ (n - idx.zkRows) → ζ ^ n ≠ 1 →
          ξ ∉ badXi E ζ → r ∉ badR E ζ ξ →
          FiatShamirTreeB σ (combinedCommitment ξ (batchC wC zC comms))
            (combinedEvalVector (2 ^ σ.k) r ![ζ, idx.omega * ζ])
            (combinedInnerProduct ξ r E) A →
          A →
          (commit σ aft ρft
            = permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)
                • Cσ6 - (ζ ^ n - 1) • ∑ j : Fin 7, (ζ ^ n) ^ (j : ℕ) • TC j) →
          (innerProduct aft (evalVector (2 ^ σ.k) ζ)
            = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ
                ζ (-((idx.pubPoly pub).eval ζ)) (claimedEvals E)) →
          ∃ wTab : Fin n → Fin 15 → F, Satisfies idx pub wTab := by
  obtain ⟨badB, badG, badA, badZ, badXi, badR, hbounds, himp⟩ :=
    kimchiProof_sound_algebraic σ idx hk hbind comms hvk pub wC zC aw₀ ρw₀ hrep
  refine ⟨badB, badG, badA, badZ, badXi, badR, hbounds, ?_⟩
  intro β γ α ζ E ξ r A aft ρft hβ hγ hα hζ hζ1 hζb hζn hξ hr hFS hAcc hftc hftv
  have hσ₆ : (idx.sigmaPoly 6).natDegree < 2 ^ σ.k := by
    rw [hk]
    exact columnPoly_natDegree_lt idx.omega_prim _
  obtain ⟨htdeg, hteq⟩ := ft_identity_of_chunks σ hbind (idx.sigmaPoly 6) hσ₆ Cσ6 hCσ6
    TC aT ρT hTC
    (permScalar β γ α (zkpmEval n idx.zkRows idx.omega ζ) (claimedEvals E)) ζ
    (ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase α β γ ζ
      (-((idx.pubPoly pub).eval ζ)) (claimedEvals E)) n hk aft ρft hftc hftv
  exact himp β γ α (ftChunkAssembly σ.k aT) ζ E ξ r A hβ hγ hα hζ hζ1 hζb htdeg
    hξ hr hFS hAcc hteq

end Kimchi.Verifier
