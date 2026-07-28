import Mathlib
import Kimchi.Verifier.Reduction.Soundness
import Zcash.Snark.Soundness.AGM.Adapter

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

The last section packages the two binding-free halves for the knowledge-soundness game:
`algebraicRelationOfDL` injects a nontrivial discrete-log relation into the run's AUGMENTED
basis (the shape the relation finder consumes, at zero coefficient on the transcript-derived
base), and `badChallenge_of_not_pins` is the contrapositive of `eval_pins_of_opening_of_eq`
— "the extracted table failed ⟹ a challenge was bad", the direction the game reads.
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

/-- **Commitment linearity at the combined commitment** (Step A of the AGM bridge,
binding-free): SRS-basis representations `(aw₀ i, ρw₀ i)` of the `m` batch rows collapse
the ξ-combination `∑ i, ξ^i • C i` to a SINGLE commitment, that of the ξ-combined
representation. Pure `map_sum`/`map_smul` of the linear map `commitₗ`, mirroring
`commit_combine`.

Project-local: it is the binding-free half of `eval_pins_of_opening`, split out so that
the knowledge-soundness reduction — which runs over keys where binding provably FAILS —
can reach the discrete-log relation of `dlRelation_of_opening_ne` without assuming it. -/
theorem combinedCommitment_eq_commit_of_rep {F G : Type*} [Field F]
    [AddCommGroup G] [Module F G] (σ : SRS G)
    {m : ℕ} (C : Fin m → G)
    (aw₀ : Fin m → Fin (2 ^ σ.k) → F) (ρw₀ : Fin m → F)
    (hrep : ∀ i, commit σ (aw₀ i) (ρw₀ i) = C i) (ξ : F) :
    combinedCommitment ξ C
      = commit σ (∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i)
          (∑ i : Fin m, ξ ^ (i : ℕ) • ρw₀ i) := by
  have hpair : (∑ i : Fin m, ξ ^ (i : ℕ)
        • ((aw₀ i, ρw₀ i) : (Fin (2 ^ σ.k) → F) × F))
      = (∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i, ∑ i : Fin m, ξ ^ (i : ℕ) • ρw₀ i) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      exact Finset.sum_congr rfl fun i _ => rfl
    · rw [Prod.snd_sum]
      exact Finset.sum_congr rfl fun i _ => rfl
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

/-- **The break branch: an opening that misses the ξ-combined representation IS a
discrete-log relation** (binding-free). Given per-row representations and any pair
`(a, ρ)` whose commitment is the combined commitment, the difference pair
`(a − ∑ i, ξ^i • aw₀ i, ρ − ∑ i, ξ^i • ρw₀ i)` satisfies `DLRelation σ` — subtract the
single commitment of `combinedCommitment_eq_commit_of_rep` using linearity of `commitₗ`.

The two conclusions are deliberately separate: the relation is UNCONDITIONAL (it is what
the extractor's break branch emits, with computed coefficients), while nontriviality is
the discriminator the consumer branches on. Bundling them as an existence statement
would be useless downstream, where at the sampled key a relation always exists.

Project-local: this is where `eval_pins_of_opening` spends its binding hypothesis; over
the knowledge-soundness game's key basis binding is false, so the failure is data rather
than an obstruction. -/
theorem dlRelation_of_opening_ne {F G : Type*} [Field F]
    [AddCommGroup G] [Module F G] (σ : SRS G)
    {m : ℕ} (C : Fin m → G)
    (aw₀ : Fin m → Fin (2 ^ σ.k) → F) (ρw₀ : Fin m → F)
    (hrep : ∀ i, commit σ (aw₀ i) (ρw₀ i) = C i) (ξ : F)
    (a : Fin (2 ^ σ.k) → F) (ρ : F)
    (hcommit : commit σ a ρ = combinedCommitment ξ C) :
    DLRelation σ (a - ∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i)
        (ρ - ∑ i : Fin m, ξ ^ (i : ℕ) • ρw₀ i)
      ∧ (a ≠ ∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i →
          a - ∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i ≠ 0) := by
  refine ⟨?_, fun hne => sub_ne_zero_of_ne hne⟩
  have hA := combinedCommitment_eq_commit_of_rep σ C aw₀ ρw₀ hrep ξ
  have hlin : commit σ (a - ∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i)
        (ρ - ∑ i : Fin m, ξ ^ (i : ℕ) • ρw₀ i)
      = commit σ a ρ
        - commit σ (∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i)
            (∑ i : Fin m, ξ ^ (i : ℕ) • ρw₀ i) := by
    show commitₗ σ (a - ∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i,
        ρ - ∑ i : Fin m, ξ ^ (i : ℕ) • ρw₀ i)
      = commitₗ σ (a, ρ)
        - commitₗ σ (∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i,
            ∑ i : Fin m, ξ ^ (i : ℕ) • ρw₀ i)
    rw [← map_sub]
    rfl
  show commit σ (a - ∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i)
      (ρ - ∑ i : Fin m, ξ ^ (i : ℕ) • ρw₀ i) = 0
  rw [hlin, hcommit, hA, sub_self]

/-- **The eval pins from coefficient equality** (Steps C–D of the AGM bridge,
binding-free): at good `(ξ, r)`, an opening `(a, ρ)` of the combined claim whose witness
IS the ξ-combined representation pins every claimed evaluation to the represented row's
true evaluation. Substituting `ha` into the opening's value equation and expanding the
inner product bilinearly reduces it to `∑ j, r^j · (∑ i, ξ^i · D i j) = 0` in the
discrepancies `D i j = E i j − ⟨aw₀ i, evalVector (x j)⟩`, and
`SZ.eq_zero_of_comb_eq_zero` — first at `r`, then per point at `ξ` — kills every `D i j`.

Neither the per-row representations nor commitment linearity enter: those are consumed
only in DERIVING `ha`, which here is given.

Project-local: it is `eval_pins_of_opening` with binding replaced by its single
consequence, so the knowledge-soundness reduction can take the pins on the branch where
the extracted witness does match, and `dlRelation_of_opening_ne` on the branch where it
does not. -/
theorem eval_pins_of_opening_of_eq {F G : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] (σ : SRS G)
    {m : ℕ} (C : Fin m → G) (x : Fin evalPts → F)
    (aw₀ : Fin m → Fin (2 ^ σ.k) → F)
    (E : Fin m → Fin evalPts → F) (ξ r : F)
    (hξ : ξ ∉ badXiOf σ aw₀ x E) (hr : r ∉ badROf σ aw₀ x E ξ)
    (a : Fin (2 ^ σ.k) → F) (ρ : F)
    (hopen : openingRelationB σ (combinedCommitment ξ C)
      (combinedEvalVector (2 ^ σ.k) r x) (combinedInnerProduct ξ r E) a ρ)
    (ha : a = ∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i) :
    ∀ (i : Fin m) (j : Fin evalPts),
      E i j = innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j)) := by
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
`44·nc + 1`-segment flat batch (45 at `nc = 1`).

Recovered from the binding-free split: `dlRelation_of_opening_ne` turns the opening's
commitment equation into a discrete-log relation, `hbind` says it is trivial — which is
exactly the coefficient equality `eval_pins_of_opening_of_eq` consumes. -/
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
  obtain ⟨hrel, hnt⟩ :=
    dlRelation_of_opening_ne σ C aw₀ ρw₀ hrep ξ a ρ hopen.1
  have ha : a = ∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i := by
    by_contra hne
    exact hnt hne (hbind _ _ hrel).1
  exact eval_pins_of_opening_of_eq σ C x aw₀ E ξ r hξ hr a ρ hopen ha

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



/-! ## The algebraic-prover corollary -/


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
blinder `0` — the shape binding consumes.

Module-public (it was `private`) because the reflection layer needs exactly this bridge to
read the run's verifying-key stream as honest chunk commitments: `Capstone/Reflection.lean`
carries project-local duplicates (`commitPolyChunk_as_commit`,
`commitPolyMaskedChunk_as_commit`) that this export is meant to retire. -/
theorem commitPolyChunk_eq_commit [Field F] [AddCommGroup G] [Module F G]
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

/-- **The break branch for the ft row: an ft opening that misses the intended
combination IS a discrete-log relation** (binding-free). The intended coefficient-blinder
pair `(b, ρb)` — `pScalar` times the `ζ^{2^σ.k}`-combination of `σ₆`'s coefficient
windows (at blinder `0`, the `σ₆` chunk commitments being unblinded fixed columns) minus
`(ζ^n − 1)` times the same combination of the quotient chunk witnesses — commits to the
very group element the opened `(a, ρ)` commits to. Subtracting the two representations
through the linear map `commitₗ` leaves `DLRelation σ (a − b) (ρ − ρb)`.

The two conclusions are deliberately separate: the relation is UNCONDITIONAL (it is what
the extractor's break branch emits, with computed coefficients), while nontriviality is
the discriminator the consumer branches on. Bundling them as an existence statement would
be useless downstream, where at the sampled key a relation always exists.

Project-local: this is where `ft_identity_of_chunks` spends its binding hypothesis, so
the knowledge-soundness reduction — which runs over keys where binding provably FAILS —
gets the relation instead of an obstruction. The `ft`-row companion of
`dlRelation_of_opening_ne`. -/
theorem ft_dlRelation_of_chunks_ne [Field F] [AddCommGroup G]
    [Module F G] (σ : SRS G)
    {nc : ℕ} (σ₆ : Polynomial F)
    (Cσ6 : Fin nc → G) (hC : ∀ c : Fin nc, Cσ6 c = commitPolyChunk σ σ₆ (c : ℕ))
    {nt : ℕ}
    (TC : Fin nt → G) (aT : Fin nt → Fin (2 ^ σ.k) → F) (ρT : Fin nt → F)
    (htc : ∀ j, commit σ (aT j) (ρT j) = TC j)
    (pScalar ζ : F) (n : ℕ)
    (a : Fin (2 ^ σ.k) → F) (ρ : F) (b : Fin (2 ^ σ.k) → F) (ρb : F)
    (hb : b = pScalar • ∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ)
            • chunkCoeffs (2 ^ σ.k) σ₆ (c : ℕ)
          - (ζ ^ n - 1) • ∑ j : Fin nt, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • aT j)
    (hρb : ρb = -((ζ ^ n - 1) • ∑ j : Fin nt, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • ρT j))
    (hcommit : commit σ a ρ
      = pScalar • ∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ) • Cσ6 c
        - (ζ ^ n - 1) • ∑ j : Fin nt, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • TC j) :
    DLRelation σ (a - b) (ρ - ρb) ∧ (a ≠ b → a - b ≠ 0) := by
  refine ⟨?_, fun hne => sub_ne_zero_of_ne hne⟩
  -- Step A: σ₆'s per-chunk commitment witnesses — the coefficient windows at blinder 0.
  have hC6 : ∀ c : Fin nc,
      Cσ6 c = commit σ (chunkCoeffs (2 ^ σ.k) σ₆ (c : ℕ)) 0 := fun c =>
    (hC c).trans (commitPolyChunk_eq_commit σ σ₆ (c : ℕ))
  -- Step B: the ft commitment as ONE commitment, that of the pointwise-combined witness.
  have hpair : ((b, ρb) : (Fin (2 ^ σ.k) → F) × F)
      = pScalar • ∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ)
            • ((chunkCoeffs (2 ^ σ.k) σ₆ (c : ℕ), 0) : (Fin (2 ^ σ.k) → F) × F)
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
      show commit σ (chunkCoeffs (2 ^ σ.k) σ₆ (c : ℕ)) 0 = Cσ6 c
      exact (hC6 c).symm
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      exact congrArg _ (htc j)
  -- Step C: subtract the two representations of the same group element.
  have hlin : commit σ (a - b) (ρ - ρb) = commit σ a ρ - commit σ b ρb := by
    show commitₗ σ (a - b, ρ - ρb) = commitₗ σ (a, ρ) - commitₗ σ (b, ρb)
    rw [← map_sub]
    rfl
  show commit σ (a - b) (ρ - ρb) = 0
  rw [hlin, hcommit, hB, sub_self]

/-- **The Maller/ft identity from the coefficient equality** (binding-free): given that
the opened ft witness `a` IS the intended combination `b`, the assembled quotient meets
the degree bound `< 7n` and the ft equation holds. Expanding `⟨b, evalVector ζ⟩`
bilinearly splits it into `pScalar` times the chunk-combination of `σ₆`'s windows — which
is `σ₆.eval ζ` by the chunk decomposition at degree `< nc · 2^σ.k` — minus `(ζ^n − 1)`
times the chunk-combination of the quotient windows, which is `ftChunkAssembly`'s value
at `ζ`; the opening's value equation `heval` then reads off the identity.

Neither the `σ₆` chunk commitments nor the quotient chunk representations enter: those
are consumed only in DERIVING `hab`, which here is given.

Project-local: it is `ft_identity_of_chunks` with binding replaced by its single
consequence, so the knowledge-soundness reduction can take the identity on the branch
where the opened witness does match and `ft_dlRelation_of_chunks_ne` on the branch where
it does not. -/
theorem ft_identity_of_chunks_of_eq [Field F] [AddCommGroup G]
    [Module F G] (σ : SRS G)
    {nc : ℕ} (σ₆ : Polynomial F) (hσ₆ : σ₆.natDegree < nc * 2 ^ σ.k)
    {nt : ℕ} (hnt0 : 0 < nt) (hnt : nt ≤ 7 * nc)
    (aT : Fin nt → Fin (2 ^ σ.k) → F)
    (pScalar ζ v0 : F) (n : ℕ) (hk : nc * 2 ^ σ.k = n)
    (a b : Fin (2 ^ σ.k) → F)
    (hb : b = pScalar • ∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ)
            • chunkCoeffs (2 ^ σ.k) σ₆ (c : ℕ)
          - (ζ ^ n - 1) • ∑ j : Fin nt, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • aT j)
    (heval : innerProduct a (evalVector (2 ^ σ.k) ζ) = v0)
    (hab : a = b) :
    (ftChunkAssembly σ.k nt aT).natDegree < 7 * n
      ∧ pScalar * σ₆.eval ζ - (ζ ^ n - 1) * (ftChunkAssembly σ.k nt aT).eval ζ = v0 := by
  -- The `σ₆` side: its coefficient windows recombine to `σ₆.eval ζ`.
  have hip6 : ∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ)
      * innerProduct (chunkCoeffs (2 ^ σ.k) σ₆ (c : ℕ)) (evalVector (2 ^ σ.k) ζ)
      = σ₆.eval ζ := by
    rw [eval_eq_sum_chunkPoly _ hσ₆ ζ, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun c _ => by rw [chunkPoly_eval]
  have hdeg : (ftChunkAssembly σ.k nt aT).natDegree < 7 * n := by
    have h := ftChunkAssembly_natDegree_lt σ.k hnt0 aT
    have h2 : nt * 2 ^ σ.k ≤ 7 * (nc * 2 ^ σ.k) := by
      rw [← mul_assoc]
      exact Nat.mul_le_mul_right _ hnt
    rw [hk] at h2
    omega
  refine ⟨hdeg, ?_⟩
  -- Expand the inner product of `b` linearly and conclude.
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
      = pScalar * innerProduct
            (∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ)
              • chunkCoeffs (2 ^ σ.k) σ₆ (c : ℕ))
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
chunk-combined coefficient windows outright.

Recovered from the binding-free split: `ft_dlRelation_of_chunks_ne` turns the ft
commitment equation into a discrete-log relation against the intended combination `b`,
`hbind` says it is trivial — which is exactly the coefficient equality
`ft_identity_of_chunks_of_eq` consumes. -/
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
  set b : Fin (2 ^ σ.k) → F :=
    pScalar • ∑ c : Fin nc, (ζ ^ 2 ^ σ.k) ^ (c : ℕ) • chunkCoeffs (2 ^ σ.k) σ₆ (c : ℕ)
      - (ζ ^ n - 1) • ∑ j : Fin nt, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • aT j with hb
  set ρb : F :=
    -((ζ ^ n - 1) • ∑ j : Fin nt, (ζ ^ 2 ^ σ.k) ^ (j : ℕ) • ρT j) with hρb
  obtain ⟨hrel, hntriv⟩ :=
    ft_dlRelation_of_chunks_ne σ σ₆ Cσ6 hC TC aT ρT htc pScalar ζ n a ρ b ρb hb hρb
      hcommit
  have hab : a = b := by
    by_contra hne
    exact hntriv hne (hbind _ _ hrel).1
  exact ft_identity_of_chunks_of_eq σ σ₆ hσ₆ hnt0 hnt aT pScalar ζ v0 n hk a b hb heval
    hab


/-! ## From a discrete-log relation to a break the finder accepts

The knowledge-soundness extractor's break branch does not emit a bare discrete-log relation:
it emits a nontrivial relation over the run's AUGMENTED basis `(σ.g, U, σ.h)` — the setup
generators, the transcript-derived base and the blinder — and the relation finder keeps
exactly those whose coefficient at the transcript-derived base vanishes, restricting them to
the setup basis. Every break this development produces (the per-row collision, the
combined-opening mismatch, the verifying-key mismatch, the derived `ft` mismatch) has that
one shape, so the injection is named ONCE here rather than inlined per call site.

`badChallenge_of_not_pins` is the other half the game reads: the contrapositive of
`eval_pins_of_opening_of_eq`. The game must conclude "a challenge was bad" from "the
extracted table failed", never the converse, so the `by_contra` belongs here and not in the
game file. -/

/-- **A nontrivial discrete-log relation is a break over the augmented basis, at zero
coefficient on the transcript-derived base.** From `DLRelation σ w wh` with `w ≠ 0`, the
coefficient vector `augmentedCoeffs w 0 wh` is a nontrivial relation over
`augmentedBasis σ.g U σ.h`: the augmented representation evaluates to
`⟨w, σ.g⟩ + 0 • U + wh • σ.h` (`representationEval_augmentedBasis`), the middle term dies,
and what is left is the relation itself. Nontriviality is inherited from `w ≠ 0` — the
restriction of the coefficients to the setup generators IS `w`.

Project-local: this is the injection the knowledge-soundness extractor's break branch needs,
and the reason the breaks it emits land in the `ε`-priced arm rather than the residual —
their `u`-coefficient is `0` by `algebraicRelationOfDL_coeffs_u`, definitionally. `U` is a
parameter (not `σ.U`) because the run's transcript-derived base is squeezed from the
transcript, not read off the setup. -/
def algebraicRelationOfDL [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) (U : G) (w : Fin (2 ^ σ.k) → F) (wh : F)
    (hrel : DLRelation σ w wh) (hw : w ≠ 0) :
    Zcash.Snark.AlgebraicRelationWitness (F := F)
      (Zcash.Snark.augmentedBasis σ.g U σ.h) where
  coeffs := Zcash.Snark.augmentedCoeffs w 0 wh
  nontrivial := fun hzero => hw (funext fun i => congrFun hzero (Sum.inl i))
  relation := by
    rw [Zcash.Snark.representationEval_augmentedBasis]
    simpa using hrel

/-- **The computed break does not touch the transcript-derived base.** Definitional, and the
reason `algebraicRelationOfDL` lands in the arm the relation finder keeps: the finder retains
exactly the breaks whose coefficient at `u` vanishes. -/
theorem algebraicRelationOfDL_coeffs_u [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) (U : G) (w : Fin (2 ^ σ.k) → F) (wh : F)
    (hrel : DLRelation σ w wh) (hw : w ≠ 0) :
    (algebraicRelationOfDL σ U w wh hrel hw).coeffs Zcash.Snark.AugmentedIndex.u = 0 := rfl

/-- The break's coefficients on the setup generators are the given ones. Definitional; stated
so the consumer can read the relation off the setup basis without unfolding the injection. -/
theorem algebraicRelationOfDL_coeffs_gen [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) (U : G) (w : Fin (2 ^ σ.k) → F) (wh : F)
    (hrel : DLRelation σ w wh) (hw : w ≠ 0) (i : Fin (2 ^ σ.k)) :
    (algebraicRelationOfDL σ U w wh hrel hw).coeffs (Zcash.Snark.AugmentedIndex.gen i)
      = w i := rfl

/-- The break's coefficient at the blinding base is the given one. Definitional. -/
theorem algebraicRelationOfDL_coeffs_w [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) (U : G) (w : Fin (2 ^ σ.k) → F) (wh : F)
    (hrel : DLRelation σ w wh) (hw : w ≠ 0) :
    (algebraicRelationOfDL σ U w wh hrel hw).coeffs Zcash.Snark.AugmentedIndex.w = wh := rfl

/-- **An unpinned evaluation forces a bad challenge** — the contrapositive packaging of
`eval_pins_of_opening_of_eq`. Given the per-row representations `aw₀`, an accepted opening
`(a, ρ)` of the combined claim, and the coordinate equality `ha` the extractor's left branch
certifies, a single claimed evaluation that is NOT the inner product of its row's
representation with the evaluation vector forces the polyscale challenge into `badXiOf` or
the evalscale challenge into `badROf` — both counted, never assumed.

Project-local: this is the direction the knowledge-soundness game consumes. It reads "the
extracted table failed at `(i, j)`", and must charge that to one of the two counted
exclusion sets; stating it here keeps the `by_contra` out of the game file. The per-row
blinders `ρw₀` and their representation hypothesis do NOT appear — deriving `ha` is what
consumes them, and here `ha` is given. -/
theorem badChallenge_of_not_pins [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    (σ : SRS G) {m : ℕ} (C : Fin m → G) (x : Fin evalPts → F)
    (aw₀ : Fin m → Fin (2 ^ σ.k) → F) (E : Fin m → Fin evalPts → F) (ξ r : F)
    (a : Fin (2 ^ σ.k) → F) (ρ : F)
    (hopen : openingRelationB σ (combinedCommitment ξ C)
      (combinedEvalVector (2 ^ σ.k) r x) (combinedInnerProduct ξ r E) a ρ)
    (ha : a = ∑ i : Fin m, ξ ^ (i : ℕ) • aw₀ i)
    {i : Fin m} {j : Fin evalPts}
    (hij : E i j ≠ innerProduct (aw₀ i) (evalVector (2 ^ σ.k) (x j))) :
    ξ ∈ badXiOf σ aw₀ x E ∨ r ∈ badROf σ aw₀ x E ξ := by
  by_contra hcon
  obtain ⟨hξ, hr⟩ := not_or.mp hcon
  exact hij (eval_pins_of_opening_of_eq σ C x aw₀ E ξ r hξ hr a ρ hopen ha i j)

end Kimchi.Verifier
