import Bulletproof.Forking.Prover
import Bulletproof.Forking.Triviality
import Zcash.Snark.Soundness.Forking.Probability

/-!
# Knowledge soundness in the uniform-challenge game

The probabilistic capstone of the interactive model: a kimchi prover strategy that convinces the
verifier with probability **above the knowledge-error threshold** `kerr` — over uniformly drawn
challenge vectors — yields an opening witness, or a computed discrete-log relation exists.

The composition is `Zcash.Snark.extractable_of_prob` (uniform success above `kerr N (k+1)/N^(k+1)`
forks a full `(3,…,3)` acceptance tree) into `kimchi_opening_or_break_of_extractable`. The
challenge count is `σ.k + 1`: the `k` round challenges plus the Schnorr challenge, forked like
any other round.

## What stands between this and the deployed verifier

This theorem is the **interactive** (uniform-challenge) statement. The deployed verifier draws
its challenges from the Poseidon sponge (`Ipa.verify`, reflected into the abstract equations by
`verify_reflects` and `kimchiProverAccept_iff_verifierAcceptsAt`). The remaining gap — the
Fiat–Shamir/random-oracle reduction, relating a sponge-driven adversary's success to `hprob`
below — is exactly the Poseidon-as-RO trust boundary (Option A): provable in the random-oracle
model with query-loss accounting, not about any concrete hash. Discharging the declared
`poseidon_fiat_shamir_*` axioms against this theorem reduces their content to precisely that
transfer.
-/

namespace Bulletproof.Forking

open Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Acceptance of a prover strategy is decidable: it unfolds to finitely many equalities in `F`
and `G` along the branch. `extractable_of_prob` needs this to count the accepting set. -/
instance decKimchiProverAccept [DecidableEq F] [DecidableEq G] :
    {d : ℕ} → (pr : KimchiProver F G d) → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) →
    (U H : G) → (v : F) → (P : G) → (χ : Fin (d + 1) → F) →
    Decidable (kimchiProverAccept pr g b U H v P χ)
  | 0, .leaf _ _ _, _, _, _, _, _, _, _ =>
      inferInstanceAs (Decidable (_ ∧ _))
  | _ + 1, .node L R cont, g, b, U, H, v, P, χ =>
      decKimchiProverAccept (cont (χ 0)) (foldHalves g (χ 0)) (foldHalves b (χ 0)) U H v
        (P + (χ 0)⁻¹ • L + (χ 0) • R) (Fin.tail χ)

open scoped ENNReal in
/-- **Knowledge soundness, uniform-challenge game.** A prover strategy that convinces the wire
verifier (`kimchiProverAccept` = `VerifierAcceptsAt` branchwise, by
`kimchiProverAccept_iff_verifierAcceptsAt`) with probability above the knowledge error
`kerr |F| (k+1) / |F|^(k+1)`, together with the algebraic representation of its commitment,
yields an opening witness for `openingRelationB` — or a nontrivial discrete-log relation over
`(σ.g, σ.U, σ.h)` exists.

Neither conclusion can be conjured (`Forking/Triviality.lean`): the witness is extracted from
the strategy's own responses, and the relation carries explicit coefficients. No `hbind`
hypothesis — binding violations are returned, not assumed away. -/
theorem kimchi_knowledge_soundness [Fintype F] [DecidableEq F] [DecidableEq G] (σ : SRS G)
    (b : Fin (2 ^ σ.k) → F) (v : F) (P : G)
    (pg : Fin (2 ^ σ.k) → F) (pw : F) (hP : P = commitGen σ.g pg + pw • σ.h)
    (pr : KimchiProver F G σ.k)
    (hprob : (Zcash.Snark.kerr (Fintype.card F) (σ.k + 1) : ℝ≥0∞)
          / Fintype.card (Fin (σ.k + 1) → F)
        < (PMF.uniformOfFintype (Fin (σ.k + 1) → F)).toOuterMeasure
            (Finset.univ.filter (kimchiProverAccept pr σ.g b σ.U σ.h v P))) :
    (∃ (a : Fin (2 ^ σ.k) → F) (ρ : F), openingRelationB σ P b v a ρ) ∨
      Nonempty (Zcash.Snark.AlgebraicRelationWitness (F := F)
        (Zcash.Snark.augmentedBasis σ.g σ.U σ.h)) :=
  kimchi_opening_or_break_of_extractable σ b v P pg pw hP pr
    (Zcash.Snark.extractable_of_prob _ hprob)

/-! ## Self-audit: where this `Prop`-level statement carries content, and where it does not

`kimchi_knowledge_soundness` is a genuine theorem of arbitrary `F`-modules: for generic `G` its
conclusion is not provable without `hprob`. But at the **deployed instantiation** — a
1-dimensional point group — the disjunction is free with every hypothesis discarded: the left
disjunct already follows from linear algebra (`openingRelation_solvable`), exactly as
`Forking/Triviality.lean` showed for the old axioms' conclusion. Recorded as a theorem below,
per the vacuity discipline.

The content at deployed parameters therefore lives in the **data-valued** chain — the
certificate handed to `kimchiOpeningOrBreak`, whose `Σ' ⊕'` output cannot be conjured — and the
remaining work is to *compute* that certificate from a sponge-driven adversary (ironwood's
`Forking/Adversary` route: rewinding with explicit coins, measure-bounded failure), not to
strengthen this `Prop` wrapper. -/

/-- **At a 1-dimensional group the conclusion is free**: `hprob`, the strategy and the
representation are all discarded. This is the reason the `Prop`-level headline is *not* the
deployed-parameters endpoint — the data-valued `kimchiOpeningOrBreak` is. -/
theorem kimchi_knowledge_soundness_conclusion_free_at_1dim (σ : SRS G)
    (b : Fin (2 ^ σ.k) → F) (v : F) (P : G)
    (H₀ : G) (hspan : ∀ x : G, ∃ s : F, x = s • H₀)
    (hh : ∃ s : F, σ.h = s • H₀ ∧ s ≠ 0) (hb : ∃ i, b i ≠ 0) :
    (∃ (a : Fin (2 ^ σ.k) → F) (ρ : F), openingRelationB σ P b v a ρ) ∨
      Nonempty (Zcash.Snark.AlgebraicRelationWitness (F := F)
        (Zcash.Snark.augmentedBasis σ.g σ.U σ.h)) := by
  left
  obtain ⟨a, ρ, hPa, hv⟩ := openingRelation_solvable σ P b v H₀ hspan hh hb
  refine ⟨a, ρ, by simpa [commit] using hPa, ?_⟩
  simpa [innerProduct, commitGen, mul_comm] using hv.symm

end Bulletproof.Forking
