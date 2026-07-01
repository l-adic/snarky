/-
Copyright (c) 2025 O(1) Labs. Released under Apache 2.0 license.
-/
import Kimchi.Commitment.IPA.Basic

/-!
# Binding / Knowledge Soundness of the IPA Commitment

This file states the second headline security property of kimchi's IPA polynomial
commitment: *evaluation binding*. Where `Correctness.lean` says honest openings
are accepted, binding says it is computationally infeasible to make the verifier
accept two *different* evaluations of the same commitment at the same point.

In the Halo development the strong form of this property is packaged as
*computational witness-extended emulation* (Halo Definition 2 / Theorem 1): for
any efficient malicious prover there is an emulator that, alongside a transcript
indistinguishable from the real interaction, extracts a witness satisfying the
opening relation (`openingRelation`) whenever the transcript accepts. ArkLib's
`Commitment.extractability` predicate currently has its body stubbed to `False`,
so there is no provable upstream target; we therefore record the intended notion
directly (`witnessExtendedEmulation`) and prove the strictly weaker, fully
well-formed notion of evaluation binding (`Commitment.binding`).

The binding error is measured against the **discrete log relation assumption**
(Halo Definition 6), a foundational hardness hypothesis generalizing discrete log
to `n ≥ 2` random group elements. We render that assumption in ArkLib's
experiment shape, mirroring the worked `t`-SDH development
(`KZG/HardnessAssumptions.lean`), with the single commitment group `G` and `n`
independent generators in place of the SRS tower.

## Layout

* `dlRelationAdversary` / `dlRelationCondition` / `dlRelationGame` /
  `dlRelationExperiment` / `dlRelationAssumption` — the DL-relation hardness game
  (Halo §Definition 6), mirroring `tSdh*`.
* `witnessExtendedEmulation` — Halo Definition 2 recorded as the semantic goal.
* `ipa_binding` — evaluation binding of `ipa`, reduced to the DL-relation
  assumption (proof deferred; body `sorry`).

## References

* [Halo] Bowe, Grigg, Hopwood, *Recursive Proof Composition without a Trusted
  Setup*, §3, Definitions 2 and 6, Theorem 1.
* [tSdh] `ArkLib/Commitments/Functional/KZG/HardnessAssumptions.lean`,
  `ArkLib/Commitments/Functional/KZG/Binding.lean`.
-/

namespace Kimchi.Commitment.IPA.Binding

open Commitment OracleSpec OracleComp ProtocolSpec Polynomial
open scoped NNReal ENNReal

open Kimchi.Commitment.IPA

section DLRelation

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-! ## The discrete log relation assumption (Halo Definition 6)

The following blocks render the DL-relation hardness game in ArkLib's experiment
shape, mirroring the `t`-SDH development with the single commitment group `G` and
a vector of `n` independent random generators in place of the SRS tower. -/

/-- A *discrete-log-relation adversary* (Halo Definition 6) receives `n` random
group elements `(G₁, …, G_n) ∈ Gⁿ` and, running from an empty query cache,
returns an optional coefficient vector `a ∈ Fⁿ` — its proposed relation. The
analogue of `tSdhAdversary` with the SRS tower replaced by `n` independent
generators. -/
abbrev dlRelationAdversary (n : ℕ) :=
  (Fin n → G) → StateT unifSpec.QueryCache ProbComp (Option (Fin n → F))

/-- The DL-relation *winning condition*: relative to the sampled generators
`gens = (G₁, …, G_n)`, the adversary's output `a ∈ Fⁿ` wins when it is a
non-trivial discrete-log relation — some `aᵢ ≠ 0` and `∑ᵢ [aᵢ] Gᵢ = O` (the
group identity). The analogue of `tSdhCondition`.

The generators appear in the second component of the evaluated tuple (rather than
as an implicit parameter) because they are sampled inside `dlRelationGame` and
paired with the adversary's output, so that `Pr[dlRelationCondition | …]`
typechecks against the game's output type. -/
abbrev dlRelationCondition {n : ℕ} : ((Fin n → F) × (Fin n → G)) → Prop :=
  fun (a, gens) => (∃ i, a i ≠ 0) ∧ ∑ i, a i • gens i = 0

/-- The DL-relation *game* (analogue of `tSdhGame`): sample the `n` generators
`gens ← Gⁿ` uniformly as private setup randomness, run the adversary on them from
an empty query cache, and pair its output with the sampled generators so the
winning condition can be evaluated. -/
noncomputable def dlRelationGame [SampleableType G] (n : ℕ)
    (adversary : dlRelationAdversary (F := F) (G := G) n) :
    OptionT ProbComp ((Fin n → F) × (Fin n → G)) :=
  OptionT.mk (do
    let gens ← ($ᵗ (Fin n → G))
    let result ← (adversary gens).run' ∅
    pure (result.map (fun (a : Fin n → F) => (a, gens))))

/-- The DL-relation *experiment* (analogue of `tSdhExperiment`): the probability
that the game of `dlRelationGame` satisfies the winning condition of
`dlRelationCondition`, i.e. the adversary's success probability at producing a
non-trivial relation. -/
noncomputable def dlRelationExperiment [SampleableType G] (n : ℕ)
    (adversary : dlRelationAdversary (F := F) (G := G) n) : ℝ≥0∞ :=
  Pr[dlRelationCondition | dlRelationGame n adversary]

/-- The **discrete log relation assumption** (Halo Definition 6, analogue of
`tSdhAssumption`): for every adversary, the success probability at producing a
non-trivial discrete-log relation among `n` random generators is at most `error`.
A postulated hardness hypothesis, not derived from the group law; it is the
quantity the IPA binding error is measured against. -/
def dlRelationAssumption [SampleableType G] (n : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : dlRelationAdversary (F := F) (G := G) n),
    dlRelationExperiment n adversary ≤ (error : ℝ≥0∞)

end DLRelation

section Scheme

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] {d k : ℕ}

/-- Local oracle interface evaluating a coefficient vector as a polynomial (the
same instance declared in `Basic` and the KZG template), so `ipa` and
`Commitment.binding` typecheck here. -/
local instance evalOracle : OracleInterface (Fin d → F) where
  Query := F
  toOC.spec := F →ₒ F
  toOC.impl z := do
    let a ← read
    return ∑ i, a i * z ^ (i : ℕ)

/-! ## Witness-extended emulation (Halo Definition 2) -/

/-- *Computational witness-extended emulation* (Halo Definition 2), recorded as
the intended knowledge-soundness notion for the IPA opening argument. Relative to
the verification predicate `verifies`, there is an extractor that, for every
accepting `(statement, transcript)` pair, produces a witness lying in the opening
relation (`openingRelation`) of Halo §3.

This is a statement-level `Prop`-valued definition, not a theorem: it carries no
proof obligation. It faithfully captures the *soundness clause* of Halo
Definition 2 — `tr accepts ⇒ (x, w) ∈ R` via an existentially-quantified
extractor — but deliberately omits the transcript-indistinguishability and
expected-polynomial-time content (Halo Appendix A), which is deferred and for
which ArkLib has no formalized target (its `Commitment.extractability` body is
stubbed to `False`). -/
def witnessExtendedEmulation (srs : SRS G d)
    (verifies : (G × F × F) → OpeningProof F G k → Prop) : Prop :=
  ∃ extractor : (G × F × F) → OpeningProof F G k → (Fin d → F) × F,
    ∀ (stmt : G × F × F) (proof : OpeningProof F G k),
      verifies stmt proof → openingRelation srs stmt (extractor stmt proof)

/-! ## The algebraic extraction core -/

/-- **Two distinct openings yield a discrete-log relation** (Halo Appendix A, inner
algebraic layer; the IPA analogue of KZG's `t_sdh_cond_of_two_valid_openings`).

If two witnesses `(a₁, r₁) ≠ (a₂, r₂)` Pedersen-commit to the *same* group element
under the SRS `σ = (g, h)`, then their difference is a non-trivial discrete-log
relation among the `d + 1` generators `(g₀, …, g_{d-1}, h)` (the `Fin.snoc` of `g`
with `h`): some coordinate of `(a₁ - a₂, r₁ - r₂)` is nonzero, and
`∑ᵢ [a₁ᵢ - a₂ᵢ] gᵢ + [r₁ - r₂] h = 0`.

This is the inner, purely-algebraic layer consumed by the eventual `ipa_binding`
reduction; the outer rewinding extractor that produces the two openings is the
deferred research tail. -/
lemma dlRelation_of_two_openings (srs : SRS G d) (a₁ a₂ : Fin d → F) (r₁ r₂ : F)
    (hne : (a₁, r₁) ≠ (a₂, r₂))
    (hP : commit srs a₁ r₁ = commit srs a₂ r₂) :
    dlRelationCondition (n := d + 1)
      (Fin.snoc (a₁ - a₂) (r₁ - r₂), Fin.snoc srs.g srs.h) := by
  refine ⟨?_, ?_⟩
  · -- Non-triviality: some coordinate of the snoc'd vector is nonzero.
    by_cases haa : a₁ = a₂
    · -- Then the blinding factors must differ, witnessed at `Fin.last d`.
      have hr : r₁ ≠ r₂ := fun h => hne (by rw [haa, h])
      exact ⟨Fin.last d, by rw [Fin.snoc_last]; exact sub_ne_zero.mpr hr⟩
    · -- Otherwise the coefficient vectors differ at some `j`, witnessed at `j.castSucc`.
      obtain ⟨j, hj⟩ := Function.ne_iff.mp haa
      exact ⟨j.castSucc, by
        rw [Fin.snoc_castSucc, Pi.sub_apply]; exact sub_ne_zero.mpr hj⟩
  · -- Sum clause: the difference telescopes to `commit … - commit … = P - P = 0`.
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.sub_apply]
    have key : (∑ i : Fin d, (a₁ i - a₂ i) • srs.g i) + (r₁ - r₂) • srs.h
        = commit srs a₁ r₁ - commit srs a₂ r₂ := by
      simp only [commit, sub_smul, Finset.sum_sub_distrib]
      abel
    rw [key, hP, sub_self]

/-- **Two openings to different values yield a discrete-log relation** (Halo
Appendix A, the faithful interface above `dlRelation_of_two_openings`). If two
witnesses `(a₁, r₁)`, `(a₂, r₂)` both satisfy the opening relation for the *same*
commitment `P` at the *same* point `x` but for *distinct* claimed values
`v₁ ≠ v₂`, then their difference is a non-trivial discrete-log relation among the
`d + 1` generators `(g₀, …, g_{d-1}, h)`.

This derives the pair-distinctness hypothesis of `dlRelation_of_two_openings`
from the value-distinctness the binding game supplies, and threads the
shared-commitment equality through. It is the entire algebraic content of the
binding contradiction *below* the rewinding hole — no probabilistic or rewinding
content. -/
lemma dlRelation_of_two_opening_witnesses (srs : SRS G d)
    (P : G) (x v₁ v₂ : F) (a₁ a₂ : Fin d → F) (r₁ r₂ : F)
    (h₁ : openingRelation srs (P, x, v₁) (a₁, r₁))
    (h₂ : openingRelation srs (P, x, v₂) (a₂, r₂))
    (hv : v₁ ≠ v₂) :
    dlRelationCondition (n := d + 1)
      (Fin.snoc (a₁ - a₂) (r₁ - r₂), Fin.snoc srs.g srs.h) := by
  obtain ⟨hcom₁, hval₁⟩ := h₁
  obtain ⟨hcom₂, hval₂⟩ := h₂
  dsimp only at hcom₁ hval₁ hcom₂ hval₂
  -- `hcom₁ : P = commit srs a₁ r₁`, `hval₁ : v₁ = ∑ i, a₁ i * x ^ (i:ℕ)` (and `₂`).
  apply dlRelation_of_two_openings srs a₁ a₂ r₁ r₂
  · -- Pair-distinctness from value-distinctness: if `a₁ = a₂` the two value sums
    -- coincide, forcing `v₁ = v₂`.
    intro heq
    apply hv
    have ha : a₁ = a₂ := congrArg Prod.fst heq
    rw [hval₁, hval₂, ha]
  · -- Shared commitment: both `commit`s equal `P`.
    rw [← hcom₁, ← hcom₂]

/-! ## Evaluation binding of the IPA scheme (Halo Theorem 1) -/

/-- **Binding of the IPA scheme** (Halo Theorem 1). The IPA commitment scheme
`ipa` satisfies ArkLib evaluation `Commitment.binding` with error `dlError`,
provided the discrete log relation assumption holds with that error: no efficient
adversary can produce a commitment `P`, an evaluation point `x`, and two distinct
claims `v₁ ≠ v₂` together with malicious openings driving the protocol to
acceptance for both.

The reduction (rewinding the `k = log₂ d` folding rounds to extract two opening
witnesses `(a₁, r₁) ≠ (a₂, r₂)` for the same `P`, whose difference is a
non-trivial discrete-log relation among the random generators) is Halo Appendix A
and is deferred to a later phase; the body is `sorry`. -/
theorem ipa_binding [SampleableType F] [SampleableType G]
    [∀ i, VCVCompatible ((pSpec F G k).Challenge i)]
    [∀ i, SampleableType ((pSpec F G k).Challenge i)]
    [[(pSpec F G k).Challenge]ₒ.Inhabited]
    [[(pSpec F G k).Challenge]ₒ.Fintype]
    (dlError : ℝ≥0)
    (hdl : dlRelationAssumption (F := F) (G := G) d dlError) :
    Commitment.binding (init := pure ∅) (impl := randomOracle)
      (ipa (F := F) (G := G) (d := d) (k := k)) dlError := sorry

end Scheme

end Kimchi.Commitment.IPA.Binding
