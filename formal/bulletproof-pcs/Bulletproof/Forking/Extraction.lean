import Bulletproof.Forking.Triviality
import Zcash.Snark.Soundness.Forking.Probability

/-!
# A content-bearing IPA extraction theorem, on ironwood's strategy

`Bulletproof/Forking/Triviality.lean` shows the shape the declared Fiat–Shamir axioms conclude
in — `∃ ρ t, IpaAcceptV …` — is satisfiable unconditionally at the deployed instantiation, so
deriving it establishes nothing. This module states and proves the replacement, following
`zcash/ironwood`'s approach.

## Why this one has content

Ironwood's `Zcash.Snark.Extractable` (`Forking/Tree.lean:26`) is a predicate on the *acceptance
predicate itself*:

```
Extractable acc  ↔  ∃ three distinct nonzero challenges, each continuing to an Extractable
                    subtree, with `acc` holding at every leaf
```

so a witness is a ternary tree **all of whose leaves are genuine acceptances**. That cannot be
manufactured by linear algebra: the trivial construction of `Triviality.lean` invents node data
out of an opening witness, and satisfies no acceptance predicate at all.

The hypothesis is likewise not free. `Zcash.Snark.extractable_of_prob`
(`Forking/Probability.lean:354`) requires the prover to succeed with probability *above the
knowledge-error threshold* `kerr N d / N ^ d` over uniformly drawn challenges. A prover that
does not actually convince the verifier cannot satisfy it.

## The model

The prover is an interactive strategy, and the ordering is what carries the soundness: at each
round it commits to `(L, R)` and the value cross-terms **before** seeing that round's challenge,
then continues as a function of it. That is exactly the shape of `Strategy` below — a `d`-deep
tree of responses branching on the challenge — and it is why a success-probability bound implies
knowledge.

The extraction from a tree is already in the package (`ipaRelation_of_acceptV`, the 3-point
Vandermonde recursion); what is new here is the bridge from ironwood's *predicate-level*
`Extractable` to our *data-level* `IpaTreeV`, and the composition into a knowledge statement.
-/

namespace Bulletproof.Forking

open Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- An interactive prover strategy for the IPA reduction, to depth `d`.

At each round the prover commits to the round message — the two group elements `L`, `R` and the
two value cross-terms `Lv`, `Rv` — and only then receives the challenge, continuing as a
function of it. At the leaf it opens with a single scalar.

The commit-then-challenge order is the whole point: a strategy cannot choose its round message
after seeing the challenge, which is what makes a success-probability hypothesis meaningful. -/
inductive Strategy (F G : Type*) : ℕ → Type _ where
  /-- The final opening scalar. -/
  | leaf : F → Strategy F G 0
  /-- A round message `(L, R, Lv, Rv)`, then the continuation as a function of the challenge. -/
  | node {d : ℕ} : G → G → F → F → (F → Strategy F G d) → Strategy F G (d + 1)

/-- The verifier's acceptance of a strategy at a given challenge vector: fold the generators,
the evaluation vector, the commitment and the value by each challenge in turn — the same fold
as `IpaAcceptV` — and check the leaf equations.

This is the `acc : (Fin d → F) → Prop` that ironwood's `Extractable`/`extractable_of_prob` are
stated over. -/
def stratAccept : {d : ℕ} → Strategy F G d → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) →
    G → F → (Fin d → F) → Prop
  | 0, .leaf c, g, b, P, v, _ =>
      P = commitGen g (fun _ => c) ∧ v = commitGen b (fun _ => c)
  | _ + 1, .node L R Lv Rv k, g, b, P, v, χ =>
      stratAccept (k (χ 0)) (foldHalves g (χ 0)) (foldHalves b (χ 0))
        (P + (χ 0)⁻¹ • L + (χ 0) • R) (v + (χ 0)⁻¹ • Lv + (χ 0) • Rv) (Fin.tail χ)

/-- **The bridge: ironwood's predicate-level tree becomes our data-level tree.** An
`Extractable` acceptance predicate for a strategy yields an `IpaTreeV` satisfying `IpaAcceptV` —
the node data being the strategy's own round messages and the extracted challenge triples.

This is the step that makes ironwood's machinery deliver *our* `IpaTreeV`, and hence feed the
existing Vandermonde extraction `ipaRelation_of_acceptV`. -/
theorem ipaTreeV_of_extractable : {d : ℕ} → (S : Strategy F G d) → (g : Fin (2 ^ d) → G) →
    (b : Fin (2 ^ d) → F) → (P : G) → (v : F) →
    Zcash.Snark.Extractable (stratAccept S g b P v) →
    ∃ t : IpaTreeV F G d, IpaAcceptV g b P v t
  | 0, .leaf c, _, _, _, _, h => ⟨.leaf c, h⟩
  | _ + 1, .node L R Lv Rv k, g, b, P, v, h => by
      obtain ⟨u₁, u₂, u₃, h12, h13, h23, hu₁, hu₂, hu₃, e₁, e₂, e₃⟩ := h
      -- Fixing the first challenge turns the strategy's acceptance into the continuation's,
      -- against the folded generators, eval vector, commitment and value.
      have key : ∀ u : F,
          (fun rest => stratAccept (Strategy.node L R Lv Rv k) g b P v (Fin.cons u rest)) =
            stratAccept (k u) (foldHalves g u) (foldHalves b u)
              (P + u⁻¹ • L + u • R) (v + u⁻¹ • Lv + u • Rv) := by
        intro u; funext rest; simp [stratAccept]
      rw [key u₁] at e₁
      rw [key u₂] at e₂
      rw [key u₃] at e₃
      obtain ⟨t₁, ht₁⟩ := ipaTreeV_of_extractable (k u₁) _ _ _ _ e₁
      obtain ⟨t₂, ht₂⟩ := ipaTreeV_of_extractable (k u₂) _ _ _ _ e₂
      obtain ⟨t₃, ht₃⟩ := ipaTreeV_of_extractable (k u₃) _ _ _ _ e₃
      exact ⟨.node L R Lv Rv u₁ u₂ u₃ t₁ t₂ t₃,
        h12, h13, h23, hu₁, hu₂, hu₃, ht₁, ht₂, ht₃⟩

/-- **The replacement theorem.** A prover strategy that convinces the verifier with probability
above the knowledge-error threshold *knows* an opening: there is a witness `a` and blinder `ρ`
satisfying the opening relation.

Unlike `FiatShamirTreeB`, this is not satisfiable by construction — the hypothesis demands
genuine acceptance on a `kerr`-sized fraction of challenge vectors, and the conclusion is
extracted from the strategy's own messages. -/
theorem ipa_knowledge_soundness [Fintype F] [DecidableEq F] (σ : SRS G)
    (S : Strategy F G σ.k) (P : G) (b : Fin (2 ^ σ.k) → F) (v : F)
    [DecidablePred (stratAccept S σ.g b P v)]
    (hprob : (Zcash.Snark.kerr (Fintype.card F) σ.k : ENNReal) / Fintype.card (Fin σ.k → F)
        < (PMF.uniformOfFintype (Fin σ.k → F)).toOuterMeasure
            (Finset.univ.filter (stratAccept S σ.g b P v))) :
    ∃ (a : Fin (2 ^ σ.k) → F) (ρ : F), openingRelationB σ P b v a ρ := by
  have hext := Zcash.Snark.extractable_of_prob (stratAccept S σ.g b P v) hprob
  obtain ⟨t, ht⟩ := ipaTreeV_of_extractable S σ.g b P v hext
  obtain ⟨a, hP, hv⟩ := ipaRelation_of_acceptV σ b P v t ht
  exact ⟨a, 0, by simpa [commit] using hP, hv⟩

/-! ## Self-audit: the conclusion is still free at the deployed instantiation

`ipa_knowledge_soundness` fixes the *hypothesis* — `Extractable` cannot be met without genuinely
convincing the verifier on a `kerr`-sized fraction of challenge vectors. It does **not** fix the
*conclusion*, and that is the defect `Triviality.lean` identified.

The theorem is stated over an abstract `(G, Module F G)`, where `∃ a ρ, openingRelationB …` is
not provable outright. But it is consumed at the deployed Pasta instantiation, where the point
group is a 1-dimensional `F`-vector space — and there the conclusion follows from
`openingRelation_solvable` with the probability hypothesis discarded, exactly as
`fiatShamirTreeB_trivial` discards `A`.

So at the point of use this theorem is worth no more than the axiom it was meant to replace.
Recording it as a checkable claim rather than a caveat in prose. -/
theorem ipa_knowledge_soundness_conclusion_free (σ : SRS G) (P : G) (b : Fin (2 ^ σ.k) → F)
    (v : F) (H : G) (hspan : ∀ x : G, ∃ s : F, x = s • H)
    (hh : ∃ s : F, σ.h = s • H ∧ s ≠ 0) (hb : ∃ i, b i ≠ 0) :
    ∃ (a : Fin (2 ^ σ.k) → F) (ρ : F), openingRelationB σ P b v a ρ := by
  obtain ⟨a, ρ, hP, hv⟩ := openingRelation_solvable σ P b v H hspan hh hb
  refine ⟨a, ρ, by simpa [commit] using hP, ?_⟩
  simpa [innerProduct, commitGen, mul_comm] using hv.symm

end Bulletproof.Forking
