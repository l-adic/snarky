import Mathlib
import Kimchi.Commitment.IPA.Verify
import Kimchi.Commitment.IPA.Soundness.Tree
import Kimchi.Commitment.IPA.Soundness.Binding

/-!
# The Fiat–Shamir bridge and the headline soundness of the kimchi IPA

The top module of the IPA soundness development: the trust boundary. Everything
below the Fiat–Shamir bridge is proved; the bridge itself is the single stated
hypothesis.

`FiatShamirTree` turns an accepting verifier run into a clean accepting transcript
tree over a de-blinded commitment. It bundles the Fiat–Shamir rewinding (uniform
challenges yield three distinct sub-transcripts per round), the correspondence
between the verifier's multi-scalar check and the recursive tree, and the
Schnorr/hiding reduction that extracts the blinder `r` (so the tree is over the
non-hiding commitment `P - r • σ.h`). Given the tree, `ipaRelation_of_acceptV` and
`ipa_soundV` derive the opening witness, and `ipa_soundness` re-blinds it into the
opening relation.
-/

namespace Kimchi.Commitment.IPA

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## The tree derives the opening relation -/

/-- **The tree derives the opening relation.** For an eval vector `b` and
commitment `P`, an accepting transcript tree yields a non-hiding opening:
`IpaAcceptV σ.g b P v t → ∃ a, ⟨a, σ.g⟩ = P ∧ v = ⟨a, b⟩`.

`ipa_soundV` gives `a` with `⟨a, σ.g⟩ = P` and `commitGen b a = v`; since
`commitGen b a = ∑ i, a i • b i = ∑ i, a i * b i = innerProduct a b`, the second
conjunct is the inner product. -/
theorem ipaRelation_of_acceptV (σ : SRS G) (b : Fin (2 ^ σ.k) → F) (P : G) (v : F)
    (t : IpaTreeV F G σ.k) (h : IpaAcceptV σ.g b P v t) :
    ∃ a : Fin (2 ^ σ.k) → F, commitGen σ.g a = P ∧ v = innerProduct a b := by
  obtain ⟨a, hP, hv⟩ := ipa_soundV σ.g b P v t h
  refine ⟨a, hP, ?_⟩
  have hib : innerProduct a b = commitGen b a := by
    simp only [innerProduct, commitGen, smul_eq_mul]
  rw [hib]; exact hv.symm

/-! ## The Fiat–Shamir rewinding hypothesis -/

/-- **The Fiat–Shamir rewinding hypothesis** — the single trust assumption. An
accepting run yields a *de-blinded* accepting tree: a blinder `r : F` and a tree
`t` with

`accepts → ∃ (r : F) (t : IpaTreeV F G σ.k),
  IpaAcceptV σ.g (evalVector (2 ^ σ.k) x) (P - r • σ.h) v t`.

This bundles the rewinding proper (uniform challenges give three distinct
sub-transcripts per round), the correspondence between the verifier's multi-scalar
check and the recursive tree, and the Schnorr/hiding reduction extracting the
blinder `r`, so the tree is over the non-hiding de-blinded commitment
`P - r • σ.h`. -/
def FiatShamirTree (σ : SRS G) (P : G) (x v : F) (accepts : Prop) : Prop :=
  accepts → ∃ (r : F) (t : IpaTreeV F G σ.k),
    IpaAcceptV σ.g (evalVector (2 ^ σ.k) x) (P - r • σ.h) v t

/-! ## The headline soundness theorem -/

/-- **IPA knowledge soundness — lands in the opening relation.** Under the
Fiat–Shamir hypothesis, an accepting run yields a witness in the opening relation:

`VerifierAccepts σ proof P x v c u →
  ∃ (a : Fin (2 ^ σ.k) → F) (r : F), openingRelation σ P x v a r`.

The hypothesis yields a blinder `r` and an accepting tree over `P - r • σ.h`;
`ipaRelation_of_acceptV` extracts `a` with `⟨a, σ.g⟩ = P - r • σ.h` and
`v = ⟨a, evalVector (2 ^ σ.k) x⟩`. Re-blinding,
`commit σ a r = ⟨a, σ.g⟩ + r • σ.h = (P - r • σ.h) + r • σ.h = P`, so
`openingRelation σ P x v a r` holds. -/
theorem ipa_soundness (σ : SRS G) (proof : OpeningProof F G σ.k) (P : G) (x v c : F)
    (u : Fin σ.k → F)
    (hFS : FiatShamirTree σ P x v (VerifierAccepts σ proof P x v c u))
    (hacc : VerifierAccepts σ proof P x v c u) :
    ∃ (a : Fin (2 ^ σ.k) → F) (r : F), openingRelation σ P x v a r := by
  obtain ⟨r, t, ht⟩ := hFS hacc
  obtain ⟨a, hP, hv⟩ :=
    ipaRelation_of_acceptV σ (evalVector (2 ^ σ.k) x) (P - r • σ.h) v t ht
  refine ⟨a, r, ?_, hv⟩
  show commitGen σ.g a + r • σ.h = P
  rw [hP]
  abel

end Kimchi.Commitment.IPA
