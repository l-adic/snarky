import Mathlib
import Kimchi.Commitment.IPA.Basic
import Kimchi.Commitment.IPA.Soundness.Linear

/-!
# Binding of the kimchi IPA commitment as discrete-log-relation hardness

Binding is the sole cryptographic assumption on the group, made auditable: a
binding violation is reduced to a nontrivial discrete-log relation among the
generators `σ.g` and the blinding base `σ.h`, and binding is shown to be *exactly*
DL-relation triviality.

The commitment is hiding (`commit σ a r = ⟨a, σ.g⟩ + r • σ.h`), so a witness is
the pair `(a, r)` and a discrete-log relation ranges over `[σ.g, σ.h]`: a pair
`(r, r_h)` with `⟨r, σ.g⟩ + r_h • σ.h = 0`.
-/

namespace Kimchi.Commitment.IPA

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- **Commitment binding (hiding form).** The hiding commitment is injective in its
witness *pair*: the map `(a, r) ↦ commit σ a r = ⟨a, σ.g⟩ + r • σ.h` is injective. -/
@[reducible] def CommitmentBinding (σ : SRS G) : Prop :=
  Function.Injective (fun p : (Fin (2 ^ σ.k) → F) × F => commit σ p.1 p.2)

/-- **Discrete-log relation among `[σ.g, σ.h]`.** A pair `(r, r_h)` with
`⟨r, σ.g⟩ + r_h • σ.h = 0`. It is nontrivial when `(r, r_h) ≠ 0`. DL-relation
hardness is the assumption that no feasible adversary finds a nontrivial relation. -/
@[reducible] def DLRelation (σ : SRS G) (r : Fin (2 ^ σ.k) → F) (r_h : F) : Prop :=
  commitGen σ.g r + r_h • σ.h = 0

/-- **Binding is exactly DL-relation hardness.** `CommitmentBinding σ` holds iff
every discrete-log relation among `[σ.g, σ.h]` is trivial. -/
theorem commitmentBinding_iff_no_relation (σ : SRS G) :
    CommitmentBinding (F := F) σ ↔
      ∀ (r : Fin (2 ^ σ.k) → F) (r_h : F), DLRelation σ r r_h → r = 0 ∧ r_h = 0 := by
  constructor
  · -- (⟹) A relation `(r, r_h)` is a collision between `(r, r_h)` and `(0, 0)`.
    intro hb r r_h hr
    have hr' : commitGen σ.g r + r_h • σ.h = 0 := hr
    have hcol : commit σ r r_h = commit σ (0 : Fin (2 ^ σ.k) → F) (0 : F) := by
      simp only [commit, hr']
      simp [commitGen]
    have h := @hb (r, r_h) (0, 0) hcol
    rw [Prod.mk.injEq] at h
    exact h
  · -- (⟸) A collision yields the relation `(a - a', r - r')`, which is trivial.
    intro hnr p q hpq
    have hpq' : commit σ p.1 p.2 = commit σ q.1 q.2 := hpq
    have hr : DLRelation σ (p.1 - q.1) (p.2 - q.2) := by
      show commitGen σ.g (p.1 - q.1) + (p.2 - q.2) • σ.h = 0
      rw [commitGen_sub, sub_smul]
      have hrw : commitGen σ.g p.1 - commitGen σ.g q.1 + (p.2 • σ.h - q.2 • σ.h)
          = commit σ p.1 p.2 - commit σ q.1 q.2 := by
        simp only [commit]; abel
      rw [hrw, hpq', sub_self]
    obtain ⟨h1, h2⟩ := hnr _ _ hr
    rw [sub_eq_zero] at h1 h2
    exact Prod.ext_iff.mpr ⟨h1, h2⟩

/-- **The opening is unique under binding.** Two witnesses opening the same
commitment `P` at `x` to the same value `v` coincide. -/
theorem ipaRelation_unique {σ : SRS G} {P : G} {x v : F}
    {a a' : Fin (2 ^ σ.k) → F} {r r' : F} (hb : CommitmentBinding (F := F) σ)
    (h : openingRelation σ P x v a r) (h' : openingRelation σ P x v a' r') :
    (a, r) = (a', r') := by
  -- Both witnesses satisfy `commit σ · · = P`; injectivity forces them equal.
  exact @hb (a, r) (a', r') (h.1.trans h'.1.symm)

end Kimchi.Commitment.IPA
