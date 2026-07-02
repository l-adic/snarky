import Mathlib
import Kimchi.Commitment.IPA.Basic
import Kimchi.Commitment.IPA.Soundness.Linear

/-!
# IPA soundness: the transcript tree and 3-special soundness

The IPA recursion, packaged as a `3`-ary transcript *tree*. Each node records the
prover's cross-terms and three challenges, with three sub-transcripts; the whole
tree witnesses that the verifier accepts three consistent runs at every round.

The main result (`ipa_soundV`) is that an accepting tree yields a witness for the
full opening relation, by induction on the tree: each node applies the 3-special
round soundness of `Soundness.Linear` (`ipa_round_commit_with_coeffs`,
`vandermonde3`) to combine the three sub-witnesses, and reassembles the halves
with `commitGen_append`. The generators fold by the challenge `u`
(`g ↦ gLo + u • gHi`) and the commitment recombines by `u⁻¹ • L + u • R`.
-/

namespace Kimchi.Commitment.IPA

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Halving the index set

Using `2 ^ k + 2 ^ k = 2 ^ (k + 1)` and the sum-equivalence
`Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1))`: `loHalf`/`hiHalf` restrict a
length-`2^{k+1}` vector to its first/last `2^k` indices, and `append`
concatenates two halves. -/

/-- Lower half: the restriction of a length-`2^{k+1}` vector to its first `2^k`
indices. -/
def loHalf {α : Type*} {k : ℕ} (f : Fin (2 ^ (k + 1)) → α) : Fin (2 ^ k) → α :=
  fun i => f (Fin.castLE (by rw [pow_succ]; omega) i)

/-- Upper half: the restriction of a length-`2^{k+1}` vector to its last `2^k`
indices (offset by `2^k`). -/
def hiHalf {α : Type*} {k : ℕ} (f : Fin (2 ^ (k + 1)) → α) : Fin (2 ^ k) → α :=
  fun i => f ⟨2 ^ k + i.val, by have := i.isLt; rw [pow_succ]; omega⟩

/-- Concatenation of two length-`2^k` halves into a length-`2^{k+1}` vector. -/
def append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) : Fin (2 ^ (k + 1)) → α :=
  fun i => if h : i.val < 2 ^ k then lo ⟨i.val, h⟩
    else hi ⟨i.val - 2 ^ k, by
      have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
      have := i.isLt; omega⟩

/-- The tree's generator / eval-vector fold on the two halves: `foldHalves v u =
loHalf v + u • hiHalf v` — the high half scaled by the challenge `u`. Generic over
the module `M` so it serves both the generators (`M := G`) and the eval vector
(`M := F`). -/
def foldHalves {M : Type*} [AddCommGroup M] [Module F M] {k : ℕ}
    (v : Fin (2 ^ (k + 1)) → M) (u : F) : Fin (2 ^ k) → M :=
  loHalf v + u • hiHalf v

/-- The lower half of an `append` is the lower part. -/
theorem loHalf_append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) :
    loHalf (append lo hi) = lo := by
  funext i
  simp only [loHalf, append, Fin.val_castLE, dif_pos i.isLt, Fin.eta]

/-- The upper half of an `append` is the upper part. -/
theorem hiHalf_append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) :
    hiHalf (append lo hi) = hi := by
  funext i
  have h : ¬ (2 ^ k + i.val < 2 ^ k) := by omega
  simp only [hiHalf, append, dif_neg h]
  congr 1
  apply Fin.ext
  simp

/-- A length-`2^{k+1}` commitment splits over the two halves:
`⟨a, g⟩ = ⟨loHalf a, loHalf g⟩ + ⟨hiHalf a, hiHalf g⟩`. -/
theorem commitGen_split {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (a : Fin (2 ^ (k + 1)) → F) :
    commitGen g a = commitGen (loHalf g) (loHalf a) + commitGen (hiHalf g) (hiHalf a) := by
  have e : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
  let φ : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) := finSumFinEquiv.trans (finCongr e)
  simp only [commitGen]
  rw [← φ.sum_comp (fun j => a j • g j), Fintype.sum_sum_type]
  congr 1

/-- A commitment of an `append` splits over the parent halves:
`⟨append a_lo a_hi, g⟩ = ⟨a_lo, loHalf g⟩ + ⟨a_hi, hiHalf g⟩`. -/
theorem commitGen_append {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (a_lo a_hi : Fin (2 ^ k) → F) :
    commitGen g (append a_lo a_hi) = commitGen (loHalf g) a_lo + commitGen (hiHalf g) a_hi := by
  rw [commitGen_split, loHalf_append, hiHalf_append]

/-! ## The opening-relation tree -/

/-- A `3`-ary IPA transcript tree carrying both the commitment cross-terms
`L`, `R : G` and the inner-product cross-terms `Lv`, `Rv : F` per round; a node
also holds three round challenges and three depth-`d` sub-transcripts, and a leaf
holds the final folded scalar. -/
inductive IpaTreeV (F G : Type*) : ℕ → Type _ where
  | leaf : F → IpaTreeV F G 0
  | node {d : ℕ} : G → G → F → F → F → F → F →
      IpaTreeV F G d → IpaTreeV F G d → IpaTreeV F G d → IpaTreeV F G (d + 1)

/-- Acceptance for the full relation: at a node the three challenges are distinct
and nonzero, and each sub-transcript is accepted against the folded data — the
generators `g` and eval vector `b` folded by `foldHalves`, the commitment `P` by
`uᵢ⁻¹ • L + uᵢ • R`, and the value `v` by `uᵢ⁻¹ • Lv + uᵢ • Rv`; a leaf checks
`P = ⟨const c, g⟩` and `v = ⟨const c, b⟩`. -/
def IpaAcceptV : {d : ℕ} → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → G → F → IpaTreeV F G d → Prop
  | 0, g, b, P, v, .leaf c => P = commitGen g (fun _ => c) ∧ v = commitGen b (fun _ => c)
  | _ + 1, g, b, P, v, .node L R Lv Rv u₁ u₂ u₃ t₁ t₂ t₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        IpaAcceptV (foldHalves g u₁) (foldHalves b u₁)
          (P + u₁⁻¹ • L + u₁ • R) (v + u₁⁻¹ • Lv + u₁ • Rv) t₁ ∧
        IpaAcceptV (foldHalves g u₂) (foldHalves b u₂)
          (P + u₂⁻¹ • L + u₂ • R) (v + u₂⁻¹ • Lv + u₂ • Rv) t₂ ∧
        IpaAcceptV (foldHalves g u₃) (foldHalves b u₃)
          (P + u₃⁻¹ • L + u₃ • R) (v + u₃⁻¹ • Lv + u₃ • Rv) t₃

/-- Full opening-relation soundness of the tree. An accepting transcript tree
yields a single witness `a` that both opens the commitment and gives the claimed
inner product: `IpaAcceptV g b P v t → ∃ a, ⟨a, g⟩ = P ∧ ⟨a, b⟩ = v` (with
`⟨a, b⟩` read as the commitment at `G := F`). The two conjuncts share the same
`a`: the explicit Vandermonde combination applied once to `(g, P, L, R)` and once
to `(b, v, Lv, Rv)`. Binding-free. -/
theorem ipa_soundV : {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (P : G) → (v : F) →
    (t : IpaTreeV F G d) → IpaAcceptV g b P v t →
    ∃ a : Fin (2 ^ d) → F, commitGen g a = P ∧ commitGen b a = v
  | 0, g, b, P, v, .leaf c, h => ⟨fun _ => c, h.1.symm, h.2.symm⟩
  | _ + 1, g, b, P, v, .node L R Lv Rv u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, ha₁, ha₂, ha₃⟩ := h
      obtain ⟨c₁, hP₁, hv₁⟩ :=
        ipa_soundV (foldHalves g u₁) (foldHalves b u₁) _ _ t₁ ha₁
      obtain ⟨c₂, hP₂, hv₂⟩ :=
        ipa_soundV (foldHalves g u₂) (foldHalves b u₂) _ _ t₂ ha₂
      obtain ⟨c₃, hP₃, hv₃⟩ :=
        ipa_soundV (foldHalves g u₃) (foldHalves b u₃) _ _ t₃ ha₃
      obtain ⟨l₁, l₂, l₃, hl0, hl1, hl2⟩ := vandermonde3 u₁ u₂ u₃ h12 h13 h23
      refine ⟨append (l₁ • (u₁ • c₁) + l₂ • (u₂ • c₂) + l₃ • (u₃ • c₃))
        (l₁ • (u₁ ^ 2 • c₁) + l₂ • (u₂ ^ 2 • c₂) + l₃ • (u₃ ^ 2 • c₃)), ?_, ?_⟩
      · rw [commitGen_append]
        exact ipa_round_commit_with_coeffs (loHalf g) (hiHalf g) P L R
          c₁ c₂ c₃ u₁ u₂ u₃ l₁ l₂ l₃ hl0 hl1 hl2 hu₁ hu₂ hu₃ hP₁ hP₂ hP₃
      · rw [commitGen_append]
        exact ipa_round_commit_with_coeffs (loHalf b) (hiHalf b) v Lv Rv
          c₁ c₂ c₃ u₁ u₂ u₃ l₁ l₂ l₃ hl0 hl1 hl2 hu₁ hu₂ hu₃ hv₁ hv₂ hv₃

end Kimchi.Commitment.IPA
