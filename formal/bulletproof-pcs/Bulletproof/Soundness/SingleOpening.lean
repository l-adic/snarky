import Mathlib
import Bulletproof.Protocol

/-!
# Single-opening soundness of the abstract kimchi IPA

Knowledge soundness of one IPA opening — one committed polynomial, one point — axiom-free:
an accepting transcript yields an opening witness. The round algebra (§ one IPA round),
the `3`-ary transcript tree and its `3`-special soundness (§ transcript tree), commitment
binding as discrete-log-relation triviality (§ binding), and the Fiat–Shamir bridge to the
opening relation (§ the headline). The batched and chunked openings build on this in
`Bulletproof.Soundness`.
-/

/-!
## The linear algebra of one IPA round (soundness)

The elementary algebra behind IPA soundness: bilinearity of the generator
commitment `⟨a, g⟩`, the three-point Vandermonde functional, and the
3-special-soundness of a single round.

A round folds the generators by the challenge `u` (`g ↦ gLo + u • gHi`) and
recombines the commitment as `P + u⁻¹ • L + u • R`. From three sub-openings at
distinct nonzero challenges the round is 3-special-sound: an explicit Vandermonde
combination of the three folded witnesses opens the parent commitment `P`, with no
binding assumption — pure module linear algebra.
-/

namespace Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Bilinearity of the generator commitment

The commitment `⟨a, g⟩ = ∑ i, a i • g i` is bilinear: additive and homogeneous in
both the witness `a` and the generators `g`. -/

/-- Additivity in the witness: `⟨a + a', g⟩ = ⟨a, g⟩ + ⟨a', g⟩`. -/
private theorem commitGen_add_left {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a + a') = commitGen g a + commitGen g a' := by
  simp only [commitGen, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Homogeneity in the witness: `⟨c • a, g⟩ = c • ⟨a, g⟩`. -/
private theorem commitGen_smul_left {n : ℕ} (g : Fin n → G) (c : F) (a : Fin n → F) :
    commitGen g (c • a) = c • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Additivity in the generators: `⟨a, g + g'⟩ = ⟨a, g⟩ + ⟨a, g'⟩`. -/
private theorem commitGen_add_gen {n : ℕ} (g g' : Fin n → G) (a : Fin n → F) :
    commitGen (g + g') a = commitGen g a + commitGen g' a := by
  simp only [commitGen, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Homogeneity in the generators: `⟨a, c • g⟩ = c • ⟨a, g⟩`. -/
private theorem commitGen_smul_gen {n : ℕ} (c : F) (g : Fin n → G) (a : Fin n → F) :
    commitGen (c • g) a = c • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm (a i) c (g i)

/-- Subtractivity in the witness: `⟨a - a', g⟩ = ⟨a, g⟩ - ⟨a', g⟩`. -/
private theorem commitGen_sub {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a - a') = commitGen g a - commitGen g a' := by
  simp only [commitGen, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-! ## The three-point Vandermonde functional -/

/-- For distinct `u₁, u₂, u₃` there are coefficients `l₁, l₂, l₃` with `Σ lᵢ = 0`,
`Σ lᵢuᵢ = 1`, and `Σ lᵢuᵢ² = 0`: the functional `p ↦ Σ lᵢ · p(uᵢ)` reads off the
linear coefficient of any degree-≤2 polynomial `p`. -/
theorem vandermonde3 (u₁ u₂ u₃ : F) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃)
    (h23 : u₂ ≠ u₃) :
    ∃ l₁ l₂ l₃ : F, (l₁ + l₂ + l₃ = 0)
      ∧ (l₁ * u₁ + l₂ * u₂ + l₃ * u₃ = 1)
      ∧ (l₁ * u₁ ^ 2 + l₂ * u₂ ^ 2 + l₃ * u₃ ^ 2 = 0) := by
  have d12 : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr h12
  have d13 : u₁ - u₃ ≠ 0 := sub_ne_zero.mpr h13
  have d23 : u₂ - u₃ ≠ 0 := sub_ne_zero.mpr h23
  have d21 : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have d31 : u₃ - u₁ ≠ 0 := sub_ne_zero.mpr h13.symm
  have d32 : u₃ - u₂ ≠ 0 := sub_ne_zero.mpr h23.symm
  refine ⟨-(u₂ + u₃) / ((u₁ - u₂) * (u₁ - u₃)), -(u₁ + u₃) / ((u₂ - u₁) * (u₂ - u₃)),
    -(u₁ + u₂) / ((u₃ - u₁) * (u₃ - u₂)), ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-! ## Round soundness (3-special) -/

/-- One IPA round is 3-special-sound for the commitment, with an explicit witness.
Given three openings `⟨cᵢ, gLo + uᵢ • gHi⟩ = P + uᵢ⁻¹ • L + uᵢ • R` against the
`uᵢ`-folded generators at distinct nonzero challenges, and Vandermonde coefficients
`lᵢ`, the parent witness `aLo = Σ lᵢ(uᵢ cᵢ)`, `aHi = Σ lᵢ(uᵢ² cᵢ)` opens `P`:
`⟨aLo, gLo⟩ + ⟨aHi, gHi⟩ = P`. No binding assumption; the witness is explicit, so
the same combination serves the inner-product side at `G := F`. -/
private theorem ipa_round_commit_with_coeffs {m : ℕ} (g_lo g_hi : Fin m → G) (P L R : G)
    (c₁ c₂ c₃ : Fin m → F) (u₁ u₂ u₃ l₁ l₂ l₃ : F)
    (hl0 : l₁ + l₂ + l₃ = 0) (hl1 : l₁ * u₁ + l₂ * u₂ + l₃ * u₃ = 1)
    (hl2 : l₁ * u₁ ^ 2 + l₂ * u₂ ^ 2 + l₃ * u₃ ^ 2 = 0)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (e₁ : commitGen (g_lo + u₁ • g_hi) c₁ = P + u₁⁻¹ • L + u₁ • R)
    (e₂ : commitGen (g_lo + u₂ • g_hi) c₂ = P + u₂⁻¹ • L + u₂ • R)
    (e₃ : commitGen (g_lo + u₃ • g_hi) c₃ = P + u₃⁻¹ • L + u₃ • R) :
    commitGen g_lo (l₁ • (u₁ • c₁) + l₂ • (u₂ • c₂) + l₃ • (u₃ • c₃))
        + commitGen g_hi
            (l₁ • (u₁ ^ 2 • c₁) + l₂ • (u₂ ^ 2 • c₂)
              + l₃ • (u₃ ^ 2 • c₃))
      = P := by
  -- Expand the folded generators: the generator half carries `u`, not `u⁻¹`.
  rw [commitGen_add_gen, commitGen_smul_gen] at e₁ e₂ e₃
  -- e_i : commitGen g_lo c_i + u_i • commitGen g_hi c_i = P + u_i⁻¹ • L + u_i • R
  -- Multiply each opening by `u_i` to clear the `u_i⁻¹` on `L`; the `g_hi` half picks up `u_i²`.
  have s₁ : u₁ • commitGen g_lo c₁ + u₁ ^ 2 • commitGen g_hi c₁ = u₁ • P + L + u₁ ^ 2 • R := by
    have h := congrArg (u₁ • ·) e₁
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₁, one_smul, ← pow_two] at h
    exact h
  have s₂ : u₂ • commitGen g_lo c₂ + u₂ ^ 2 • commitGen g_hi c₂ = u₂ • P + L + u₂ ^ 2 • R := by
    have h := congrArg (u₂ • ·) e₂
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₂, one_smul, ← pow_two] at h
    exact h
  have s₃ : u₃ • commitGen g_lo c₃ + u₃ ^ 2 • commitGen g_hi c₃ = u₃ • P + L + u₃ ^ 2 • R := by
    have h := congrArg (u₃ • ·) e₃
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₃, one_smul, ← pow_two] at h
    exact h
  -- Isolate the `g_hi` sub-commitments (the `u_i²` half).
  have hB₁ : u₁ ^ 2 • commitGen g_hi c₁
      = u₁ • P + L + u₁ ^ 2 • R - u₁ • commitGen g_lo c₁ := by rw [← s₁]; abel
  have hB₂ : u₂ ^ 2 • commitGen g_hi c₂
      = u₂ • P + L + u₂ ^ 2 • R - u₂ • commitGen g_lo c₂ := by rw [← s₂]; abel
  have hB₃ : u₃ ^ 2 • commitGen g_hi c₃
      = u₃ • P + L + u₃ ^ 2 • R - u₃ • commitGen g_lo c₃ := by rw [← s₃]; abel
  simp only [commitGen_add_left, commitGen_smul_left, hB₁, hB₂, hB₃]
  match_scalars <;>
    first
      | linear_combination hl1
      | linear_combination hl0
      | linear_combination hl2
      | ring

end Bulletproof

/-!
## IPA soundness: the transcript tree and 3-special soundness

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

namespace Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Halving the index set

Using `2 ^ k + 2 ^ k = 2 ^ (k + 1)` and the sum-equivalence
`Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1))`: `loHalf`/`hiHalf` restrict a
length-`2^{k+1}` vector to its first/last `2^k` indices, and `append`
concatenates two halves. -/

/-- Lower half: the restriction of a length-`2^{k+1}` vector to its first `2^k`
indices. -/
private def loHalf {α : Type*} {k : ℕ} (f : Fin (2 ^ (k + 1)) → α) : Fin (2 ^ k) → α :=
  fun i => f (Fin.castLE (by rw [pow_succ]; omega) i)

/-- Upper half: the restriction of a length-`2^{k+1}` vector to its last `2^k`
indices (offset by `2^k`). -/
private def hiHalf {α : Type*} {k : ℕ} (f : Fin (2 ^ (k + 1)) → α) : Fin (2 ^ k) → α :=
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
private def foldHalves {M : Type*} [AddCommGroup M] [Module F M] {k : ℕ}
    (v : Fin (2 ^ (k + 1)) → M) (u : F) : Fin (2 ^ k) → M :=
  loHalf v + u • hiHalf v

/-- The lower half of an `append` is the lower part. -/
private theorem loHalf_append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) :
    loHalf (append lo hi) = lo := by
  funext i
  simp only [loHalf, append, Fin.val_castLE, dif_pos i.isLt, Fin.eta]

/-- The upper half of an `append` is the upper part. -/
private theorem hiHalf_append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) :
    hiHalf (append lo hi) = hi := by
  funext i
  have h : ¬ (2 ^ k + i.val < 2 ^ k) := by omega
  simp only [hiHalf, append, dif_neg h]
  congr 1
  apply Fin.ext
  simp

/-- A length-`2^{k+1}` commitment splits over the two halves:
`⟨a, g⟩ = ⟨loHalf a, loHalf g⟩ + ⟨hiHalf a, hiHalf g⟩`. -/
private theorem commitGen_split {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (a : Fin (2 ^ (k + 1)) → F) :
    commitGen g a = commitGen (loHalf g) (loHalf a) + commitGen (hiHalf g) (hiHalf a) := by
  have e : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
  let φ : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) := finSumFinEquiv.trans (finCongr e)
  simp only [commitGen]
  rw [← φ.sum_comp (fun j => a j • g j), Fintype.sum_sum_type]
  congr 1

/-- A commitment of an `append` splits over the parent halves:
`⟨append a_lo a_hi, g⟩ = ⟨a_lo, loHalf g⟩ + ⟨a_hi, hiHalf g⟩`. -/
private theorem commitGen_append {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (a_lo a_hi : Fin (2 ^ k) → F) :
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
private theorem ipa_soundV : {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) →
    (P : G) → (v : F) → (t : IpaTreeV F G d) → IpaAcceptV g b P v t →
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

end Bulletproof

/-!
## Binding of the kimchi IPA commitment as discrete-log-relation hardness

Binding is the sole cryptographic assumption on the group, made auditable: a
binding violation is reduced to a nontrivial discrete-log relation among the
generators `σ.g` and the blinding base `σ.h`, and binding is shown to be *exactly*
DL-relation triviality.

The commitment is hiding (`commit σ a r = ⟨a, σ.g⟩ + r • σ.h`), so a witness is
the pair `(a, r)` and a discrete-log relation ranges over `[σ.g, σ.h]`: a pair
`(r, r_h)` with `⟨r, σ.g⟩ + r_h • σ.h = 0`.
-/

namespace Bulletproof

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

end Bulletproof

/-!
## The Fiat–Shamir bridge and single-opening soundness of the kimchi IPA

The trust boundary of the IPA soundness development, and the single-opening kernel the
chunked claims compose onto (`Chunk.lean`, `Soundness/ChunkedBatch.lean`). Everything
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

namespace Bulletproof

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

end Bulletproof
