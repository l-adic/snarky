import Mathlib

/-! # Number-theoretic kernel of the VarBaseMul gate soundness (pure math).

The deployed circuit's scalar register is a valid base-field element, so the double-and-add
ladder top is bounded: `k L < 2·baseFieldOrder + 2^L`. Combined with the 2-cycle size relation
`baseFieldOrder + 2^(L-1) < 2·order`, that bound keeps every partial accumulator strictly below
`2·order ± 1` — the smallest values congruent to `±1 (mod order)`. So no accumulator is `≡ ±1`,
i.e. no accumulator equals `±T`, with no exclusion set in sight. `ladder_x_nondegen` is that
argument; `ladder_bounds` / `ladder_step` / `ladder_odd` are its envelope/parity lemmas. -/

namespace Kimchi.Circuit.VarBaseMul.Ladder

/-- Lower/upper envelope of the ladder: `2^j + 1 ≤ k j ≤ 3·2^j - 1` for `j ≤ L`. -/
lemma ladder_bounds (L : ℕ) (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) :
    ∀ j, j ≤ L → 2 ^ j + 1 ≤ k j ∧ k j ≤ 3 * 2 ^ j - 1 := by
  intro j hj
  induction' j with j ih <;> norm_num [hk0, pow_succ']
  by_cases h : j < L <;> simp_all +decide
  grind

/-- Forward-propagation bound: after `d` doubling steps the value differs from `2^d · k j`
    by at most `2^d - 1` (because each step adds `ε ∈ {-1, 1}`). -/
lemma ladder_step (L : ℕ) (k ε : ℕ → ℤ)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) :
    ∀ d j, j + d ≤ L → |k (j + d) - 2 ^ d * k j| ≤ 2 ^ d - 1 := by
  intro d j hjL
  induction d <;> simp_all +decide [pow_succ']
  grind +qlia

/-- Every accumulator after the first step is odd (each step adds `ε ∈ {-1,1}`). -/
lemma ladder_odd (L : ℕ) (k ε : ℕ → ℤ)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) :
    ∀ j, 1 ≤ j → j ≤ L → Odd (k j) := by
  intro j hj₁ hj₂;
  induction' j with j ih;
  · contradiction;
  · grind +splitImp

/--
**x-condition non-degeneracy from the register/magnitude bound** (pure number theory,
    orthogonal to the t-condition `tne_of_holds`). The deployed circuit's register is a
    valid field element `< baseFieldOrder`, so the ladder top is bounded:
    `k L < 2·baseFieldOrder + 2^L`. The only x-condition accumulator values are
    `k ≡ ±1 (mod order)`, whose smallest ODD representatives are `2·order ± 1` (the even
    reps `order ± 1` are unreachable since every `k j` with `1 ≤ j` is odd, `ladder_odd`).
    The regime `baseFieldOrder + 2^(L-1) < 2·order` (the Pasta `2δ > δ'` fact) puts those
    above the bounded range, so no INPUT `k j` (`j < L`) is `≡ ±1 (mod order)` — i.e. no
    accumulator equals `±T`. (No constraints, no curve, no forbidden set.)

    ## Why each side condition is needed

    Brute-force search over small parameters pins down three hypotheses, each necessary
    (a concrete degenerate input exists without it):

    * `hodd : Odd order` — when `order` is even the even representatives `order ± 1` of
      `±1 (mod order)` are reachable. With `ladder_odd` (every `k j`, `1 ≤ j`, is odd)
      it rules out the even reps and forces the odd reps `2·order ± 1`. The real `order`
      is prime, hence odd.
    * `hbound : baseFieldOrder + 2^(L-1) + 2 ≤ 2·order` — for `j = L - 1` the `+1` branch
      (`k (L-1) = 2·order - 1`) gives `k L = 4·order - 2 + ε ≥ 4·order - 3`, which the
      slacker bound `baseFieldOrder + 2^(L-1) < 2·order` (`k L < 4·order - 2`) fails to
      exclude (e.g. `order = 5, baseFieldOrder = 5, L = 3`); tightening the slack by `2`
      (`k L < 4·order - 4`) closes it.
    * `horder : 3 < order` — for `order = 3, L = 2` the input `k 0 = 2` satisfies
      `order ∣ (k 0 + 1) = 3`.

    All three hold comfortably for the real Pasta parameters (`L = 255`,
    `order ≈ 2^254 + 4.56·10^37` a large prime, `2δ > δ'`).
-/
theorem ladder_x_nondegen (order baseFieldOrder L : ℕ)
    (hreg₁ : 2 ^ (L - 1) < order)
    (hodd : Odd order) (horder : 3 < order)
    (hbound : baseFieldOrder + 2 ^ (L - 1) + 2 ≤ 2 * order)
    (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j)
    (hkL : k L < 2 * (baseFieldOrder : ℤ) + 2 ^ L) :
    ∀ j, j < L → ¬ (order : ℤ) ∣ (k j - 1) ∧ ¬ (order : ℤ) ∣ (k j + 1) := by
  -- From `ladder_bounds`, `2^j + 1 ≤ k j` and `k j ≤ 3 * 2^j - 1` for all `j < L`.
  intros j hj
  have h_bounds : 2 ^ j + 1 ≤ k j ∧ k j ≤ 3 * 2 ^ j - 1 :=
    ladder_bounds L k ε hk0 hε hrec j (by linarith)
  constructor <;> intro h <;> obtain ⟨t, ht⟩ := h
  · rcases lt_trichotomy t 1 with ht' | rfl | ht' <;>
      try nlinarith [pow_pos (zero_lt_two' ℤ) j]
    · obtain ⟨m, hm⟩ := hodd
      simp_all +decide [parity_simps]
      rcases j with (_ | j) <;> simp_all +decide [pow_succ']
      grind
    · -- Propagate forward: `k L ≥ 2^(L-j) * k j - (2^(L-j) - 1)`.
      have h_step : k L ≥ 2 ^ (L - j) * k j - (2 ^ (L - j) - 1) := by
        have h_step : |k L - 2 ^ (L - j) * k j| ≤ 2 ^ (L - j) - 1 := by
          convert ladder_step L k ε hε hrec (L - j) j (by omega) using 1
          simp +decide [Nat.add_sub_of_le hj.le]
        linarith [abs_le.mp h_step]
      rcases L with (_ | L) <;> simp_all +decide [pow_succ']
      nlinarith [pow_pos (zero_lt_two' ℤ) (L + 1 - j),
        pow_le_pow_right₀ (by decide : 1 ≤ 2)
          (show L + 1 - j ≥ 1 from Nat.sub_pos_of_lt (by linarith))]
  · rcases t with ⟨_ | _ | _ | t⟩ <;> norm_num at ht
    · linarith [pow_pos (zero_lt_two' ℤ) j]
    · obtain ⟨m, hm⟩ := hodd
      simp_all +decide [parity_simps]
      exact absurd
        (ladder_odd L k ε hε hrec j (Nat.pos_of_ne_zero (by rintro rfl; linarith))
          (by linarith))
        (by norm_num [ht, parity_simps])
    · -- Propagate forward: `k L ≥ 2^(L-j) * k j - (2^(L-j) - 1)`.
      have h_step : k L ≥ 2 ^ (L - j) * k j - (2 ^ (L - j) - 1) := by
        have := ladder_step L k ε hε hrec (L - j) j (by omega)
        simp_all +decide [Nat.add_sub_of_le hj.le]
        linarith [abs_lt.mp this]
      rcases L with (_ | L) <;> simp_all +decide [pow_succ']
      nlinarith [pow_pos (zero_lt_two' ℤ) j,
        pow_le_pow_right₀ (by decide : 1 ≤ 2) hj,
        pow_pos (zero_lt_two' ℤ) (L + 1 - j),
        pow_le_pow_right₀ (by decide : 1 ≤ 2)
          (show L + 1 - j ≥ 1 from Nat.sub_pos_of_lt (by linarith))]
    · nlinarith [pow_pos (zero_lt_two' ℤ) j,
        pow_le_pow_right₀ (show 1 ≤ 2 by decide)
          (show j ≤ L - 1 from Nat.le_sub_one_of_lt hj)]
    · grind

end Kimchi.Circuit.VarBaseMul.Ladder
