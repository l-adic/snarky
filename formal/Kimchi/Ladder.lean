import Mathlib

/-! # Number-theoretic kernel of the VarBaseMul gate soundness (pure math).

## Correction to the originally stated forbidden set

The task shipped with the forbidden condition phrased as `q ∣ (k L + 2^L - 1)` or
`q ∣ (k L + 2^L + 1)` (i.e. `k L + 2^L ≡ ±1 (mod q)`).  That condition is **false** as a
characterisation of degeneracy: a brute-force search over the entire one-wrap regime (every
prime `q` with `2^(L-1) < q < 2^L`, for `L = 5,…,13`) produces sign patterns whose final value
`s = k L` is *not* of that form yet has a degenerate input.  Concretely, for `L = 5`, `q = 29`
the pattern giving `k 3 = 15` has `2·k 3 = 30 ≡ 1 (mod 29)`, yet `s + 2^L = 95 ≢ ±1 (mod 29)`.

The *correct* forbidden set is a small band around the multiples of `q`, on `k L` itself (not on
`k L + 2^L`).  Propagating a degenerate input `k j` forward through `d = L - j` doubling steps
gives `k L = 2^d · k j + T` with `|T| ≤ 2^d - 1`; a size argument confines degeneracy to the top
three inputs (`d ≤ 3`), so the reachable degenerate finals satisfy `k L ≡ t (mod q)` for some
integer `|t| ≤ 15`.  We therefore replace the (incorrect) two-residue hypothesis by

  `hnf : ∀ t : ℤ, -15 ≤ t → t ≤ 15 → ¬ (q : ℤ) ∣ (k L - t)`.

This is a genuine *strengthening* of "`s` is not forbidden": it rules out the full band that can
actually be reached.  It is satisfiable for the real parameters (`L = 255`, `q ≈ 2^254`): the band
has `31 ≪ q` residues, so the overwhelming majority of `k L` avoid it.  A brute-force check
confirms that under this hypothesis there are **no** degenerate inputs for any prime `q` in the
regime and `L = 2,…,13`.  The conclusion is left exactly as originally requested.

The upper regime bound `hreg₂ : q < 2 ^ L` and the primality `hq` are kept because the user asked
for the one-wrap regime, but they turn out not to be needed for the proof (only the lower regime
bound `hreg₁ : 2^(L-1) < q` is used). -/

namespace Kimchi.Ladder

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

/-- Non-degeneracy of the "deep" inputs (`d = L - j ≥ 4`) by a pure size argument:
    `k j` and `2·k j` are then strictly between `1` and `q - 1`. -/
lemma ladder_size (q L : ℕ) (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hreg₁ : 2 ^ (L - 1) < q)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) :
    ∀ j, j + 4 ≤ L → ¬ (q : ℤ) ∣ (k j - 1) ∧ ¬ (q : ℤ) ∣ (k j + 1)
                ∧ ¬ (q : ℤ) ∣ (2 * k j - 1) ∧ ¬ (q : ℤ) ∣ (2 * k j + 1) := by
  intro j hj
  have h_bounds : 2 ^ j + 1 ≤ k j ∧ k j ≤ 3 * 2 ^ j - 1 :=
    ladder_bounds L k ε hk0 hε hrec j (by linarith)
  -- From `hreg₁`, we have `8 * 2^(L - 4) < q`.
  have h_q_bound : 8 * 2 ^ (L - 4) < q := by
    rcases L with (_ | _ | _ | _ | L) <;> simp_all +decide [pow_succ']
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
    have := Int.le_of_dvd (by linarith [pow_pos (zero_lt_two' ℤ) j]) h <;>
    nlinarith [pow_pos (zero_lt_two' ℤ) j,
      pow_le_pow_right₀ (by decide : 1 ≤ 2) (show j ≤ L - 4 by omega)]

/-- Non-degeneracy of the top inputs (`1 ≤ d = L - j ≤ 3`): a degenerate input propagates
    forward to a final value `k L ≡ t (mod q)` with `|t| ≤ 15`, contradicting `hnf`. -/
lemma ladder_top (q L : ℕ) (k ε : ℕ → ℤ)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j)
    (hnf : ∀ t : ℤ, -15 ≤ t → t ≤ 15 → ¬ (q : ℤ) ∣ (k L - t)) :
    ∀ j, j < L → L ≤ j + 3 → ¬ (q : ℤ) ∣ (k j - 1) ∧ ¬ (q : ℤ) ∣ (k j + 1)
                ∧ ¬ (q : ℤ) ∣ (2 * k j - 1) ∧ ¬ (q : ℤ) ∣ (2 * k j + 1) := by
  intro j hj_lt_L hj_le_L_plus_3
  -- Let `D := L - j`; since `j < L` and `L ≤ j + 3`, we have `1 ≤ D ≤ 3`.
  set D := L - j with hD
  have hD_bounds : 1 ≤ D ∧ D ≤ 3 := by omega
  -- By `ladder_step`, `|k L - 2^D * k j| ≤ 2^D - 1`.
  have h_step : |k L - 2 ^ D * k j| ≤ 2 ^ D - 1 := by
    have := ladder_step L k ε hε hrec D j (by omega)
    simpa [hD, Nat.add_sub_cancel' (le_of_lt hj_lt_L)] using this
  have hp2 : (2 : ℤ) ^ D ≤ 8 :=
    pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) hD_bounds.2 |>.trans_eq (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hdvd
  · -- `t = k L - 2^D * (k j - 1)`.
    set t := k L - 2 ^ D * (k j - 1) with ht
    have ht_bounds : -15 ≤ t ∧ t ≤ 15 := by
      constructor <;> nlinarith [abs_le.mp h_step, hp2]
    exact hnf t ht_bounds.1 ht_bounds.2
      (by convert dvd_mul_of_dvd_right hdvd (2 ^ D) using 1; ring)
  · -- `t = k L - 2^D * (k j + 1)`.
    set t := k L - 2 ^ D * (k j + 1) with ht
    have ht_bounds : -15 ≤ t ∧ t ≤ 15 := by
      constructor <;> nlinarith [abs_le.mp h_step, hp2]
    exact hnf t ht_bounds.1 ht_bounds.2
      (by convert dvd_mul_of_dvd_right hdvd (2 ^ D) using 1; ring)
  · -- `t = k L - 2^(D-1) * (2 * k j - 1)`.
    set t := k L - 2 ^ (D - 1) * (2 * k j - 1) with ht
    have ht_bounds : -15 ≤ t ∧ t ≤ 15 := by
      rcases hD_bounds with ⟨_, _⟩
      interval_cases D <;> norm_num at * <;> constructor <;> linarith [abs_le.mp h_step]
    exact hnf t ht_bounds.1 ht_bounds.2
      (by convert hdvd.mul_left (2 ^ (D - 1)) using 1; ring)
  · -- `t = k L - 2^(D-1) * (2 * k j + 1)`.
    set t := k L - 2 ^ (D - 1) * (2 * k j + 1) with ht
    have ht_bounds : -15 ≤ t ∧ t ≤ 15 := by
      rcases hD_bounds with ⟨_, _⟩
      interval_cases D <;> norm_num at * <;> constructor <;> linarith [abs_le.mp h_step]
    exact hnf t ht_bounds.1 ht_bounds.2
      (by convert hdvd.mul_left (2 ^ (D - 1)) using 1; ring)

/-- A double-and-add ladder `k 0 = 2`, `k (j+1) = 2·k j + ε j` with `ε j ∈ {-1, 1}`,
    of length `L`, over a prime modulus `q` in the one-wrap regime `2^(L-1) < q < 2^L`.
    If the final value `s = k L` avoids the forbidden band `k L ≡ t (mod q)` for all
    `|t| ≤ 15`, then every INPUT `k j` (`j < L`) is non-degenerate:
    `k j ≢ ±1` and `2·k j ≢ ±1 (mod q)`.  (See the file header for why the originally
    stated forbidden set had to be corrected.) -/
theorem ladder_nondegen (q L : ℕ) (_hq : Nat.Prime q)
    (hreg₁ : 2 ^ (L - 1) < q) (_hreg₂ : q < 2 ^ L)
    (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j)
    (hnf : ∀ t : ℤ, -15 ≤ t → t ≤ 15 → ¬ (q : ℤ) ∣ (k L - t)) :
    ∀ j, j < L → ¬ (q : ℤ) ∣ (k j - 1) ∧ ¬ (q : ℤ) ∣ (k j + 1)
                ∧ ¬ (q : ℤ) ∣ (2 * k j - 1) ∧ ¬ (q : ℤ) ∣ (2 * k j + 1) := by
  intro j hj
  by_cases hd : j + 4 ≤ L
  · exact ladder_size q L k ε hk0 hreg₁ hε hrec j hd
  · exact ladder_top q L k ε hε hrec hnf j hj (by omega)

end Kimchi.Ladder
