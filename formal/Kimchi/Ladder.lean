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

/-
Every accumulator after the first step is odd (each step adds `ε ∈ {-1,1}`).
-/
lemma ladder_odd (L : ℕ) (k ε : ℕ → ℤ)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) :
    ∀ j, 1 ≤ j → j ≤ L → Odd (k j) := by
  intro j hj₁ hj₂;
  induction' j with j ih;
  · contradiction;
  · grind +splitImp

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

/-- The exact forbidden scalar residues for the Pasta VarBaseMul gate (verified by
    exhaustive computation, and identical for both Pasta scalar fields): the small
    scalars whose double-and-add drives the accumulator onto `±T` in the final
    doublings. For ANY prime `q ≡ 1 (mod 4)` in the one-wrap regime, the actual
    reachable degenerate set is a subset of these, so excluding them is sound; for the
    Pasta primes it is exactly this set. -/
def forbiddenResidues : List ℤ := [0, 1, -1, 2, -2, 3, -3, 5, 7, 9, 11]

/-
Depth-1 input (`L = j + 1`): every degeneracy branch lands on a forbidden residue.
-/
lemma degen_d1 (q L : ℕ)
    (k ε : ℕ → ℤ)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) (j : ℕ) (hj : j < L) (hL : L = j + 1)
    (hdeg : (q : ℤ) ∣ (k j - 1) ∨ (q : ℤ) ∣ (k j + 1) ∨ (q : ℤ) ∣ (2 * k j - 1)
              ∨ (q : ℤ) ∣ (2 * k j + 1)) :
    ∃ t ∈ forbiddenResidues, (q : ℤ) ∣ (k L - t) := by
  obtain h | h | h | h := hdeg;
  · rcases hε j hj with ( hε | hε ) <;> simp_all +decide;
    · exact ⟨ 3, by decide, by convert h.mul_left 2 using 1; ring ⟩;
    · exact ⟨ 1, by decide, by convert h.mul_left 2 using 1; ring ⟩;
  · rcases hε j hj with ( hε | hε ) <;> simp_all +decide;
    · exact ⟨ -1, by decide, by convert h.mul_left 2 using 1; ring ⟩;
    · exact ⟨ -3, by decide, by convert h.mul_left 2 using 1; ring ⟩;
  · rcases hε j hj with ( hε | hε ) <;> simp_all +decide;
    · exact ⟨ 2, by decide, by convert h using 1; ring ⟩;
    · exact ⟨ 0, by decide, by simpa using h ⟩;
  · cases hε j hj <;> simp_all +decide;
    · exact ⟨ 0, by decide, by simpa using h ⟩;
    · exact ⟨ -2, by decide, by convert h using 1; ring ⟩

/-
Depth-2 input (`L = j + 2`). Branches `q∣(k j-1)` and `q∣(2 k j-1)` land on forbidden
    residues; `q∣(k j+1)` is impossible by parity+size; `q∣(2 k j+1)` is impossible by
    `q ≡ 1 (mod 4)`.
-/
lemma degen_d2 (q L : ℕ) (hq4 : q % 4 = 1)
    (hreg₁ : 2 ^ (L - 1) < q) (hreg₂ : q < 2 ^ L)
    (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) (j : ℕ) (hj : j < L) (hL : L = j + 2)
    (hdeg : (q : ℤ) ∣ (k j - 1) ∨ (q : ℤ) ∣ (k j + 1) ∨ (q : ℤ) ∣ (2 * k j - 1)
              ∨ (q : ℤ) ∣ (2 * k j + 1)) :
    ∃ t ∈ forbiddenResidues, (q : ℤ) ∣ (k L - t) := by
  obtain h | h | h | h := hdeg;
  · rcases hε j hj with ha | ha <;>
      rcases hε ( j + 1 ) ( by linarith ) with hb | hb <;> simp_all +decide;
    · exact ⟨ 7, by decide, by convert h.mul_left 4 using 1; ring ⟩;
    · use 5;
      exact ⟨ by decide, by convert h.mul_left 4 using 1; ring ⟩;
    · exact ⟨ 3, by decide, by convert h.mul_left 4 using 1; ring ⟩;
    · exact ⟨ 1, by decide, by convert h.mul_left 4 using 1; ring ⟩;
  · -- From hb, `0 < k j + 1 ≤ 3*2^j` and `2*q > 4*2^j > 3*2^j`, so `0 < k j + 1 < 2*q`;
    -- `Int.le_of_dvd` forces `k j + 1 = q` (the only positive multiple below `2q`).
    have h_eq_q : k j + 1 = q := by
      have h_eq_q : 0 < k j + 1 ∧ k j + 1 < 2 * q := by
        have h_bound : 0 < k j + 1 ∧ k j + 1 ≤ 3 * 2 ^ j := by
          have := ladder_bounds L k ε hk0 hε hrec j ( by linarith )
          norm_num at * ; constructor <;> linarith;
        simp_all +decide [ pow_succ' ];
        linarith;
      obtain ⟨ a, ha ⟩ := h; nlinarith [ show a = 1 by nlinarith ] ;
    obtain ⟨ m, hm ⟩ := ladder_odd L k ε hε hrec j ( by
      grind ) ( by
      grind );
    omega;
  · -- `q ∣ 2 * k j - 1` propagates to `q ∣ k L - t` for some `t ∈ forbiddenResidues`.
    have h_div : (q : ℤ) ∣ k L - (2 * ε j + ε (j + 1) + 2) := by
      convert h.mul_left 2 using 1
      rw [ hL, hrec _ ( by linarith ), hrec _ ( by linarith ) ] ; ring;
    cases hε j hj <;> cases hε ( j + 1 ) ( by linarith ) <;>
      simp_all +decide only [forbiddenResidues];
    · exact ⟨ 5, by decide, h_div ⟩;
    · exact ⟨ 3, by decide, h_div ⟩;
    · exact ⟨ 1, by decide, h_div ⟩;
    · exact ⟨ _, by decide, h_div ⟩;
  · -- `2 k j + 1` is odd and `0 < 2 k j + 1 < 3q`; writing `2 k j + 1 = q * c`, the range
    -- gives `c ∈ {1,2}`, and `c = 2` is even, so `c = 1`, i.e. `2 k j + 1 = q`.
    obtain ⟨c, hc⟩ := h
    have hc_val : c = 1 := by
      have hc_val : c = 1 ∨ c = 2 := by
        have hc_val : 0 < c ∧ c < 3 := by
          have hc_bounds : 0 < 2 * k j + 1 ∧ 2 * k j + 1 < 3 * q := by
            have := ladder_bounds L k ε hk0 hε hrec j ( by linarith )
            simp_all +decide [ pow_succ' ]
            constructor <;> linarith [ pow_pos ( zero_lt_two' ℤ ) j ];
          have hq2 : 2 ≤ q := by
            have h1 := Nat.one_le_pow (L - 1) 2 (by norm_num)
            omega
          constructor <;> nlinarith only [ hc, hc_bounds, hq2 ];
        cases hc_val ; interval_cases c <;> trivial;
      grind +qlia;
    obtain ⟨ m, hm ⟩ := ladder_odd L k ε hε hrec j ( by
      grind +qlia ) ( by
      linarith );
    grind

/-
Depth-3 input (`L = j + 3`). Branch `q∣(2 k j-1)` lands on a forbidden residue;
    `q∣(k j±1)` are impossible by size; `q∣(2 k j+1)` is impossible by `q ≡ 1 (mod 4)`
    (or, when `j = 0`, forces `q = 5`, where forbiddenResidues covers every residue).
-/
lemma degen_d3 (q L : ℕ) (hq : Nat.Prime q) (hq4 : q % 4 = 1)
    (hreg₁ : 2 ^ (L - 1) < q) (hreg₂ : q < 2 ^ L)
    (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) (j : ℕ) (hj : j < L) (hL : L = j + 3)
    (hdeg : (q : ℤ) ∣ (k j - 1) ∨ (q : ℤ) ∣ (k j + 1) ∨ (q : ℤ) ∣ (2 * k j - 1)
              ∨ (q : ℤ) ∣ (2 * k j + 1)) :
    ∃ t ∈ forbiddenResidues, (q : ℤ) ∣ (k L - t) := by
  rcases j with ( _ | j ) <;> simp_all +decide;
  · interval_cases q <;> simp_all +decide;
    rcases hε 0 ( by decide ) with ha | ha <;>
      rcases hε 1 ( by decide ) with hb | hb <;>
      rcases hε 2 ( by decide ) with hc | hc <;> simp +decide only [ha, hb, hc];
  · rcases hdeg with ( h | h | h | h );
    · have h_bounds : 2 ^ (j + 1) + 1 ≤ k (j + 1) ∧ k (j + 1) ≤ 3 * 2 ^ (j + 1) - 1 := by
        apply ladder_bounds (j + 3) k ε hk0 (fun j hj => hε j (by linarith))
          (fun j hj => hrec j (by linarith)) (j + 1) (by linarith);
      nlinarith [ Int.le_of_dvd ( by linarith [ pow_pos ( zero_lt_two' ℤ ) ( j + 1 ) ] ) h,
        pow_succ' ( 2 : ℤ ) j, pow_succ' ( 2 : ℤ ) ( j + 1 ), pow_succ' ( 2 : ℤ ) ( j + 2 ),
        pow_succ' ( 2 : ℤ ) ( j + 3 ) ];
    · obtain ⟨ m, hm ⟩ := h;
      have h_bounds : 2 ^ (j + 1) + 1 ≤ k (j + 1) ∧ k (j + 1) ≤ 3 * 2 ^ (j + 1) - 1 := by
        apply ladder_bounds (j + 3) k ε hk0 (fun j hj => hε j (by linarith))
          (fun j hj => hrec j (by linarith)) (j + 1) (by linarith);
      rcases lt_trichotomy m 0 with hm' | rfl | hm' <;> norm_num [ pow_succ' ] at * <;> nlinarith;
    · obtain ⟨ m, hm ⟩ := h;
      rcases hε ( j + 1 ) ( by linarith ) with ha | ha <;>
        rcases hε ( j + 2 ) ( by linarith ) with hb | hb <;>
        rcases hε ( j + 3 ) ( by linarith ) with hc | hc <;> simp_all +decide [ pow_succ' ];
      all_goals rw [ sub_eq_iff_eq_add ] at hm; norm_num [ hm, ha, hb, hc ] ; ring_nf ;
      all_goals norm_num [ forbiddenResidues ];
      all_goals norm_num [ dvd_mul_of_dvd_left ] ;
    · obtain ⟨ m, hm ⟩ := h;
      rcases lt_trichotomy m 1 with hm' | rfl | hm';
      · have h_contra : k (j + 1) ≥ 2 ^ (j + 1) + 1 := by
          apply (ladder_bounds (j + 3) k ε hk0 (fun j hj => hε j (by linarith))
            (fun j hj => hrec j (by linarith)) (j + 1) (by linarith)).left;
        nlinarith [ pow_pos ( zero_lt_two' ℤ ) ( j + 1 ), pow_succ' ( 2 : ℤ ) ( j + 1 ),
          pow_succ' ( 2 : ℤ ) ( j + 2 ), pow_succ' ( 2 : ℤ ) ( j + 3 ) ];
      · obtain ⟨ m, hm ⟩ :=
          ladder_odd ( j + 4 ) k ε hε hrec ( j + 1 ) ( by linarith ) ( by linarith )
        simp_all +decide [ parity_simps ];
        omega;
      · have := ladder_bounds ( j + 4 ) k ε hk0 ( fun i hi => hε i ( by linarith ) )
          ( fun i hi => hrec i ( by linarith ) ) ( j + 1 ) ( by linarith )
        norm_num [ pow_succ' ] at *
        nlinarith [ Int.mul_ediv_add_emod ( 2 * k ( j + 1 ) + 1 ) q,
          Int.emod_nonneg ( 2 * k ( j + 1 ) + 1 ) ( Nat.cast_ne_zero.mpr hq.ne_zero ),
          Int.emod_lt_of_pos ( 2 * k ( j + 1 ) + 1 ) ( Nat.cast_pos.mpr hq.pos ) ] ;

/-- **Core of the tight bound.** A degenerate input `k j` (`j < L`) propagates forward to
    a final value `k L ≡ t (mod q)` for some `t ∈ forbiddenResidues`. Inputs at depth
    `d = L - j ≥ 4` cannot be degenerate (`ladder_size`); for `d ≤ 3` the four degeneracy
    branches either land on an explicit forbidden residue, or are ruled out by a size /
    parity / `q ≡ 1 (mod 4)` argument. -/
lemma degenerate_input_forces_forbidden (q L : ℕ) (hq : Nat.Prime q) (hq4 : q % 4 = 1)
    (hreg₁ : 2 ^ (L - 1) < q) (hreg₂ : q < 2 ^ L)
    (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) (j : ℕ) (hj : j < L)
    (hdeg : (q : ℤ) ∣ (k j - 1) ∨ (q : ℤ) ∣ (k j + 1) ∨ (q : ℤ) ∣ (2 * k j - 1)
              ∨ (q : ℤ) ∣ (2 * k j + 1)) :
    ∃ t ∈ forbiddenResidues, (q : ℤ) ∣ (k L - t) := by
  by_cases hsize : j + 4 ≤ L
  · exfalso
    obtain ⟨h1, h2, h3, h4⟩ := ladder_size q L k ε hk0 hreg₁ hε hrec j hsize
    rcases hdeg with h | h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h4 h
  · have hcase : L = j + 1 ∨ L = j + 2 ∨ L = j + 3 := by omega
    rcases hcase with hL | hL | hL
    · exact degen_d1 q L k ε hε hrec j hj hL hdeg
    · exact degen_d2 q L hq4 hreg₁ hreg₂ k ε hk0 hε hrec j hj hL hdeg
    · exact degen_d3 q L hq hq4 hreg₁ hreg₂ k ε hk0 hε hrec j hj hL hdeg

/-- **Tight (exact-set) form.** Same ladder as `ladder_nondegen`, but for a prime
    `q ≡ 1 (mod 4)` the forbidden set shrinks from the `[-15,15]` band to the explicit
    11 residues `forbiddenResidues = {0, ±1, ±2, ±3, 5, 7, 9, 11}`. The `q ≡ 1 (mod 4)`
    hypothesis closes the `2·k ≡ -1` degeneracy branch (`(q-1)/2` is even, so it is not a
    reachable odd accumulator at the deep inputs), which is what would otherwise add the
    residues `-5, -7, -9, -11`. If `s = k L` avoids these 11 residues, every input
    `k j` (`j < L`) is non-degenerate. -/
theorem ladder_nondegen_tight (q L : ℕ) (hq : Nat.Prime q) (hq4 : q % 4 = 1)
    (hreg₁ : 2 ^ (L - 1) < q) (hreg₂ : q < 2 ^ L)
    (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j)
    (hnf : ∀ t ∈ forbiddenResidues, ¬ (q : ℤ) ∣ (k L - t)) :
    ∀ j, j < L → ¬ (q : ℤ) ∣ (k j - 1) ∧ ¬ (q : ℤ) ∣ (k j + 1)
                ∧ ¬ (q : ℤ) ∣ (2 * k j - 1) ∧ ¬ (q : ℤ) ∣ (2 * k j + 1) := by
  intro j hj
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hdvd <;>
    obtain ⟨t, ht, htd⟩ :=
      degenerate_input_forces_forbidden q L hq hq4 hreg₁ hreg₂ k ε hk0 hε hrec j hj
        (by tauto) <;>
    exact hnf t ht htd

end Kimchi.Ladder
