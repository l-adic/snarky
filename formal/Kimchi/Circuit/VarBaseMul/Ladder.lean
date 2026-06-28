import Mathlib

/-! # Number-theoretic kernel of the VarBaseMul gate soundness (pure math).

## The forbidden set is a band, not a two-residue condition

The degenerate finals are **not** characterised by `k L + 2^L ≡ ±1 (mod q)`: for `L = 5`, `q = 29`
the sign pattern giving `k 3 = 15` has a degenerate input (`2·k 3 = 30 ≡ 1 (mod 29)`) yet
`s + 2^L = 95 ≢ ±1 (mod 29)`.

The forbidden set is instead a small band around the multiples of `q`, on `k L` itself (not on
`k L + 2^L`).  Propagating a degenerate input `k j` forward through `d = L - j` doubling steps
gives `k L = 2^d · k j + T` with `|T| ≤ 2^d - 1`; a size argument confines degeneracy to the top
three inputs (`d ≤ 3`), so every reachable degenerate final satisfies `k L ≡ t (mod q)` for some
integer `|t| ≤ 15`.  The non-forbidden hypothesis is therefore

  `hnf : ∀ t : ℤ, -15 ≤ t → t ≤ 15 → ¬ (q : ℤ) ∣ (k L - t)`,

which rules out the full reachable band, and is satisfiable for the real parameters
(`L = 255`, `q ≈ 2^254`): the band has `31 ≪ q` residues, so the overwhelming majority of `k L`
avoid it.

Only the lower regime bound `hreg₁ : 2^(L-1) < q` is used in the proof; the upper bound
`hreg₂ : q < 2 ^ L` and primality `hq` are carried to state the one-wrap regime. -/

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

/-- Every accumulator after the first step is odd (each step adds `ε ∈ {-1,1}`). -/
lemma ladder_odd (L : ℕ) (k ε : ℕ → ℤ)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) :
    ∀ j, 1 ≤ j → j ≤ L → Odd (k j) := by
  intro j hj₁ hj₂;
  induction' j with j ih;
  · contradiction;
  · grind +splitImp

/-- The exact forbidden scalar residues for the Pasta VarBaseMul gate (verified by
    exhaustive computation, and identical for both Pasta scalar fields): the small
    scalars whose double-and-add drives the accumulator onto `±T` in the final
    doublings. For ANY prime `q ≡ 1 (mod 4)` in the one-wrap regime, the actual
    reachable degenerate set is a subset of these, so excluding them is sound; for the
    Pasta primes it is exactly this set. -/
def forbiddenResidues : List ℤ := [0, 1, -1, 2, -2, 3, -3, 5, 7, 9, 11]

/-- Depth-1 input (`L = j + 1`): every degeneracy branch lands on a forbidden residue. -/
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

/-- Depth-2 input (`L = j + 2`). Branches `q∣(k j-1)` and `q∣(2 k j-1)` land on forbidden
    residues; `q∣(k j+1)` is impossible by parity+size; `q∣(2 k j+1)` is impossible by
    `q ≡ 1 (mod 4)`. -/
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

/-- Depth-3 input (`L = j + 3`). Branch `q∣(2 k j-1)` lands on a forbidden residue;
    `q∣(k j±1)` are impossible by size; `q∣(2 k j+1)` is impossible by `q ≡ 1 (mod 4)`
    (or, when `j = 0`, forces `q = 5`, where forbiddenResidues covers every residue). -/
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

/-- **Tight (exact-set) form.** The same double-and-add ladder, but for a prime
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

/-- **Sub-wrap non-degeneracy.** When the whole ladder fits below the modulus (`3·2^L ≤ q`), every
    input is non-degenerate *unconditionally* — no primality, no `q ≡ 1 (mod 4)`, no forbidden set.
    The envelope `2^j + 1 ≤ k j ≤ 3·2^j - 1` (`ladder_bounds`) places each of `k j ± 1` and
    `2·k j ± 1` strictly inside `(0, q)`, so none can be a multiple of `q`. This is the small-`L`
    regime (`5m ≤ bitlength(order) - 1`), where the scalar is too small to ever drive an
    accumulator onto `±T`, so the gate is safe with no guard at all. -/
lemma ladder_subwrap_nondegen (q L : ℕ) (hsub : 3 * 2 ^ L ≤ q)
    (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) :
    ∀ j, j < L → ¬ (q : ℤ) ∣ (k j - 1) ∧ ¬ (q : ℤ) ∣ (k j + 1)
                ∧ ¬ (q : ℤ) ∣ (2 * k j - 1) ∧ ¬ (q : ℤ) ∣ (2 * k j + 1) := by
  intro j hj
  obtain ⟨hlo, hhi⟩ := ladder_bounds L k ε hk0 hε hrec j hj.le
  have hjpos : (0 : ℤ) < 2 ^ j := by positivity
  have hps : (2 : ℤ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  have hpow : (2 : ℤ) ^ (j + 1) ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (by omega)
  have hqz : (3 : ℤ) * 2 ^ L ≤ (q : ℤ) := by exact_mod_cast hsub
  -- `6·2^j = 3·2^(j+1) ≤ 3·2^L ≤ q`, so every value below is `< q`.
  have h6 : 6 * 2 ^ j ≤ (q : ℤ) := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hdvd <;>
    have hle := Int.le_of_dvd (by nlinarith [hlo, hjpos]) hdvd <;>
    nlinarith [hhi, h6, hle, hjpos, hlo]

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

    Each of the three hypotheses is necessary — without it a concrete degenerate input exists:

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
