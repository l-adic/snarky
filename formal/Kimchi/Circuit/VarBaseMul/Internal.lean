import Kimchi.Curve
import Kimchi.Gate.VarBaseMul
import Kimchi.Shifted
import Mathlib

/-!
# The `VarBaseMul` circuit: supporting development

Variable-base scalar multiplication composes `Kimchi.Gate.VarBaseMul` gate rows: `m` gates run
back to back, each consuming five bits of the scalar, with gate `i`'s output accumulator feeding
gate `i + 1`'s input and its scalar register threading alongside. Each gate's `sound` supplies the
per-step relation `P_{i+1} = 32·P_i + cᵢ·T`, and folding that recurrence over the `m` rows is pure
group algebra. This module gathers the definitions and lemmas on which the deployed correctness
theorems rest — the curve-specialized `varBaseMul_scaleFast1` and `varBaseMul_scaleFast2` (in
`Kimchi.Circuit.VarBaseMul`) and the two generic roots `varBaseMul_subwrap_correct` and
`varBaseMul_forbidden_correct` it exposes here.

## Correspondence to the PureScript circuit

The hypotheses are exactly the constraints `Snarky.Circuit.Kimchi.VarBaseMul` emits
(`packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/VarBaseMul.purs`):

* `P 0 = 2·T` ← `addFast CheckFinite base base` (acc := `[2]·base`);
* `N 0 = 0` ← `nAccPrev: const_ zero`; per-bit `n' = 2·n + b` ← `foldl (\a b -> double a + b)`;
* `q_j = (xT, (2·b − 1)·yT)` ← `Q = (xBase, (2·b − 1)·yBase)` (`computeVbmChain`);
* `N m` holds the caller's shifted register ← `assertEqual_ nAcc t`.

The two circuit entry points appear here as `scalarMul_shifted` (the core `varBaseMul`, computing
`[2·t + 2^n + 1]·g`) and `scalarMul_type2` (`scaleFast2`, the parity split). This is an audit-level
correspondence: the model's hypotheses match the PureScript constraints by inspection, not by a
mechanized extraction.

## Contents

* the point- and register-level recurrence folds (`chain_scalarMul`, `chain_register`,
  `chain_sum_bound`) and the folded scalar-multiplication theorems (`scalarMul`,
  `scalarMul_baseMul`, `scalarMul_shifted`, `scalarMul_type2`);
* the per-row hypothesis bundles `NonDegen` (the non-vertical side conditions) and `GateStep`;
* the number-theoretic ladder kernel (`Kimchi.Circuit.VarBaseMul.Ladder`): the double-and-add
  ladder's bounds, the forbidden-band / forbidden-residue characterization of degenerate finals,
  and the unconditional sub-wrap non-degeneracy;
* the group-order non-degeneracy toolkit (`smul_ne_zero_of_lt`, `x_ne_xT_of_ne_base`,
  `tne_of_holds`): the partial accumulators stay away from `±T`;
* the soundness folds (`gate_chain_produce`, `gateStep_chain`) and the two regime roots
  `varBaseMul_forbidden_correct` / `varBaseMul_subwrap_correct`.

The `scalarMul_shifted` headline closes the loop with proof-systems: at the real init `P 0 = 2·T`,
`N 0 = 0`, the scalar `(n : F) = 2·(N m) + 2^(5m) + 1` is verbatim `Shifted_value.Type1.to_field`
and reproduces the reference value `[1 + 2^numBits + 2·n_bits]·BasePoint` from `varbasemul.rs`'s own
test, so the circuit computes `[s]·T` for the caller's scalar `s` once it is fed the shifted scalar.

## The number-theoretic ladder kernel

The non-degeneracy of every partial accumulator reduces to a pure statement about the integer
double-and-add ladder `k 0 = 2`, `k (j + 1) = 2·k j + εⱼ` with signs `εⱼ ∈ {-1, 1}`. The degenerate
finals are not characterized by `k L + 2^L ≡ ±1 (mod q)`; they form a small band around the
multiples of `q`, on `k L` itself. A degenerate input `k j` propagates forward through `d = L − j`
doublings to `k L = 2^d·k j + T` with `|T| ≤ 2^d − 1`; a size argument confines degeneracy to the
top three inputs (`d ≤ 3`), so every reachable degenerate final satisfies `k L ≡ t (mod q)` for some
`|t| ≤ 15`. For a prime `q ≡ 1 (mod 4)` the band shrinks to the eleven explicit residues
`forbiddenResidues = {0, ±1, ±2, ±3, 5, 7, 9, 11}` (`ladder_nondegen_tight`). When the whole ladder
fits below the modulus (`3·2^L ≤ q`) no input is degenerate at all (`ladder_subwrap_nondegen`). The
lower regime bound `2^(L-1) < q` situates the one-wrap regime; for the real parameters `L = 255`,
`q ≈ 2^254`, the band's 31 residues are a vanishing fraction of `q`.
-/

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

namespace Kimchi.Circuit.VarBaseMul

open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine Kimchi.Shifted

variable {F : Type*} [Field F] [DecidableEq F]

/-- Chaining the per-gate relation `P_{i+1} = 32·P_i + cᵢ·T` over `m` gates gives
    the closed-form scalar multiple

        P_m = 32^m·P₀ + (∑_{i<m} 32^(m-1-i)·cᵢ)·T

    — i.e. `m` chained `VarBaseMul` gates compute variable-base scalar
    multiplication by the `5m`-bit scalar `k = ∑_{i<m} 32^(m-1-i)·cᵢ` (plus the
    carried `32^m·P₀`). The per-gate relation is supplied by `sound`
    after folding its `Qⱼ` points into `±T` via booleanity. -/
theorem chain_scalarMul
    (W : WeierstrassCurve.Affine F)
    (m : ℕ) (P : ℕ → W.Point) (T : W.Point) (c : ℕ → ℤ)
    (hstep : ∀ i, i < m → P (i + 1) = (32 : ℤ) • P i + c i • T) :
    P m = (32 : ℤ) ^ m • P 0
        + (∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i) • T := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : P (m + 1) = (32 : ℤ) • P m + c m • T := hstep m (Nat.lt_succ_self m)
    have ih' := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hsum : (∑ i ∈ Finset.range (m + 1), (32 : ℤ) ^ (m + 1 - 1 - i) * c i)
        = (32 : ℤ) * (∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i) + c m := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : m - i = (m - 1 - i) + 1 := by
        have := Finset.mem_range.mp hi; omega
      rw [hi', pow_succ]
      ring
    rw [hs, ih', hsum, smul_add, smul_smul, smul_smul, add_smul, pow_succ']
    abel

omit [DecidableEq F] in
/-- The scalar-register companion to `chain_scalarMul`: if each step's integer
    contribution `c i` matches the register transition `N i → N (i+1)` by
    `(c i : F) = 2·N (i+1) − 64·N i − 31`, then the folded scalar
    `k = ∑ 32^(m-1-i)·c i` satisfies `(k : F) = 2·N m − 2·32^m·N 0 − (32^m − 1)`.
    (The `−31`s sum to `−(32^m−1)`; the register terms telescope.) -/
theorem chain_register (m : ℕ) (N : ℕ → F) (c : ℕ → ℤ)
    (hstep : ∀ i, i < m → (c i : F) = 2 * N (i + 1) - 64 * N i - 31) :
    ((∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i : ℤ) : F)
      = 2 * N m - 2 * (32 : F) ^ m * N 0 - ((32 : F) ^ m - 1) := by
  induction' m with m ih <;> simp_all +decide [pow_succ', Finset.sum_range_succ]
  convert congr_arg (fun x : F => 32 * x + (2 * N (m + 1) - 64 * N m - 31))
    (ih fun i hi => hstep i hi.le) using 1
  · rw [Finset.mul_sum _ _ _]
    refine congr_arg₂ _ (Finset.sum_congr rfl fun i hi => ?_) rfl
    rw [← mul_assoc, ← pow_succ', tsub_right_comm,
      Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hi)))]
  · ring

/-- Magnitude bound on the folded signed-digit multiplier. If each per-gate digit
    `c i` has `|c i| ≤ 31`, then the accumulated scalar
    `k = ∑_{i<m} 32^(m-1-i)·c i` satisfies `|k| ≤ 32^m − 1`. (Induction: the
    recurrence `k_{m+1} = 32·k_m + c m` and `32·(32^m−1) + 31 = 32^(m+1)−1`.) -/
theorem chain_sum_bound (m : ℕ) (c : ℕ → ℤ) (hc : ∀ i, i < m → (c i).natAbs ≤ 31) :
    (∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i).natAbs ≤ 32 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsum : (∑ i ∈ Finset.range (m + 1), (32 : ℤ) ^ (m + 1 - 1 - i) * c i)
        = (32 : ℤ) * (∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i) + c m := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : m - i = (m - 1 - i) + 1 := by
        have := Finset.mem_range.mp hi; omega
      rw [hi', pow_succ]
      ring
    rw [hsum]
    have ihb := ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))
    have hcm := hc m (Nat.lt_succ_self m)
    set S := ∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i with hS
    have key : (32 * S + c m).natAbs ≤ 32 * S.natAbs + (c m).natAbs := by
      calc (32 * S + c m).natAbs
          ≤ (32 * S).natAbs + (c m).natAbs := Int.natAbs_add_le _ _
        _ = 32 * S.natAbs + (c m).natAbs := by rw [Int.natAbs_mul]; norm_num
    have h1 : (1 : ℕ) ≤ 32 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have hps : 32 ^ (m + 1) = 32 * 32 ^ m := by rw [pow_succ]; ring
    omega

/-- The per-gate NON-DEGENERACY side conditions: the additions are non-vertical
    (`xⱼ ≠ xT`) and the second additions are non-vertical (`tⱼ ≠ 0`). For the kimchi
    VarBaseMul gate these are exactly what the deployed guards (`scaleFast1`'s forbidden-value
    check, `scaleFast2`'s register range-check) are supposed to secure for ANY satisfying
    witness (their soundness). -/
structure NonDegen (g : Witness F) : Prop where
  x0 : g.x0 ≠ g.xT
  x1 : g.x1 ≠ g.xT
  x2 : g.x2 ≠ g.xT
  x3 : g.x3 ≠ g.xT
  x4 : g.x4 ≠ g.xT
  t0 : 2 * g.x0 + g.xT - g.s0 * g.s0 ≠ 0
  t1 : 2 * g.x1 + g.xT - g.s1 * g.s1 ≠ 0
  t2 : 2 * g.x2 + g.xT - g.s2 * g.s2 ≠ 0
  t3 : 2 * g.x3 + g.xT - g.s3 * g.s3 ≠ 0
  t4 : 2 * g.x4 + g.xT - g.s4 * g.s4 ≠ 0

/-- A full per-gate step: the nonsingular accumulator points `a0..a5`, the base `hT`, the gate
    constraints `holds`, and the `NonDegen` side conditions, in one flat bundle. The register
    subsystem `scalarMul` / `scalarMul_type2` consumes all of these via the gate `sound`. The
    deployed entry points derive a `GateStep` per row from `Holds` plus threading, via
    `gateStep_chain`. -/
structure GateStep (W : WeierstrassCurve.Affine F) (g : Witness F) : Prop where
  a0 : W.Nonsingular g.x0 g.y0
  a1 : W.Nonsingular g.x1 g.y1
  a2 : W.Nonsingular g.x2 g.y2
  a3 : W.Nonsingular g.x3 g.y3
  a4 : W.Nonsingular g.x4 g.y4
  a5 : W.Nonsingular g.x5 g.y5
  hT : W.Nonsingular g.xT g.yT
  holds : Holds g
  x0 : g.x0 ≠ g.xT
  x1 : g.x1 ≠ g.xT
  x2 : g.x2 ≠ g.xT
  x3 : g.x3 ≠ g.xT
  x4 : g.x4 ≠ g.xT
  t0 : 2 * g.x0 + g.xT - g.s0 * g.s0 ≠ 0
  t1 : 2 * g.x1 + g.xT - g.s1 * g.s1 ≠ 0
  t2 : 2 * g.x2 + g.xT - g.s2 * g.s2 ≠ 0
  t3 : 2 * g.x3 + g.xT - g.s3 * g.s3 ≠ 0
  t4 : 2 * g.x4 + g.xT - g.s4 * g.s4 ≠ 0

/-! ## Main theorem: variable-base scalar multiplication -/

/-- The computation the circuit provides. `m` chained `VarBaseMul` gates over a
    shared target `T`, threading BOTH the accumulator points `P` (gate `i`'s input
    `P i`, output `P (i+1)`) AND the scalar register `N` (input `N i = (g i).n`,
    output `N (i+1) = (g i).nPrime`), compute

        P m = 32^m·P₀ + k·T   with   (k : F) = 2·N m − 2·32^m·N 0 − (32^m − 1),

    i.e. the output point is the carried `32^m·P₀` plus `k·T`, where the integer
    scalar `k` is pinned to what the scalar register computed (`N 0 → N m`) — in
    signed-digit form. The proof folds the point chain with `chain_scalarMul` and
    the register chain with `chain_register`, both fed by the gate's
    `sound`. -/
theorem scalarMul
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → GateStep W (g i))
    (P : ℕ → W.Point) (T : W.Point) (N : ℕ → F)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).a5)
    (hregIn : ∀ i, i < m → N i = (g i).n)
    (hregOut : ∀ i, i < m → N (i + 1) = (g i).nPrime) :
    ∃ k : ℤ, P m = (32 : ℤ) ^ m • P 0 + k • T
           ∧ (k : F) = 2 * N m - 2 * (32 : F) ^ m * N 0 - ((32 : F) ^ m - 1)
           ∧ k.natAbs ≤ 32 ^ m - 1 := by
  obtain ⟨c, hc₁, hc₂, hc₃⟩ :
      ∃ c : ℕ → ℤ, (∀ i < m, P (i + 1) = (32 : ℤ) • P i + c i • T)
        ∧ (∀ i < m, (c i : F) = 2 * N (i + 1) - 64 * N i - 31)
        ∧ (∀ i < m, (c i).natAbs ≤ 31) := by
    choose! c hc₁ hc₂ hc₃ using fun i hi => sound W ha (g i)
      (gs i hi).a0 (gs i hi).a1 (gs i hi).a2 (gs i hi).a3 (gs i hi).a4 (gs i hi).a5
      (gs i hi).hT
      (gs i hi).x0 (gs i hi).x1 (gs i hi).x2 (gs i hi).x3 (gs i hi).x4
      (gs i hi).t0 (gs i hi).t1 (gs i hi).t2 (gs i hi).t3 (gs i hi).t4 (gs i hi).holds
    refine ⟨c, ?_, ?_, ?_⟩ <;> intros i hi <;> simp_all +decide only
    rw [hT i hi]
  refine ⟨∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i, ?_, ?_, ?_⟩
  · exact chain_scalarMul W m P T c hc₁
  · exact chain_register m N c hc₂
  · exact chain_sum_bound m c hc₃

/-- Clean variable-base scalar multiplication. When the accumulator is
    initialized to a multiple of the base (`P 0 = a · T`, `a : ℤ` — the circuit
    inits to `[2]T`), the carried `32^m·P₀` term is absorbed and the output is a
    SINGLE scalar multiple of the base:

        P m = n · T   for an explicit integer `n`,

    with `(n : F) = 32^m·a + 2·N m − 2·32^m·N 0 − (32^m − 1)`. So `m` chained
    `VarBaseMul` gates compute `[n]·T`: variable-base scalar multiplication of the
    base point `T`, the scalar `n` determined by the init `a` and the scalar
    register (`N 0 → N m`), in signed-digit form. -/
theorem scalarMul_baseMul
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → GateStep W (g i))
    (T : W.Point) (N : ℕ → F) (a : ℤ) (P : ℕ → W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).a5)
    (hregIn : ∀ i, i < m → N i = (g i).n)
    (hregOut : ∀ i, i < m → N (i + 1) = (g i).nPrime)
    (hP0 : P 0 = a • T) :
    ∃ n : ℤ, P m = n • T
           ∧ (n : F) = (32 : F) ^ m * (a : F) + 2 * N m
                        - 2 * (32 : F) ^ m * N 0 - ((32 : F) ^ m - 1)
           ∧ n.natAbs ≤ 32 ^ m * a.natAbs + (32 ^ m - 1) := by
  obtain ⟨k, hk, hkf, hkb⟩ := scalarMul W ha m g gs P T N hT hin hout hregIn hregOut
  refine ⟨(32 : ℤ) ^ m * a + k, ?_, ?_, ?_⟩
  · rw [hk, hP0, smul_smul, ← add_smul]
  · push_cast; rw [hkf]; ring
  · calc ((32 : ℤ) ^ m * a + k).natAbs
        ≤ ((32 : ℤ) ^ m * a).natAbs + k.natAbs := Int.natAbs_add_le _ _
      _ = 32 ^ m * a.natAbs + k.natAbs := by rw [Int.natAbs_mul, Int.natAbs_pow]; norm_num
      _ ≤ 32 ^ m * a.natAbs + (32 ^ m - 1) := by omega

/-! ## Matching the real circuit: scalar-mul by the pickles Type1 unshift -/

/-- The circuit computes `[s]·T` for the pickles-unshifted scalar `s`. At the real
    circuit's parameters — accumulator initialized to `[2]·T` (`P 0 = 2·T`) and
    scalar register started at `0` (`N 0 = 0`) — the `m` gates (processing `5m`
    bits) compute `P m = n·T` where the scalar is exactly the pickles Type1
    unshift of the final register value:

        (n : F) = unshiftType1 (5·m) (N m) = 2·(N m) + 2^(5m) + 1.

    This closes the loop: `2·t + 2^numBits + 1` is verbatim
    `Shifted_value.Type1.to_field`, and it reproduces the kimchi reference value
    `[1 + 2^numBits + 2·n_bits]·BasePoint` asserted in proof-systems
    `varbasemul.rs`'s own test. So feeding the gate the Type1-shifted scalar
    `t = shift(s)` (`N m = t`) makes it compute `[s]·T` — variable-base scalar
    multiplication by the original scalar `s`, the cross-field shift being the
    pickles `Shifted_value` contract. -/
theorem scalarMul_shifted
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → GateStep W (g i))
    (T : W.Point) (N : ℕ → F) (P : ℕ → W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).a5)
    (hregIn : ∀ i, i < m → N i = (g i).n)
    (hregOut : ∀ i, i < m → N (i + 1) = (g i).nPrime)
    (hP0 : P 0 = (2 : ℤ) • T) (hN0 : N 0 = 0) :
    ∃ n : ℤ, P m = n • T ∧ (n : F) = unshiftType1 (5 * m) (N m)
           ∧ n.natAbs ≤ 3 * 32 ^ m := by
  obtain ⟨n, hn, hnf, hnb⟩ :=
    scalarMul_baseMul W ha m g gs T N 2 P hT hin hout hregIn hregOut hP0
  refine ⟨n, hn, ?_, ?_⟩
  · have h32 : (2 : F) ^ (5 * m) = (32 : F) ^ m := by rw [pow_mul]; norm_num
    rw [hnf, hN0, unshiftType1, h32]
    push_cast
    ring
  · -- `a = 2`, so `(2 : ℤ).natAbs = 2` and `32^m·2 + (32^m − 1) ≤ 3·32^m`.
    have h2 : (2 : ℤ).natAbs = 2 := rfl
    rw [h2] at hnb
    omega

/-! ## The Type2 caller scalar: split + the odd correction -/

/-- Type2 scalar multiplication: split + the explicit low-bit correction. The
    `VarBaseMul` chain runs on the high part (register `N m = sHi`, giving
    `P m = [2·sHi + 2^(5m) + 1]·T`); the parity bit `sOdd` (a boolean column) then
    selects the final `if sOdd then P m else P m − T`. That corrected accumulator is
    `n·T` with `(n : F) = unshiftType2 (5m) (N m) sOdd = 2·(N m) + sOdd + 2^(5m)` — the
    Type2 scalar — in both bit cases. The correction is stated on `P m` directly (no
    prover-supplied output point or correction relation). -/
theorem scalarMul_type2
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → GateStep W (g i))
    (T : W.Point) (N : ℕ → F) (P : ℕ → W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).a5)
    (hregIn : ∀ i, i < m → N i = (g i).n)
    (hregOut : ∀ i, i < m → N (i + 1) = (g i).nPrime)
    (hP0 : P 0 = (2 : ℤ) • T) (hN0 : N 0 = 0)
    (sOdd : F) (hsOdd : sOdd = 0 ∨ sOdd = 1) :
    ∃ n : ℤ, (n : F) = unshiftType2 (5 * m) (N m) sOdd
      ∧ ((sOdd = 1 ∧ P m = n • T) ∨ (sOdd = 0 ∧ P m - T = n • T)) := by
  obtain ⟨n, hn, hnf, _⟩ :=
    scalarMul_shifted W ha m g gs T N P hT hin hout hregIn hregOut hP0 hN0
  rcases hsOdd with ho | ho
  · refine ⟨n - 1, ?_, Or.inr ⟨ho, ?_⟩⟩
    · push_cast; rw [hnf, ho, unshiftType1, unshiftType2]; ring
    · rw [hn, sub_smul, one_zsmul]
  · exact ⟨n, by rw [hnf, ho, unshiftType1, unshiftType2]; ring, Or.inl ⟨ho, hn⟩⟩

/-! ## Group-order non-degeneracy toolkit

In the point group of a short-Weierstrass curve the `order` is prime, so a nonzero point times a
scalar strictly between `0` and `order` is itself nonzero. Hence a multiple `k • T` of a nonzero
point `T`, with `k` strictly between `1` and `order − 1`, is neither `T` nor `−T`, and has a
different `x`-coordinate than `T`. These library lemmas are the mathematical core of "the partial
accumulators stay away from `±T`", consumed by the per-row non-degeneracy below. -/

/-- **Core non-degeneracy.** With prime `order`, a nonzero point times a scalar strictly
    between `0` and `order` is nonzero. -/
lemma smul_ne_zero_of_lt (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] {T : c.Point} (hT : T ≠ 0)
    {k : ℤ} (h0 : 0 < k) (hlt : k < (c.order : ℤ)) : k • T ≠ 0 := by
  intro h_contra
  -- prime `order` together with `0 < k < order` forces `gcd k order = 1`
  have h_coprime : Int.gcd k (c.order : ℤ) = 1 := by
    refine Nat.coprime_comm.mp (c.order_prime.coprime_iff_not_dvd.mpr fun hd => ?_)
    have := Int.le_of_dvd (by positivity) (Int.natCast_dvd.mpr hd)
    omega
  -- Bézout: `k * a + order * b = 1`
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, k * a + (c.order : ℤ) * b = 1 := by
    have h := Int.gcd_eq_gcd_ab k (c.order : ℤ)
    exact ⟨_, _, h.symm.trans (by rw [h_coprime]; simp)⟩
  -- hence `T = a • (k • T) + b • (order • T)`, and both terms vanish
  have h_decomp : T = a • (k • T) + b • ((c.order : ℤ) • T) := by
    rw [← mul_smul, ← mul_smul, ← add_smul, mul_comm a k, mul_comm b (c.order : ℤ), hab,
      one_zsmul]
  rw [h_contra, c.order_smul, smul_zero, smul_zero, add_zero] at h_decomp
  exact hT h_decomp

/-- **x-coordinate bridge.** On a short-Weierstrass curve, a point that is neither `T`
    nor `−T` has a different `x`-coordinate. -/
lemma x_ne_xT_of_ne_base (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] {x y xT yT : F}
    (h : c.Nonsingular x y) (hT : c.Nonsingular xT yT)
    (hne : Point.some _ _ h ≠ Point.some _ _ hT) (hneg : Point.some _ _ h ≠ -Point.some _ _ hT) :
    x ≠ xT := by
  contrapose! hneg
  contrapose! hne
  simp_all +decide [WeierstrassCurve.Affine.negY]
  have h_eq : y ^ 2 + c.a₁ * xT * y + c.a₃ * y
      = yT ^ 2 + c.a₁ * xT * yT + c.a₃ * yT := by
    have := h.1; have := hT.1
    simp_all +decide [WeierstrassCurve.Affine.equation_iff]
  exact mul_left_cancel₀ (sub_ne_zero_of_ne hne) (by linear_combination h_eq)

/-- **Second-addition non-vertical guarantee.** The geometric non-degeneracy
    `2·I + Q ≠ 0` forces the field condition `tⱼ = 2·xi + xb − s1² ≠ 0` that the
    `VarBaseMul` gate bundles. -/
lemma singleBit_tne_of_double_ne (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)]
    {b xb yb s1 xi yi xo yo : F}
    (hI : c.Nonsingular xi yi)
    (hQ : c.Nonsingular xb ((2 * b - 1) * yb))
    (hxne : xi ≠ xb)
    (h : singleBitHolds b xb yb s1 xi yi xo yo)
    (hdbl : (2 : ℤ) • Point.some _ _ hI + Point.some _ _ hQ ≠ 0) :
    2 * xi + xb - s1 * s1 ≠ 0 := by
  contrapose! hdbl
  -- the first addition `I + Q` is the secant point `R = (rx, ry)` with slope `s1`
  have hR : ∃ hR : c.Nonsingular (s1 * s1 - xi - xb)
      (s1 * (xi - (s1 * s1 - xi - xb)) - yi),
      Point.some _ _ hI + Point.some _ _ hQ = Point.some _ _ hR := by
    apply secant_add c c.short hI hQ hxne (l := s1)
    · rw [eq_div_iff (sub_ne_zero_of_ne hxne)]
      linear_combination' ((singleBitHolds_iff _ _ _ _ _ _ _ _).mp h).2.1
    · rfl
    · rfl
  grind +suggestions

/-- **t-condition self-enforcement.** The gate constraints together with prime order
    already force `t ≠ 0` — the forbidden check is NOT needed for the second-addition
    non-degeneracy. If `t = 2·xi + xb − s1² = 0`, then the `xo` constraint
    `u² − t²·(…) = 0` collapses to `u² = 0`, i.e. `u = 2·yi − t·s1 = 2·yi = 0`, so
    `yi = 0`. But a nonsingular affine point with `yi = 0` equals its own negation
    (short Weierstrass), hence is 2-torsion; on a group of odd prime `order` there is no
    such point. Contradiction.

    The hypothesis `c.order ≠ 2` (equivalently, the prime `order` is odd) is genuinely
    required, not a convenience: for `order = 2` the statement is false. E.g. over
    `ZMod 7` with the curve `y² = x³ + 6` (group `(ℤ/2)²`, so `order = 2`), the input
    point `(xi, yi) = (1, 0)` is nonsingular and `singleBitHolds 0 5 0 0 1 0 0 0` holds,
    yet `2·xi + xb − s1² = 2·1 + 5 − 0 = 7 = 0`. The Pasta `order` is a 255-bit prime,
    so `order ≠ 2` there. But `order ≠ 2` does not follow from `order` being prime (`2`
    is prime) or from the short shape, so it is taken as a separate hypothesis. -/
lemma tne_of_holds (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    {b xb yb s1 xi yi xo yo : F}
    (hI : c.Nonsingular xi yi)
    (hh : singleBitHolds b xb yb s1 xi yi xo yo) :
    2 * xi + xb - s1 * s1 ≠ 0 := by
  intro ht
  -- Step 1: the `xo` constraint collapses (with `t = 0`) to `4·yi² = 0`, so `yi = 0`.
  have hyi : yi = 0 := by
    rw [singleBitHolds_iff] at hh
    obtain ⟨_, _, h3, _⟩ := hh
    have htt : xi - (s1 * s1 - xi - xb) = 0 := by linear_combination ht
    rw [htt] at h3
    have hy2 : yi * yi = 0 := by
      have hfour : (4 : F) * (yi * yi) = 0 := by linear_combination h3
      have h4ne : (4 : F) ≠ 0 := by
        have h44 : (4 : F) = 2 * 2 := by norm_num
        rw [h44]; exact mul_ne_zero h2 h2
      exact (mul_eq_zero.mp hfour).resolve_left h4ne
    exact mul_self_eq_zero.mp hy2
  -- Step 2: with `yi = 0` (and short shape `a₁ = a₃ = 0`), `negY = yi`, so `P = -P`.
  obtain ⟨ha1, -, ha3⟩ := c.short
  have hneg : negY c xi yi = yi := by
    simp [WeierstrassCurve.Affine.negY, ha1, ha3, hyi]
  have hPselfneg : -(Point.some _ _ hI) = Point.some _ _ hI := by
    rw [Point.neg_some]; congr 1
  -- Step 3: `P = -P` gives `2 • P = P + (-P) = 0`.
  have hPne : Point.some _ _ hI ≠ 0 := Point.some_ne_zero hI
  have h2P : (2 : ℤ) • Point.some _ _ hI = 0 := by
    rw [two_zsmul]; nth_rewrite 2 [← hPselfneg]; rw [add_neg_cancel]
  -- Step 4: `0 < 2 < order` (prime, `≠ 2`) contradicts `2 • P = 0` for `P ≠ 0`.
  have hlt : (2 : ℤ) < (c.order : ℤ) := by
    have : 3 ≤ c.order := by have := c.order_prime.two_le; omega
    exact_mod_cast this
  exact smul_ne_zero_of_lt c hPne (by norm_num) hlt h2P

/-! ## Soundness: avoiding `±T` makes every row non-degenerate

The kimchi VarBaseMul gate uses incomplete addition, so each row needs its additions to be
non-vertical (`NonDegen`). The complete obstruction is the forbidden band `s ∈ [-15, 15] (mod
order)` — equivalently the eleven residues `forbiddenValues order` for a prime `order ≡ 1 (mod 4)`.
Excluding it makes every satisfying witness's rows non-degenerate, the guarantee the deployed
two-residue runtime check does not by itself provide. The accumulator nonsingularity is derived,
not assumed: from `Holds` per row plus the base, threading, and initial accumulator `2·T`,
`gate_chain_produce` and `gateStep_chain` produce the whole point sequence, and the two regime roots
conclude correctness — `varBaseMul_subwrap_correct` unconditionally below the order,
`varBaseMul_forbidden_correct` at the one-wrap width. -/

/-- The forbidden set for VarBaseMul non-degeneracy: the EXACT Pasta reachable
    degenerate residues `forbiddenResidues = {0, ±1, ±2, ±3, 5, 7, 9, 11}`. Sound for any
    prime `order ≡ 1 (mod 4)` (the actual degenerate set is `⊆` these), and exactly tight
    for the Pasta primes. -/
def forbiddenValues (order : ℕ) : Set ℤ :=
  {s | ∃ t ∈ Ladder.forbiddenResidues, (order : ℤ) ∣ (s - t)}

/-- **Prime order ⇒ full order.** For a nonzero point `T` on a `short-Weierstrass curve`, a scalar
    multiple `m • T` vanishes iff `order ∣ m`. (`order` is prime and `order • T = 0`, so
    `addOrderOf T ∣ order`; nonzero `T` rules out `addOrderOf T = 1`, hence it equals
    `order`.) -/
lemma zsmul_eq_zero_iff_order_dvd (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] {T : c.Point} (hT : T ≠ 0) (m : ℤ) :
    m • T = 0 ↔ (c.order : ℤ) ∣ m := by
  have hdvd : (addOrderOf T : ℤ) ∣ (c.order : ℤ) :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr (c.order_smul T)
  have horder : addOrderOf T = c.order := by
    have hnat : addOrderOf T ∣ c.order := by exact_mod_cast hdvd
    rcases (Nat.Prime.eq_one_or_self_of_dvd c.order_prime _ hnat) with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hT
    · exact h1
  rw [← addOrderOf_dvd_iff_zsmul_eq_zero, horder]

/-- The raw bit processed at sub-step `j`: bit `j % 5` of gate `j / 5`. -/
def gateBit (g : ℕ → Witness F) (j : ℕ) : F :=
  match j % 5 with
  | 0 => (g (j / 5)).b0
  | 1 => (g (j / 5)).b1
  | 2 => (g (j / 5)).b2
  | 3 => (g (j / 5)).b3
  | _ => (g (j / 5)).b4

/-- The signed bit `±1` at sub-step `j`. -/
def gateBitSign (g : ℕ → Witness F) (j : ℕ) : ℤ := if gateBit g j = 1 then 1 else -1

/-- The integer double-and-add ladder over the gate bits, with `k 0 = 2`. -/
def gateLadder (g : ℕ → Witness F) : ℕ → ℤ
  | 0 => 2
  | j + 1 => 2 * gateLadder g j + gateBitSign g j

@[simp] lemma gateLadder_zero (g : ℕ → Witness F) : gateLadder g 0 = 2 := rfl

lemma gateLadder_succ (g : ℕ → Witness F) (j : ℕ) :
    gateLadder g (j + 1) = 2 * gateLadder g j + gateBitSign g j := rfl

lemma gateBitSign_eq (g : ℕ → Witness F) (j : ℕ) :
    gateBitSign g j = 1 ∨ gateBitSign g j = -1 := by
  unfold gateBitSign; split <;> simp

/-- The unsigned bit at sub-step `j`: `1` if set, else `0` (same `= 1` test as `gateBitSign`). -/
def ubit (g : ℕ → Witness F) (j : ℕ) : ℤ := if gateBit g j = 1 then 1 else 0

/-- The signed digit is `2·(unsigned bit) − 1`, unconditionally (same `gateBit = 1` test). -/
lemma gateBitSign_eq_ubit (g : ℕ → Witness F) (j : ℕ) :
    gateBitSign g j = 2 * ubit g j - 1 := by
  unfold gateBitSign ubit; split <;> ring

/-- The unsigned scalar register the ladder bits encode (Horner over `ubit`), `r 0 = 0`. -/
def gateRegister (g : ℕ → Witness F) : ℕ → ℤ
  | 0 => 0
  | j + 1 => 2 * gateRegister g j + ubit g j

lemma gateRegister_succ (g : ℕ → Witness F) (j : ℕ) :
    gateRegister g (j + 1) = 2 * gateRegister g j + ubit g j := rfl

/-- **Signed ladder ↔ unsigned register bridge.** The signed double-and-add top is the `Type1`
    unshift of the unsigned register it encodes, as an honest **ℤ** identity (no booleanity needed —
    the signed digits are `2·ubit − 1`): `gateLadder g L = 2·gateRegister g L + 2^L + 1`. This links
    the non-degeneracy path (`gateLadder`) to the scalar-register path: a range-check
    `gateRegister < 2^k` directly bounds the ladder top, hence the deployed `hcanonical`. -/
lemma gateLadder_eq_register (g : ℕ → Witness F) (L : ℕ) :
    gateLadder g L = 2 * gateRegister g L + 2 ^ L + 1 := by
  induction L with
  | zero => norm_num [gateLadder, gateRegister]
  | succ j ih =>
    rw [gateLadder_succ, ih, gateBitSign_eq_ubit, gateRegister_succ, pow_succ]; ring

omit [Field F] [DecidableEq F] in
/-- The five raw bits of gate `i` are the sub-step bits `5i … 5i+4`. -/
lemma gateBit_block (g : ℕ → Witness F) (i : ℕ) :
    gateBit g (5 * i) = (g i).b0 ∧ gateBit g (5 * i + 1) = (g i).b1
      ∧ gateBit g (5 * i + 2) = (g i).b2 ∧ gateBit g (5 * i + 3) = (g i).b3
      ∧ gateBit g (5 * i + 4) = (g i).b4 := by
  unfold gateBit; simp +decide [ Nat.add_mod ] ;
  norm_num [ Nat.add_div ]

/-- The signed bit `e` produced by `signed_target` matches `gateBitSign`. -/
lemma e_eq_gateBitSign (g : ℕ → Witness F) (j : ℕ) {b : F} (hgb : gateBit g j = b)
    (hbit : b = 0 ∨ b = 1) {e : ℤ} (he2 : (e : F) = 2 * b - 1) (he : e = 1 ∨ e = -1)
    (h2 : (2 : F) ≠ 0) : e = gateBitSign g j := by
  cases hbit <;> simp_all +decide [ gateBitSign ];
  · cases he <;> simp_all +decide;
    exact h2 ( by linear_combination' he2 );
  · rcases he with ( rfl | rfl ) <;> norm_num at *;
    grind +extAll

/-- Per sub-step advance using ONLY the x-condition `k ≢ ±1`; the t-condition `t ≠ 0`
    is supplied by `tne_of_holds` (the constraints + prime order), not by `2k ≢ ±1`. -/
lemma gate_step_advance' (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    {xT yT b s1 xi yi xo yo : F}
    (hTns : c.Nonsingular xT yT)
    (hI : c.Nonsingular xi yi)
    (hQ : c.Nonsingular xT ((2 * b - 1) * yT))
    (hbit : b = 0 ∨ b = 1)
    (hTne : Point.some _ _ hTns ≠ 0)
    (k : ℤ) (hIk : Point.some _ _ hI = k • Point.some _ _ hTns)
    (hkx1 : ¬ ((c.order : ℤ) ∣ (k - 1))) (hkx2 : ¬ ((c.order : ℤ) ∣ (k + 1)))
    (hh : singleBitHolds b xT yT s1 xi yi xo yo) :
    xi ≠ xT ∧ (2 * xi + xT - s1 * s1 ≠ 0) ∧
      ∃ (hO : c.Nonsingular xo yo) (e : ℤ),
        (e = 1 ∨ e = -1) ∧ (e : F) = 2 * b - 1 ∧
          Point.some _ _ hO = (2 * k + e) • Point.some _ _ hTns := by
  obtain ⟨e, he, he'⟩ := signed_target c c.short hTns hQ hbit
  have hxne : xi ≠ xT := by
    apply x_ne_xT_of_ne_base c hI hTns
    · contrapose! hkx1
      have hd : (k - 1) • Point.some _ _ hTns = 0 := by
        rw [sub_smul, one_smul, ← hIk, hkx1, sub_self]
      exact (zsmul_eq_zero_iff_order_dvd c hTne _).1 hd
    · contrapose! hkx2
      rw [← zsmul_eq_zero_iff_order_dvd c hTne, add_zsmul, one_zsmul, ← hIk, hkx2,
        neg_add_cancel]
  have htne : 2 * xi + xT - s1 * s1 ≠ 0 := tne_of_holds c h2 hodd hI hh
  obtain ⟨hO, hOeq⟩ := singleBit_sound c c.short b xT yT s1 xi yi xo yo hI hQ hxne htne hh
  refine ⟨hxne, htne, hO, e, he'.2, he'.1, ?_⟩
  rw [hOeq, hIk, he]
  module

/-- One gate block, deriving the output point's nonsingularity rather than asserting it: from the
    input point `a0` on-curve, the constraint `Holds`, and the base, it chains the five
    `gate_step_advance'` steps and produces `a5` existentially, together with the row's `NonDegen`
    side conditions. The deployed soundness needs only the threaded input. This mirrors EndoMul's
    `gate_advance`. -/
lemma gate_block_produce (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] (g : ℕ → Witness F) (i : ℕ)
    (h2 : (2 : F) ≠ 0)
    {T : c.Point} (hTne : T ≠ 0)
    (hTns : c.Nonsingular (g i).xT (g i).yT) (hTeq : T = Point.some _ _ hTns)
    (ha0ns : c.Nonsingular (g i).x0 (g i).y0) (hh : Holds (g i))
    (ha0 : Point.some _ _ ha0ns = gateLadder g (5 * i) • T)
    (hodd : c.order ≠ 2)
    (hnd : ∀ ℓ, ℓ < 5 →
        ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) - 1)
          ∧ ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) + 1)) :
    NonDegen (g i) ∧ ∃ ha5ns : c.Nonsingular (g i).x5 (g i).y5,
      Point.some _ _ ha5ns = gateLadder g (5 * i + 5) • T := by
  have hT0 : Point.some _ _ hTns ≠ 0 := by rw [← hTeq]; exact hTne
  obtain ⟨_hdec, hsb0, hsb1, hsb2, hsb3, hsb4⟩ := (holds_iff _).mp hh
  obtain ⟨gb0, gb1, gb2, gb3, gb4⟩ := gateBit_block g i
  have bit : ∀ {x : F}, x * x - x = 0 → x = 0 ∨ x = 1 := by
    intro x hx
    rcases mul_eq_zero.mp (show x * (x - 1) = 0 by linear_combination hx) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  have ha0' : Point.some _ _ ha0ns = gateLadder g (5 * i) • Point.some _ _ hTns := by
    rw [hTeq] at ha0; exact ha0
  obtain ⟨hx0, ht0, hO0, e0, hepm0, hef0, hOeq0⟩ :=
    gate_step_advance' c h2 hodd hTns ha0ns
      (signed_target_nonsingular c c.short hTns (bit hsb0.bool))
      (bit hsb0.bool) hT0 (gateLadder g (5 * i)) ha0'
      (hnd 0 (by omega)).1 (hnd 0 (by omega)).2 hsb0
  have ha1 : Point.some _ _ hO0 = gateLadder g (5 * i + 1) • Point.some _ _ hTns := by
    rw [hOeq0, e_eq_gateBitSign g (5 * i) gb0 (bit hsb0.bool) hef0 hepm0 h2, ← gateLadder_succ]
  obtain ⟨hx1, ht1, hO1, e1, hepm1, hef1, hOeq1⟩ :=
    gate_step_advance' c h2 hodd hTns hO0 (signed_target_nonsingular c c.short hTns (bit hsb1.bool))
      (bit hsb1.bool) hT0 (gateLadder g (5 * i + 1)) ha1
      (hnd 1 (by omega)).1 (hnd 1 (by omega)).2 hsb1
  have ha2 : Point.some _ _ hO1 = gateLadder g (5 * i + 2) • Point.some _ _ hTns := by
    rw [hOeq1, e_eq_gateBitSign g (5 * i + 1) gb1 (bit hsb1.bool) hef1 hepm1 h2, ← gateLadder_succ]
  obtain ⟨hx2, ht2, hO2, e2, hepm2, hef2, hOeq2⟩ :=
    gate_step_advance' c h2 hodd hTns hO1 (signed_target_nonsingular c c.short hTns (bit hsb2.bool))
      (bit hsb2.bool) hT0 (gateLadder g (5 * i + 2)) ha2
      (hnd 2 (by omega)).1 (hnd 2 (by omega)).2 hsb2
  have ha3 : Point.some _ _ hO2 = gateLadder g (5 * i + 3) • Point.some _ _ hTns := by
    rw [hOeq2, e_eq_gateBitSign g (5 * i + 2) gb2 (bit hsb2.bool) hef2 hepm2 h2, ← gateLadder_succ]
  obtain ⟨hx3, ht3, hO3, e3, hepm3, hef3, hOeq3⟩ :=
    gate_step_advance' c h2 hodd hTns hO2 (signed_target_nonsingular c c.short hTns (bit hsb3.bool))
      (bit hsb3.bool) hT0 (gateLadder g (5 * i + 3)) ha3
      (hnd 3 (by omega)).1 (hnd 3 (by omega)).2 hsb3
  have ha4 : Point.some _ _ hO3 = gateLadder g (5 * i + 4) • Point.some _ _ hTns := by
    rw [hOeq3, e_eq_gateBitSign g (5 * i + 3) gb3 (bit hsb3.bool) hef3 hepm3 h2, ← gateLadder_succ]
  obtain ⟨hx4, ht4, hO4, e4, hepm4, hef4, hOeq4⟩ :=
    gate_step_advance' c h2 hodd hTns hO3 (signed_target_nonsingular c c.short hTns (bit hsb4.bool))
      (bit hsb4.bool) hT0 (gateLadder g (5 * i + 4)) ha4
      (hnd 4 (by omega)).1 (hnd 4 (by omega)).2 hsb4
  have ha5 : Point.some _ _ hO4 = gateLadder g (5 * i + 5) • Point.some _ _ hTns := by
    rw [hOeq4, e_eq_gateBitSign g (5 * i + 4) gb4 (bit hsb4.bool) hef4 hepm4 h2, ← gateLadder_succ]
  exact ⟨⟨hx0, hx1, hx2, hx3, hx4, ht0, ht1, ht2, ht3, ht4⟩, hO4, by rw [hTeq]; exact ha5⟩

/-- Like `gate_block_produce`, but returns all five derived accumulator points `a1..a5` (not just
    `a5`), so the register subsystem (`scalarMul` / `scalarMul_type2`, which consume the whole
    `GateStep` bundle) can be fed the full per-row data. Same five-`gate_step_advance'` chain. -/
lemma gate_block_full (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] (g : ℕ → Witness F) (i : ℕ)
    (h2 : (2 : F) ≠ 0)
    {T : c.Point} (hTne : T ≠ 0)
    (hTns : c.Nonsingular (g i).xT (g i).yT) (hTeq : T = Point.some _ _ hTns)
    (ha0ns : c.Nonsingular (g i).x0 (g i).y0) (hh : Holds (g i))
    (ha0 : Point.some _ _ ha0ns = gateLadder g (5 * i) • T)
    (hodd : c.order ≠ 2)
    (hnd : ∀ ℓ, ℓ < 5 →
        ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) - 1)
          ∧ ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) + 1)) :
    NonDegen (g i) ∧ ∃ (a1 : c.Nonsingular (g i).x1 (g i).y1)
      (_a2 : c.Nonsingular (g i).x2 (g i).y2) (_a3 : c.Nonsingular (g i).x3 (g i).y3)
      (_a4 : c.Nonsingular (g i).x4 (g i).y4) (a5 : c.Nonsingular (g i).x5 (g i).y5),
      Point.some _ _ a5 = gateLadder g (5 * i + 5) • T := by
  have hT0 : Point.some _ _ hTns ≠ 0 := by rw [← hTeq]; exact hTne
  obtain ⟨_hdec, hsb0, hsb1, hsb2, hsb3, hsb4⟩ := (holds_iff _).mp hh
  obtain ⟨gb0, gb1, gb2, gb3, gb4⟩ := gateBit_block g i
  have bit : ∀ {x : F}, x * x - x = 0 → x = 0 ∨ x = 1 := by
    intro x hx
    rcases mul_eq_zero.mp (show x * (x - 1) = 0 by linear_combination hx) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  have ha0' : Point.some _ _ ha0ns = gateLadder g (5 * i) • Point.some _ _ hTns := by
    rw [hTeq] at ha0; exact ha0
  obtain ⟨hx0, ht0, hO0, e0, hepm0, hef0, hOeq0⟩ :=
    gate_step_advance' c h2 hodd hTns ha0ns
      (signed_target_nonsingular c c.short hTns (bit hsb0.bool))
      (bit hsb0.bool) hT0 (gateLadder g (5 * i)) ha0'
      (hnd 0 (by omega)).1 (hnd 0 (by omega)).2 hsb0
  have ha1 : Point.some _ _ hO0 = gateLadder g (5 * i + 1) • Point.some _ _ hTns := by
    rw [hOeq0, e_eq_gateBitSign g (5 * i) gb0 (bit hsb0.bool) hef0 hepm0 h2, ← gateLadder_succ]
  obtain ⟨hx1, ht1, hO1, e1, hepm1, hef1, hOeq1⟩ :=
    gate_step_advance' c h2 hodd hTns hO0 (signed_target_nonsingular c c.short hTns (bit hsb1.bool))
      (bit hsb1.bool) hT0 (gateLadder g (5 * i + 1)) ha1
      (hnd 1 (by omega)).1 (hnd 1 (by omega)).2 hsb1
  have ha2 : Point.some _ _ hO1 = gateLadder g (5 * i + 2) • Point.some _ _ hTns := by
    rw [hOeq1, e_eq_gateBitSign g (5 * i + 1) gb1 (bit hsb1.bool) hef1 hepm1 h2, ← gateLadder_succ]
  obtain ⟨hx2, ht2, hO2, e2, hepm2, hef2, hOeq2⟩ :=
    gate_step_advance' c h2 hodd hTns hO1 (signed_target_nonsingular c c.short hTns (bit hsb2.bool))
      (bit hsb2.bool) hT0 (gateLadder g (5 * i + 2)) ha2
      (hnd 2 (by omega)).1 (hnd 2 (by omega)).2 hsb2
  have ha3 : Point.some _ _ hO2 = gateLadder g (5 * i + 3) • Point.some _ _ hTns := by
    rw [hOeq2, e_eq_gateBitSign g (5 * i + 2) gb2 (bit hsb2.bool) hef2 hepm2 h2, ← gateLadder_succ]
  obtain ⟨hx3, ht3, hO3, e3, hepm3, hef3, hOeq3⟩ :=
    gate_step_advance' c h2 hodd hTns hO2 (signed_target_nonsingular c c.short hTns (bit hsb3.bool))
      (bit hsb3.bool) hT0 (gateLadder g (5 * i + 3)) ha3
      (hnd 3 (by omega)).1 (hnd 3 (by omega)).2 hsb3
  have ha4 : Point.some _ _ hO3 = gateLadder g (5 * i + 4) • Point.some _ _ hTns := by
    rw [hOeq3, e_eq_gateBitSign g (5 * i + 3) gb3 (bit hsb3.bool) hef3 hepm3 h2, ← gateLadder_succ]
  obtain ⟨hx4, ht4, hO4, e4, hepm4, hef4, hOeq4⟩ :=
    gate_step_advance' c h2 hodd hTns hO3 (signed_target_nonsingular c c.short hTns (bit hsb4.bool))
      (bit hsb4.bool) hT0 (gateLadder g (5 * i + 4)) ha4
      (hnd 4 (by omega)).1 (hnd 4 (by omega)).2 hsb4
  have ha5 : Point.some _ _ hO4 = gateLadder g (5 * i + 5) • Point.some _ _ hTns := by
    rw [hOeq4, e_eq_gateBitSign g (5 * i + 4) gb4 (bit hsb4.bool) hef4 hepm4 h2, ← gateLadder_succ]
  exact ⟨⟨hx0, hx1, hx2, hx3, hx4, ht0, ht1, ht2, ht3, ht4⟩, hO0, hO1, hO2, hO3, hO4,
    by rw [hTeq]; exact ha5⟩

/-- Final-accumulator coordinates after `m` rows (row 0's `x0`/`y0` if `m = 0`, else row `(m-1)`'s
    `x5`/`y5`) — the concrete stand-in for the abstract accumulator point `P m`. -/
def accX (g : ℕ → Witness F) : ℕ → F
  | 0 => (g 0).x0
  | k + 1 => (g k).x5

def accY (g : ℕ → Witness F) : ℕ → F
  | 0 => (g 0).y0
  | k + 1 => (g k).y5

/-- **Chained non-degeneracy and scalar multiple.** Over `m` rows, from `Holds` per row, the base
    nonsingularity (row 0), the column threading (`(g (i+1)).x0 = (g i).x5`), and the initial
    accumulator `2·T`, the chain derives every intermediate point's nonsingularity
    (`gate_block_produce`) and concludes the final accumulator equals `s·T` with every row
    `NonDegen`. The prover supplies only `Holds` and the threading; the accumulator nonsingularity
    is derived. The proof inducts on `k ≤ m`, carrying the invariant
    `∃ hk, Point.some _ _ hk = gateLadder g (5·k) • T`: the base case is `hP0ns`/`hP0`
    (`gateLadder g 0 = 2`), and each step feeds the threaded input (base transported to row `k` via
    `hbase`) to `gate_block_produce`. -/
lemma gate_chain_produce (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (m : ℕ) (g : ℕ → Witness F) (T : c.Point) (s : ℤ) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : c.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : c.Nonsingular (g 0).x0 (g 0).y0)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    (hND : ∀ n, n < 5 * m →
        ¬ (c.order : ℤ) ∣ (gateLadder g n - 1) ∧ ¬ (c.order : ℤ) ∣ (gateLadder g n + 1)
          ∧ ¬ (c.order : ℤ) ∣ (2 * gateLadder g n - 1)
          ∧ ¬ (c.order : ℤ) ∣ (2 * gateLadder g n + 1))
    (hs : s = gateLadder g (5 * m)) :
    ∃ hfin : c.Nonsingular (accX g m) (accY g m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (g i) := by
  -- Point congruence across equal coordinates (local analog of `Gate.EndoMul.some_congr`).
  have some_congr : ∀ {x x' y y' : F} (h : c.Nonsingular x y) (h' : c.Nonsingular x' y'),
      x = x' → y = y' → Point.some _ _ h = Point.some _ _ h' := by
    intro x x' y y' h h' hx hy; subst hx; subst hy; rfl
  -- coordinate threading: row `k`'s input column equals the accumulator at step `k`
  have haccP : ∀ k, k < m → (g k).x0 = accX g k ∧ (g k).y0 = accY g k := by
    intro k hk
    cases k with
    | zero => exact ⟨rfl, rfl⟩
    | succ j => exact hthread j hk
  -- per-step accumulator nonsingularity + point value + accumulated non-degeneracy
  have key : ∀ k, k ≤ m → ∃ hk : c.Nonsingular (accX g k) (accY g k),
      Point.some _ _ hk = gateLadder g (5 * k) • T ∧ (∀ i, i < k → NonDegen (g i)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨hP0ns, ?_, ?_⟩
      · change Point.some (g 0).x0 (g 0).y0 hP0ns = gateLadder g (5 * 0) • T
        rw [hP0]; simp only [Nat.mul_zero, gateLadder_zero]
      · intro i hi; omega
    | succ j ih =>
      intro hj1
      have hj' : j < m := by omega
      obtain ⟨hk, hPk, hNDk⟩ := ih (by omega)
      -- transport the base nonsingularity to row `j`
      obtain ⟨hbx, hby⟩ := hbase j hj'
      have hTns_j : c.Nonsingular (g j).xT (g j).yT := by rw [hbx, hby]; exact hTns
      have hTeq_j : T = Point.some _ _ hTns_j := by
        rw [hTeq]; exact some_congr hTns hTns_j hbx.symm hby.symm
      -- transport the threaded input accumulator to row `j`'s input column
      obtain ⟨hx0, hy0⟩ := haccP j hj'
      have ha0ns_j : c.Nonsingular (g j).x0 (g j).y0 := by rw [hx0, hy0]; exact hk
      have ha0_j : Point.some _ _ ha0ns_j = gateLadder g (5 * j) • T := by
        rw [some_congr ha0ns_j hk hx0 hy0]; exact hPk
      obtain ⟨hNDj, ha5ns, ha5eq⟩ :=
        gate_block_produce c g j h2 hTne hTns_j hTeq_j ha0ns_j (hholds j hj') ha0_j hodd
          (fun ℓ _ => ⟨(hND (5 * j + ℓ) (by omega)).1, (hND (5 * j + ℓ) (by omega)).2.1⟩)
      -- `accX g (j+1) = (g j).x5` and `gateLadder g (5*(j+1)) = gateLadder g (5*j+5)` defeq
      refine ⟨ha5ns, ?_, ?_⟩
      · rw [show 5 * (j + 1) = 5 * j + 5 from by ring]; exact ha5eq
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact hNDk i h
        · subst h; exact hNDj
  obtain ⟨hfin, hPfin, hNDfin⟩ := key m le_rfl
  exact ⟨hfin, by rw [hs]; exact hPfin, hNDfin⟩

/-- **`GateStep`-producing fold.** From `Holds` per row, the base, the threading, and the initial
    accumulator `2·T`, derives the full per-row `GateStep` bundle (every `a0..a5`, via
    `gate_block_full`) together with the threaded point sequence `P` — exactly the inputs the
    register subsystem (`scalarMul` / `scalarMul_type2`) consumes. The `scaleFast2` analog of
    `gate_chain_produce`. -/
lemma gateStep_chain (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (m : ℕ) (g : ℕ → Witness F) (T : c.Point) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : c.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : c.Nonsingular (g 0).x0 (g 0).y0)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    (hND : ∀ n, n < 5 * m →
        ¬ (c.order : ℤ) ∣ (gateLadder g n - 1) ∧ ¬ (c.order : ℤ) ∣ (gateLadder g n + 1)) :
    ∃ (gs : ∀ i, i < m → GateStep c (g i)) (P : ℕ → c.Point),
      (∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
        ∧ (∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).a0)
        ∧ (∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).a5)
        ∧ P 0 = (2 : ℤ) • T := by
  -- Point congruence across equal coordinates (local analog of `Gate.EndoMul.some_congr`).
  have some_congr : ∀ {x x' y y' : F} (h : c.Nonsingular x y) (h' : c.Nonsingular x' y'),
      x = x' → y = y' → Point.some _ _ h = Point.some _ _ h' := by
    intro x x' y y' h h' hx hy; subst hx; subst hy; rfl
  -- coordinate threading: row `k`'s input column equals the accumulator at step `k`
  have haccP : ∀ k, k < m → (g k).x0 = accX g k ∧ (g k).y0 = accY g k := by
    intro k hk
    cases k with
    | zero => exact ⟨rfl, rfl⟩
    | succ j => exact hthread j hk
  -- per-step accumulator nonsingularity + point value + accumulated full `GateStep`
  have key : ∀ k, k ≤ m → ∃ hk : c.Nonsingular (accX g k) (accY g k),
      Point.some _ _ hk = gateLadder g (5 * k) • T ∧ (∀ i, i < k → GateStep c (g i)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨hP0ns, ?_, ?_⟩
      · change Point.some (g 0).x0 (g 0).y0 hP0ns = gateLadder g (5 * 0) • T
        rw [hP0]; simp only [Nat.mul_zero, gateLadder_zero]
      · intro i hi; omega
    | succ j ih =>
      intro hj1
      have hj' : j < m := by omega
      obtain ⟨hk, hPk, hGSk⟩ := ih (by omega)
      -- transport the base nonsingularity to row `j`
      obtain ⟨hbx, hby⟩ := hbase j hj'
      have hTns_j : c.Nonsingular (g j).xT (g j).yT := by rw [hbx, hby]; exact hTns
      have hTeq_j : T = Point.some _ _ hTns_j := by
        rw [hTeq]; exact some_congr hTns hTns_j hbx.symm hby.symm
      -- transport the threaded input accumulator to row `j`'s input column
      obtain ⟨hx0, hy0⟩ := haccP j hj'
      have ha0ns_j : c.Nonsingular (g j).x0 (g j).y0 := by rw [hx0, hy0]; exact hk
      have ha0_j : Point.some _ _ ha0ns_j = gateLadder g (5 * j) • T := by
        rw [some_congr ha0ns_j hk hx0 hy0]; exact hPk
      obtain ⟨nd, a1, a2, a3, a4, a5, ha5eq⟩ :=
        gate_block_full c g j h2 hTne hTns_j hTeq_j ha0ns_j (hholds j hj') ha0_j hodd
          (fun ℓ _ => hND (5 * j + ℓ) (by omega))
      -- the full per-row `GateStep` bundle at row `j`
      have hGSj : GateStep c (g j) :=
        ⟨ha0ns_j, a1, a2, a3, a4, a5, hTns_j, hholds j hj',
          nd.x0, nd.x1, nd.x2, nd.x3, nd.x4, nd.t0, nd.t1, nd.t2, nd.t3, nd.t4⟩
      -- `accX g (j+1) = (g j).x5` and `gateLadder g (5*(j+1)) = gateLadder g (5*j+5)` defeq
      refine ⟨a5, ?_, ?_⟩
      · rw [show 5 * (j + 1) = 5 * j + 5 from by ring]; exact ha5eq
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact hGSk i h
        · subst h; exact hGSj
  choose kf hkf using key
  -- kf : ∀ k, k ≤ m → c.Nonsingular (accX g k) (accY g k)
  -- hkf k hk : Point.some _ _ (kf k hk) = gateLadder g (5*k) • T ∧ (∀ i < k, GateStep c (g i))
  have gs := (hkf m le_rfl).2
  refine ⟨gs, fun k => if hk : k ≤ m then Point.some _ _ (kf k hk) else 0, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact hTeq.trans (some_congr hTns (gs i hi).hT (hbase i hi).1.symm (hbase i hi).2.symm)
  · intro i hi
    simp only [dif_pos (le_of_lt hi)]
    exact some_congr (kf i (le_of_lt hi)) (gs i hi).a0 (haccP i hi).1.symm (haccP i hi).2.symm
  · intro i hi
    simp only [dif_pos (Nat.succ_le_of_lt hi)]
    exact some_congr (kf (i + 1) (Nat.succ_le_of_lt hi)) (gs i hi).a5 rfl rfl
  · simp only [dif_pos (Nat.zero_le m)]
    rw [(hkf 0 (Nat.zero_le m)).1]; simp only [Nat.mul_zero, gateLadder_zero]

/-- **VarBaseMul correctness and soundness via the forbidden band.** For any witness satisfying the
    gate constraints (`Holds` per row) at the real init `P₀ = 2·T`, in the one-wrap regime, if the
    ladder top `s` avoids the forbidden band `forbiddenValues order`, the `m` rows compute the final
    accumulator `= s·T` and every row is `NonDegen`. The prover supplies only `Holds`, base,
    threading, and the initial accumulator; `gate_chain_produce` derives the accumulator
    nonsingularity. -/
theorem varBaseMul_forbidden_correct (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (m : ℕ) (g : ℕ → Witness F) (T : c.Point) (s : ℤ) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : c.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : c.Nonsingular (g 0).x0 (g 0).y0) (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    (hreg₁ : 2 ^ (5 * m - 1) < c.order) (hreg₂ : c.order < 2 ^ (5 * m))
    (hq4 : c.order % 4 = 1)
    (hs : s = gateLadder g (5 * m)) (hnf : s ∉ forbiddenValues c.order) :
    ∃ hfin : c.Nonsingular (accX g m) (accY g m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (g i) := by
  have hnf' : ∀ t ∈ Ladder.forbiddenResidues, ¬ (c.order : ℤ) ∣ (gateLadder g (5 * m) - t) := by
    intro t ht hdvd; exact hnf ⟨t, ht, by rw [hs]; exact hdvd⟩
  exact gate_chain_produce c m g T s hTne hholds hTns hTeq hbase hthread hP0ns hP0 h2 hodd
    (Ladder.ladder_nondegen_tight c.order (5 * m) c.order_prime hq4 hreg₁ hreg₂
      (gateLadder g) (gateBitSign g) (gateLadder_zero g) (fun j _ => gateBitSign_eq g j)
      (fun j _ => gateLadder_succ g j) hnf') hs

/-- **VarBaseMul correctness and soundness in the sub-wrap regime — no forbidden check.** When
    `3·2^(5m) ≤ order` the whole ladder fits below the order, so every row is `NonDegen`
    unconditionally. The prover supplies only `Holds`, base, threading, and the initial
    accumulator. -/
theorem varBaseMul_subwrap_correct (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (m : ℕ) (g : ℕ → Witness F) (T : c.Point) (s : ℤ) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : c.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : c.Nonsingular (g 0).x0 (g 0).y0) (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    (hsub : 3 * 2 ^ (5 * m) ≤ c.order) (hs : s = gateLadder g (5 * m)) :
    ∃ hfin : c.Nonsingular (accX g m) (accY g m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (g i) :=
  gate_chain_produce c m g T s hTne hholds hTns hTeq hbase hthread hP0ns hP0 h2 hodd
    (Ladder.ladder_subwrap_nondegen c.order (5 * m) hsub
      (gateLadder g) (gateBitSign g) (gateLadder_zero g) (fun j _ => gateBitSign_eq g j)
      (fun j _ => gateLadder_succ g j)) hs

end Kimchi.Circuit.VarBaseMul
