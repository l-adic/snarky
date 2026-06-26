import Kimchi.Gate.VarBaseMul
import Kimchi.Shifted

/-!
# The `VarBaseMul` circuit: variable-base scalar multiplication

Composition of `Kimchi.Gate.VarBaseMul` gates. A full scalar multiplication runs
many gates back to back, each consuming 5 bits: gate `i`'s output accumulator
feeds gate `i+1`'s input, and each gate's `gate_scalarMul_int` supplies the
per-step relation `P_{i+1} = 32·P_i + cᵢ·T`. Folding that recurrence over `m`
gates is pure group algebra.

## Main result

`scalarMul_shifted` — at the REAL circuit's parameters (accumulator initialized to
`[2]·T`, register started at `0`), `m` gates compute `P m = n·T` where the scalar
is the pickles Type1 unshift of the final register value,
`(n : F) = 2·(N m) + 2^(5m) + 1`. This `2·t + 2^numBits + 1` is verbatim
`Shifted_value.Type1.to_field`, and reproduces the reference value
`[1 + 2^numBits + 2·n_bits]·BasePoint` from proof-systems `varbasemul.rs`'s own
test — so the circuit computes `[s]·T` for the original scalar `s` once the
caller feeds the shifted scalar `t = shift(s)`.

The ladder under it:
* `scalarMul_baseMul` — accumulator a multiple of the base (`P 0 = a·T`): the
  output is a SINGLE scalar multiple `P m = n·T` (the `32^m·P₀` carry absorbed).
* `scalarMul` — general `P 0`: `P m = 32^m·P₀ + k·T`, `k` pinned to the register.

## Supporting development

`chain_scalarMul` / `chain_register` (the point- and register-level recurrence
folds), `GateStep` (the per-gate hypothesis bundle that `gate_scalarMul_int`
consumes), and `unshiftType1` / `shiftType1` / `unshiftType2` (the pickles shift).

## Correspondence to the PureScript circuit

The hypotheses are exactly the constraints `Snarky.Circuit.Kimchi.VarBaseMul`
emits (`packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/VarBaseMul.purs`):

* `P 0 = 2·T` ← `addFast CheckFinite base base` (acc := `[2]base`);
* `N 0 = 0` ← `nAccPrev: const_ zero`; per-bit `n' = 2·n + b` ←
  `foldl (\a b -> double a + b)`;
* `q_j = (xT, (2·b − 1)·yT)` ← `Q = (xBase, (2·b − 1)·yBase)` (`computeVbmChain`);
* `N m = shiftType1 s` (caller feeds the shift) ← `assertEqual_ nAcc t`.

So the theorems track the circuit's entry points:

* `scalarMul_caller`  ↔ `scaleFast1`  — `g, a ↦ [fromShifted a]·g` (Type1).
* `scalarMul_type2`   ↔ `scaleFast2`  — split `s = 2·sDiv2 + sOdd`, run VarBaseMul
  on `sDiv2`, then `if sOdd then g else g − base` (so `scaleFast2' ~ [s + 2^n]·g`).
* `scalarMul_shifted` ↔ the core `varBaseMul`, `[2·t + 2^n + 1]·g`.

This is an audit-level correspondence — the Lean model's hypotheses match the
PureScript constraints by inspection, not a mechanized PS→Lean extraction.
-/

namespace Kimchi.Circuit.VarBaseMul

open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine Kimchi.Shifted

variable {F : Type*} [Field F] [DecidableEq F]

/-- Chaining the per-gate relation `P_{i+1} = 32·P_i + cᵢ·T` over `m` gates gives
    the closed-form scalar multiple

        P_m = 32^m·P₀ + (∑_{i<m} 32^(m-1-i)·cᵢ)·T

    — i.e. `m` chained `VarBaseMul` gates compute variable-base scalar
    multiplication by the `5m`-bit scalar `k = ∑_{i<m} 32^(m-1-i)·cᵢ` (plus the
    carried `32^m·P₀`). The per-gate relation is supplied by `gate_scalarMul_int`
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

/-- The per-gate CONSTRAINT DATA that `gate_scalarMul_int` consumes: nonsingular
    accumulators `a0..a5`, signed targets `q0..q4`, and the 21 constraints `holds`.
    This is the prover's witness — an INPUT to the circuit, not derivable. -/
structure GateData (W : WeierstrassCurve.Affine F) (g : Witness F) : Prop where
  a0 : W.Nonsingular g.x0 g.y0
  a1 : W.Nonsingular g.x1 g.y1
  a2 : W.Nonsingular g.x2 g.y2
  a3 : W.Nonsingular g.x3 g.y3
  a4 : W.Nonsingular g.x4 g.y4
  a5 : W.Nonsingular g.x5 g.y5
  hT : W.Nonsingular g.xT g.yT
  q0 : W.Nonsingular g.xT ((2 * g.b0 - 1) * g.yT)
  q1 : W.Nonsingular g.xT ((2 * g.b1 - 1) * g.yT)
  q2 : W.Nonsingular g.xT ((2 * g.b2 - 1) * g.yT)
  q3 : W.Nonsingular g.xT ((2 * g.b3 - 1) * g.yT)
  q4 : W.Nonsingular g.xT ((2 * g.b4 - 1) * g.yT)
  holds : Holds g

/-- The per-gate NON-DEGENERACY side conditions: the additions are non-vertical
    (`xⱼ ≠ xT`) and the second additions are non-vertical (`tⱼ ≠ 0`). For ANY satisfying
    witness these are secured by the register field bound (`Soundness.varBaseMul_deployed_correct`
    via `Ladder.ladder_x_nondegen`), so no incomplete-addition step hits an exceptional case. -/
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

/-- A full per-gate step: the constraint `GateData` plus the `NonDegen` side
    conditions. (Both parents' fields are inherited via dot notation, so existing
    `gate_scalarMul_int` call sites are unaffected.) -/
structure GateStep (W : WeierstrassCurve.Affine F) (g : Witness F) : Prop
    extends GateData W g, NonDegen g

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
    `gate_scalarMul_int`. -/
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
    choose! c hc₁ hc₂ hc₃ using fun i hi => gate_scalarMul_int W ha (g i)
      (gs i hi).a0 (gs i hi).a1 (gs i hi).a2 (gs i hi).a3 (gs i hi).a4 (gs i hi).a5
      (gs i hi).hT (gs i hi).q0 (gs i hi).q1 (gs i hi).q2 (gs i hi).q3 (gs i hi).q4
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

/-! ## The caller's scalar: Type1 and the odd correction (Type2) -/

/-- The circuit computes `[s]·T` for the CALLER's scalar `s`. When the caller feeds
    the Type1 shift of `s` as the register (`N m = shiftType1 (5m) s` — what pickles
    `of_field` produces), the `m` gates compute `P m = n·T` with `(n : F) = s`:
    variable-base scalar multiplication by the original scalar `s`. -/
theorem scalarMul_caller
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → GateStep W (g i))
    (T : W.Point) (N : ℕ → F) (P : ℕ → W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).a5)
    (hregIn : ∀ i, i < m → N i = (g i).n)
    (hregOut : ∀ i, i < m → N (i + 1) = (g i).nPrime)
    (hP0 : P 0 = (2 : ℤ) • T) (hN0 : N 0 = 0)
    (s : F) (h2 : (2 : F) ≠ 0) (hNs : N m = shiftType1 (5 * m) s) :
    ∃ n : ℤ, P m = n • T ∧ (n : F) = s ∧ n.natAbs ≤ 3 * 32 ^ m := by
  obtain ⟨n, hn, hnf, hnb⟩ :=
    scalarMul_shifted W ha m g gs T N P hT hin hout hregIn hregOut hP0 hN0
  exact ⟨n, hn, by rw [hnf, hNs, unshiftType1_shiftType1 h2], hnb⟩

/-- Type2 scalar multiplication: split + the explicit low-bit correction. The
    `VarBaseMul` chain runs on the high part (register `N m = sHi`, giving
    `P m = [2·sHi + 2^(5m) + 1]·T`), then the circuit applies the final
    `if sOdd then h else h − T`. The corrected `result` is `n·T` with
    `(n : F) = unshiftType2 (5m) (N m) sOdd = 2·(N m) + sOdd + 2^(5m)` — the Type2
    scalar, in both bit cases. -/
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
    (sOdd : F) (result : W.Point)
    (hcorr : (sOdd = 1 ∧ result = P m) ∨ (sOdd = 0 ∧ result = P m - T)) :
    ∃ n : ℤ, result = n • T ∧ (n : F) = unshiftType2 (5 * m) (N m) sOdd := by
  obtain ⟨n, hn, hnf, _⟩ :=
    scalarMul_shifted W ha m g gs T N P hT hin hout hregIn hregOut hP0 hN0
  rcases hcorr with ⟨ho, hr⟩ | ⟨ho, hr⟩
  · refine ⟨n, by rw [hr, hn], ?_⟩
    rw [hnf, ho, unshiftType1, unshiftType2]; ring
  · refine ⟨n - 1, by rw [hr, hn, sub_smul, one_zsmul], ?_⟩
    push_cast
    rw [hnf, ho, unshiftType1, unshiftType2]; ring

/-! ## The circuit's correctness: it computes `[s]·T` for the caller's scalar `s`,
    given the per-gate `GateStep`s. Non-degeneracy is discharged from the field bound in
    `Soundness` (`varBaseMul_correct`); here it is a `GateStep` hypothesis. -/

/-- Given the per-gate `GateStep`s (constraints + non-degeneracy) and the sub-width
    budget, the gate computes `[s]·T` for the genuine scalar `s`. The cross-field range
    `|n − s| < p` is derived from the multiplier bound `|n| ≤ 3·32^m` (`scalarMul_caller`)
    and `|s| < 2·32^m`: `|n − s| < 5·32^m ≤ p`, so `intCast_inj_of_sub_lt` upgrades
    `(n:F) = (s:F)` to `n = s`. (`32^m = 2^(5m)`, the `5m`-bit budget.) -/
theorem varBaseMul_faithful_unconditional (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0) {p : ℕ} [CharP F p]
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → GateStep W (g i))
    (T : W.Point) (N : ℕ → F) (P : ℕ → W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).a5)
    (hregIn : ∀ i, i < m → N i = (g i).n)
    (hregOut : ∀ i, i < m → N (i + 1) = (g i).nPrime)
    (hP0 : P 0 = (2 : ℤ) • T) (hN0 : N 0 = 0)
    (h2 : (2 : F) ≠ 0) (s : ℤ) (hNs : N m = shiftType1 (5 * m) (s : F))
    (hs : s.natAbs < 2 * 32 ^ m) (hp : 5 * 32 ^ m ≤ p) :
    P m = s • T := by
  obtain ⟨n, hn, hnf, hnb⟩ := scalarMul_caller W ha m g gs T N P
    hT hin hout hregIn hregOut hP0 hN0 (s : F) h2 hNs
  have hrange : (n - s).natAbs < p := by
    have htri : (n - s).natAbs ≤ n.natAbs + s.natAbs := Int.natAbs_sub_le n s
    omega
  rw [hn, intCast_inj_of_sub_lt hnf hrange]

end Kimchi.Circuit.VarBaseMul
