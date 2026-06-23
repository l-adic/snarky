import Kimchi.Gate.VarBaseMul

/-!
# The `VarBaseMul` circuit: variable-base scalar multiplication

Composition of `Kimchi.Gate.VarBaseMul` gates. A full scalar multiplication runs
many gates back to back, each consuming 5 bits: gate `i`'s output accumulator
feeds gate `i+1`'s input, and each gate's `gate_scalarMul_int` supplies the
per-step relation `P_{i+1} = 32·P_i + cᵢ·T`. Folding that recurrence over `m`
gates is pure group algebra.

## Main result

`scalarMul` — `m` chained gates compute variable-base scalar multiplication:
`∃ k : ℤ, Pₘ = 32^m · P₀ + k · T`. It instantiates `chain_scalarMul` with the
per-gate relations from the gate's `gate_scalarMul_int`.

## Supporting development

`chain_scalarMul` (the abstract recurrence fold) and `GateStep` (the per-gate
hypothesis bundle that `gate_scalarMul_int` consumes).
-/

namespace Kimchi.Circuit.VarBaseMul

open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine

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

/-- The per-gate hypotheses `gate_scalarMul_int` needs, bundled: nonsingular
    accumulators `a0..a5` and signed targets `q0..q4`, the per-step
    non-degeneracy `x0..x4` (`xᵢ ≠ xT`) and `t0..t4` (`tᵢ ≠ 0`), and the 21
    constraints `holds`. (A `Prop`, so its fields are usable as proofs.) -/
structure GateStep (W : WeierstrassCurve.Affine F) (g : Witness F) : Prop where
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
  holds : Holds g

/-! ## Main theorem: variable-base scalar multiplication -/

/-- `m` chained `VarBaseMul` gates compute variable-base scalar
    multiplication. Given `m` valid gates `g i` over a shared target point `T`,
    whose accumulator points form a chain `P` (gate `i`'s input is `P i`, its
    output is `P (i+1)`, so consecutive gates are threaded), the final accumulator
    is `P m = 32^m·P₀ + k·T` for some integer scalar `k`. The proof applies the
    gate's `gate_scalarMul_int` to each gate for its per-step relation
    `P (i+1) = 32·P i + cᵢ·T`, then folds them with `chain_scalarMul`. -/
theorem scalarMul
    (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → GateStep W (g i))
    (P : ℕ → W.Point) (T : W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some (gs i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some (gs i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some (gs i hi).a5) :
    ∃ k : ℤ, P m = (32 : ℤ) ^ m • P 0 + k • T := by
  refine ⟨_, chain_scalarMul W m P T (fun i =>
    -- each gate's integer contribution, via `gate_scalarMul_int` (junk 0 past `m`)
    if hi : i < m then
      Classical.choose (gate_scalarMul_int W ha (g i)
        (gs i hi).a0 (gs i hi).a1 (gs i hi).a2 (gs i hi).a3 (gs i hi).a4 (gs i hi).a5
        (gs i hi).hT (gs i hi).q0 (gs i hi).q1 (gs i hi).q2 (gs i hi).q3 (gs i hi).q4
        (gs i hi).x0 (gs i hi).x1 (gs i hi).x2 (gs i hi).x3 (gs i hi).x4
        (gs i hi).t0 (gs i hi).t1 (gs i hi).t2 (gs i hi).t3 (gs i hi).t4 (gs i hi).holds)
    else 0) ?_⟩
  grind +qlia

end Kimchi.Circuit.VarBaseMul
