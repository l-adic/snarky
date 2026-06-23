import Kimchi.Cycle.Axioms
import Kimchi.Circuit.VarBaseMul

/-!
# Phase 1: VarBaseMul over a `CMCurve` — the scalar in the scalar field

The single-field `Kimchi.Circuit.VarBaseMul.scalarMul_baseMul` says the gate computes
`P_m = [n]·T` for an integer `n`, and pins `(n : F)` to the register — but `F` there
is the *coordinate* field, conflating it with the scalar field. Here we re-state it
over a `CMCurve` (which carries the true scalar field as the group `order`), and use
the order axiom (`zsmul_mod`) to make the multiplier genuinely a `ℤ/order` quantity:
the gate computes `[s]·T` for any scalar `s ≡ n (mod order)`.

The map from the in-circuit register to a *specific* such `s` is the `Shifted_value`
encoding — Phase 2. It is the final `∀ s, n ≡ s → P_m = [s]·T` conjunct here, ready
to be discharged. See `formal/docs/cycle-formalization.md`.
-/

namespace Kimchi.Cycle

open WeierstrassCurve.Affine Kimchi.Gate.VarBaseMul Kimchi.Circuit.VarBaseMul

variable {F : Type*} [Field F] [DecidableEq F]

/-- Scalar-field invariance: on a `CMCurve`, scalar multiplication of a point depends
    only on the scalar `mod` the group order. The first real consequence of the order
    axiom for the gates — it is *why* the gate's integer multiplier is a genuine
    `ℤ/order` (scalar-field) element rather than a coordinate-field one. -/
theorem zsmul_emod_eq (c : CMCurve F) {n s : ℤ} (P : c.W.Point)
    (h : n ≡ s [ZMOD (c.order : ℤ)]) :
    n • P = s • P := by
  rw [← zsmul_mod F c n P, ← zsmul_mod F c s P, h]

/-- PHASE 1 — VarBaseMul over a `CMCurve`, scalar in the scalar field. Instantiating
    the single-field `scalarMul_baseMul` at `c.W` exposes the integer multiplier `n`
    (`P_m = [n]·T`) and its register equation. Because `[n]·T` depends only on
    `n mod c.order` (`zsmul_emod_eq`), the multiplier is genuinely a SCALAR-field
    element: for ANY scalar `s ≡ n (mod order)` the gate computes `[s]·T`. The bridge
    from the in-circuit register to a specific such `s` (the `Shifted_value` decode) is
    Phase 2; it is the final `∀ s, …` conjunct, ready to discharge. -/
theorem varBaseMul_scalar (c : CMCurve F)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → GateStep c.W (g i))
    (T : c.W.Point) (N : ℕ → F) (a : ℤ) (P : ℕ → c.W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some (gs i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some (gs i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some (gs i hi).a5)
    (hregIn : ∀ i, i < m → N i = (g i).n)
    (hregOut : ∀ i, i < m → N (i + 1) = (g i).nPrime)
    (hP0 : P 0 = a • T) :
    ∃ n : ℤ, P m = n • T
      ∧ (n : F) = (32 : F) ^ m * (a : F) + 2 * N m - 2 * (32 : F) ^ m * N 0 - ((32 : F) ^ m - 1)
      ∧ ∀ s : ℤ, n ≡ s [ZMOD (c.order : ℤ)] → P m = s • T := by
  obtain ⟨n, hn, hnf⟩ :=
    scalarMul_baseMul c.W c.short m g gs T N a P hT hin hout hregIn hregOut hP0
  exact ⟨n, hn, hnf, fun s hs => hn.trans (zsmul_emod_eq c T hs)⟩

end Kimchi.Cycle
