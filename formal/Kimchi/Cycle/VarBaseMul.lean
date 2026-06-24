import Kimchi.Cycle.Axioms
import Kimchi.Circuit.VarBaseMul
import Kimchi.Shifted

/-!
# VarBaseMul over a `CMCurve` — the scalar in the scalar field

The single-field `Kimchi.Circuit.VarBaseMul.scalarMul_baseMul` says the gate computes
`P_m = [n]·T` for an integer `n`, and pins `(n : F)` to the register — but `F` there
is the *coordinate* field, conflating it with the scalar field. Over a `CMCurve`
(which carries the true scalar field as the group `order`) the order axiom
(`zsmul_mod`) makes the multiplier a genuine `ℤ/order` quantity (`varBaseMul_scalar`),
and the `Shifted_value` range bound discharges it to the *intended* scalar
(`varBaseMul_faithful`).
-/

namespace Kimchi.Cycle

open WeierstrassCurve.Affine Kimchi.Gate.VarBaseMul Kimchi.Circuit.VarBaseMul
  Kimchi.Shifted

variable {F : Type*} [Field F] [DecidableEq F]

/-- Scalar-field invariance: on a `CMCurve`, scalar multiplication of a point depends
    only on the scalar `mod` the group order. The first real consequence of the order
    axiom for the gates — it is *why* the gate's integer multiplier is a genuine
    `ℤ/order` (scalar-field) element rather than a coordinate-field one. -/
theorem zsmul_emod_eq (c : CMCurve F) {n s : ℤ} (P : c.W.Point)
    (h : n ≡ s [ZMOD (c.order : ℤ)]) :
    n • P = s • P := by
  rw [← zsmul_mod F c n P, ← zsmul_mod F c s P, h]

/-- VarBaseMul over a `CMCurve`, scalar in the scalar field. Instantiating the
    single-field `scalarMul_baseMul` at `c.W` exposes the integer multiplier `n`
    (`P_m = [n]·T`) and its register equation. Because `[n]·T` depends only on
    `n mod c.order` (`zsmul_emod_eq`), the multiplier is genuinely a SCALAR-field
    element: for ANY scalar `s ≡ n (mod order)` the gate computes `[s]·T`. The bridge
    from the in-circuit register to a specific such `s` (the `Shifted_value` decode)
    is the final `∀ s, …` conjunct, discharged by `varBaseMul_faithful`. -/
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
  obtain ⟨n, hn, hnf, _⟩ :=
    scalarMul_baseMul c.W c.short m g gs T N a P hT hin hout hregIn hregOut hP0
  exact ⟨n, hn, hnf, fun s hs => hn.trans (zsmul_emod_eq c T hs)⟩

/-- Faithful VarBaseMul. At the real init (`P₀ = [2]·T`, `N₀ = 0`) with the register
    `Shifted_value`-encoding a scalar `s` (`N_m = shiftType1 s`), the gate computes
    `P_m = [s]·T` — `s` the genuine SCALAR, not a coordinate-field element —
    **provided** the `Shifted_value` range bound `|n − s| < p` holds (`n` the gate's
    multiplier). `scalarMul_caller` gives `(n:F) = (s:F)`; `intCast_inj_of_sub_lt`
    upgrades it to `n = s` under the range, discharging `varBaseMul_scalar`'s open
    conjunct. The range bound itself follows from the 128-bit-challenge / 255-bit-field
    budget (here an explicit hypothesis). -/
theorem varBaseMul_faithful (c : CMCurve F) {p : ℕ} [CharP F p]
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → GateStep c.W (g i))
    (T : c.W.Point) (N : ℕ → F) (P : ℕ → c.W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some (gs i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some (gs i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some (gs i hi).a5)
    (hregIn : ∀ i, i < m → N i = (g i).n)
    (hregOut : ∀ i, i < m → N (i + 1) = (g i).nPrime)
    (hP0 : P 0 = (2 : ℤ) • T) (hN0 : N 0 = 0)
    (h2 : (2 : F) ≠ 0) (s : ℤ) (hNs : N m = shiftType1 (5 * m) (s : F)) :
    ∃ n : ℤ, P m = n • T ∧ (n : F) = (s : F)
      ∧ ((n - s).natAbs < p → P m = s • T) := by
  obtain ⟨n, hn, hnf, _⟩ := scalarMul_caller c.W c.short m g gs T N P
    hT hin hout hregIn hregOut hP0 hN0 (s : F) h2 hNs
  exact ⟨n, hn, hnf, fun hrange => by rw [hn, intCast_inj_of_sub_lt hnf hrange]⟩

/-- Faithful VarBaseMul, UNCONDITIONALLY, in the sub-width (128-bit-challenge)
    regime. Same setup as `varBaseMul_faithful`, but instead of *assuming* the
    `Shifted_value` range bound `|n − s| < p` we *derive* it from explicit budget
    hypotheses: the intended scalar fits in the `5m`-bit window
    (`|s| < 2·32^m`) and the field is large enough to separate the
    `5m+`-bit multiplier from it (`5·32^m ≤ p`). The gate's multiplier `n` is
    magnitude-bounded by `scalarMul_caller` (`|n| ≤ 3·32^m`, the `5m`-bit digit
    budget), so `|n − s| ≤ |n| + |s| < 3·32^m + 2·32^m = 5·32^m ≤ p`, and
    `intCast_inj_of_sub_lt` upgrades `(n:F) = (s:F)` to `n = s`. Hence the gate
    computes `P_m = [s]·T` for the genuine scalar `s` with no residual side
    condition. (`32^m = 2^(5m)`, so these are exactly the `5m`-bit budgets.) -/
theorem varBaseMul_faithful_unconditional (c : CMCurve F) {p : ℕ} [CharP F p]
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → GateStep c.W (g i))
    (T : c.W.Point) (N : ℕ → F) (P : ℕ → c.W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some (gs i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some (gs i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some (gs i hi).a5)
    (hregIn : ∀ i, i < m → N i = (g i).n)
    (hregOut : ∀ i, i < m → N (i + 1) = (g i).nPrime)
    (hP0 : P 0 = (2 : ℤ) • T) (hN0 : N 0 = 0)
    (h2 : (2 : F) ≠ 0) (s : ℤ) (hNs : N m = shiftType1 (5 * m) (s : F))
    (hs : s.natAbs < 2 * 32 ^ m) (hp : 5 * 32 ^ m ≤ p) :
    P m = s • T := by
  obtain ⟨n, hn, hnf, hnb⟩ := scalarMul_caller c.W c.short m g gs T N P
    hT hin hout hregIn hregOut hP0 hN0 (s : F) h2 hNs
  have hrange : (n - s).natAbs < p := by
    have htri : (n - s).natAbs ≤ n.natAbs + s.natAbs := Int.natAbs_sub_le n s
    omega
  rw [hn, intCast_inj_of_sub_lt hnf hrange]

end Kimchi.Cycle
