import Kimchi.Cycle.VarBaseMul

/-!
# Phase 2: the `Shifted_value` range bridge — faithful VarBaseMul

Phase 1 (`varBaseMul_scalar`) left a conjunct `∀ s, n ≡ s (mod order) → P_m = [s]·T`:
the gate computes `[s]·T` for any scalar congruent to its multiplier. Here we
discharge it for the *intended* scalar — the one the in-circuit register encodes via
`Shifted_value` (Type1: `N_m = shiftType1 s`, the existing single-field encoding).

The crux is the **cross-field coincidence** (`intCast_inj_of_sub_lt`): a
*coordinate*-field equation `(n:F) = (s:F)` only fixes `n mod p`, but once the
`Shifted_value` range bounds `|n − s| < p` it upgrades to honest integer equality
`n = s` — so the gate's multiplier *is* the encoded scalar, in both fields at once.
That range bound (`< min(p,q)`, from the 128/255-bit budget) is the property the
single-field model silently assumed; here it is an explicit hypothesis.
-/

namespace Kimchi.Cycle

open WeierstrassCurve.Affine Kimchi.Gate.VarBaseMul Kimchi.Circuit.VarBaseMul

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Cross-field coincidence (the range-bookkeeping core). In a field of
    characteristic `p`, two integers whose images agree and whose difference is
    smaller than `p` are equal. This is what turns a coordinate-field equation into
    an honest integer equality once the `Shifted_value` range bounds the gap — the
    base-field and scalar-field reductions then coincide. -/
theorem intCast_inj_of_sub_lt {p : ℕ} [CharP F p] {n s : ℤ}
    (h : (n : F) = (s : F)) (hlt : (n - s).natAbs < p) : n = s := by
  have hz : ((n - s : ℤ) : F) = 0 := by push_cast; rw [h]; ring
  have hdvd : (p : ℤ) ∣ (n - s) := (CharP.intCast_eq_zero_iff F p (n - s)).mp hz
  have h0 : n - s = 0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by rw [Int.natAbs_natCast]; exact hlt)
  omega

/-- PHASE 2 — faithful VarBaseMul. At the real init (`P₀ = [2]·T`, `N₀ = 0`) with the
    register `Shifted_value`-encoding a scalar `s` (`N_m = shiftType1 s`), the gate
    computes `P_m = [s]·T` — `s` the genuine SCALAR, not a coordinate-field element —
    **provided** the `Shifted_value` range bound `|n − s| < p` holds (`n` the gate's
    multiplier). `scalarMul_caller` gives `(n:F) = (s:F)`; the coincidence upgrades it
    to `n = s` under the range, discharging Phase 1's open conjunct. The range bound
    itself follows from the 128-bit-challenge / 255-bit-field budget (the last piece;
    here an explicit hypothesis). -/
theorem varBaseMul_faithful (c : CMCurve F) {p : ℕ} [CharP F p]
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → GateStep c.W (g i))
    (T : c.W.Point) (N : ℕ → F) (P : ℕ → c.W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).a5)
    (hregIn : ∀ i, i < m → N i = (g i).n)
    (hregOut : ∀ i, i < m → N (i + 1) = (g i).nPrime)
    (hP0 : P 0 = (2 : ℤ) • T) (hN0 : N 0 = 0)
    (h2 : (2 : F) ≠ 0) (s : ℤ) (hNs : N m = shiftType1 (5 * m) (s : F)) :
    ∃ n : ℤ, P m = n • T ∧ (n : F) = (s : F)
      ∧ ((n - s).natAbs < p → P m = s • T) := by
  obtain ⟨n, hn, hnf⟩ := scalarMul_caller c.W c.short m g gs T N P
    hT hin hout hregIn hregOut hP0 hN0 (s : F) h2 hNs
  exact ⟨n, hn, hnf, fun hrange => by rw [hn, intCast_inj_of_sub_lt hnf hrange]⟩

end Kimchi.Cycle
