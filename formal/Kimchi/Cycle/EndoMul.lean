import Kimchi.Cycle.VarBaseMul
import Kimchi.Cycle.Shifted
import Kimchi.Circuit.EndoMul

/-!
# Phase 3: EndoMul over a `CMCurve` — the eigenvalue from the curve

`endoMul_scalar` / `endoMul_toField` both take the eigenvalue `φ(T) = [λ]·T` as a
bare HYPOTHESIS. Over a `CMCurve` that hypothesis is exactly the `eigen` axiom — so
when the EndoMul rows run the curve's own endomorphism (`endo = c.beta`), the
eigenvalue is *supplied by the curve structure* rather than assumed, with `λ = c.lam`
its genuine scalar-field value. The resulting scalar acts in `ℤ/order` (`zsmul_emod_eq`).

This upgrades EndoMul's two headline results — `endoMul_scalar_cm` (single scalar
multiple) and `endoMul_toField_cm` (`P_m = [EndoScalar.toField]·T`) — to the two-field
model, leaving only the `toField`/range faithfulness (the EndoScalar analogue of
`varBaseMul_faithful`) and the cross-cycle reciprocity for Phase 4.
-/

namespace Kimchi.Cycle

open WeierstrassCurve.Affine Kimchi.Gate.EndoMul Kimchi.Circuit.EndoMul

variable {F : Type*} [Field F] [DecidableEq F]

/-- The eigenvalue relation `φ(T) = [λ]·T`, supplied by the curve's CM structure — the
    `eigen` axiom specialized to the base pair `T = (xT, yT)`, `φ(T) = (β·xT, yT)`. This
    is the `heig` hypothesis `endoMul_scalar`/`endoMul_toField` ask for, now a theorem. -/
theorem endoStep_eigen (c : CMCurve F) {xT yT : F}
    (hTbase : c.W.Nonsingular xT yT) (hφTbase : c.W.Nonsingular (c.beta * xT) yT) :
    Point.some _ _ hφTbase = c.lam • Point.some _ _ hTbase :=
  c.eigen hTbase hφTbase

/-- PHASE 3 — EndoMul over a `CMCurve`, eigenvalue from the curve. With the rows running
    the curve's endomorphism (`endo = c.beta`) and the base point `T = (xT, yT)`, the GLV
    eigenvalue collapse `P_m = 4^m·P₀ + [k]·T` holds with `λ = c.lam` taken from `eigen`
    (not hypothesized). The multiplier `k` is a genuine scalar-field element: for any
    `s ≡ k (mod order)` the result is the same (`zsmul_emod_eq`). -/
theorem endoMul_scalar_cm (c : CMCurve F)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → EndoStep c.W c.beta (g i))
    (P : ℕ → c.W.Point) (T φT : c.W.Point) {xT yT : F}
    (hTbase : c.W.Nonsingular xT yT) (hφTbase : c.W.Nonsingular (c.beta * xT) yT)
    (hTeq : T = Point.some _ _ hTbase) (hφTeq : φT = Point.some _ _ hφTbase)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hφT : ∀ i (hi : i < m), φT = Point.some _ _ (gs i hi).hφT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).hP)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).hS) :
    ∃ k : ℤ, P m = (4 : ℤ) ^ m • P 0 + k • T
      ∧ ∀ s : ℤ, k ≡ s [ZMOD (c.order : ℤ)] → P m = (4 : ℤ) ^ m • P 0 + s • T := by
  have heig : φT = c.lam • T := by rw [hTeq, hφTeq]; exact endoStep_eigen c hTbase hφTbase
  obtain ⟨k, hk⟩ := endoMul_scalar c.W c.short c.beta m g gs P T φT hT hφT hin hout c.lam heig
  exact ⟨k, hk, fun s hs => by rw [hk, zsmul_emod_eq c T hs]⟩

/-- PHASE 3 — EndoMul ∘ EndoScalar over a `CMCurve`, the top level with the eigenvalue
    from the curve. At the real init (`P₀ = 2·(T + φ(T))`) the rows produce `P_m = [s]·T`
    where `(s : F) = EndoScalar.toField (crumbList g m) c.lam` — EndoMul multiplies the
    base by exactly the scalar EndoScalar decodes, and the eigenvalue `λ = c.lam` is the
    curve's own (via `eigen`), NOT a free hypothesis. The remaining faithfulness — that
    `s mod order` is the intended scalar, via the `Shifted_value` range on `toField` — is
    the EndoScalar analogue of `varBaseMul_faithful` (Phase 4). -/
theorem endoMul_toField_cm (c : CMCurve F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → EndoStep c.W c.beta (g i))
    (P : ℕ → c.W.Point) (T φT : c.W.Point) {xT yT : F}
    (hTbase : c.W.Nonsingular xT yT) (hφTbase : c.W.Nonsingular (c.beta * xT) yT)
    (hTeq : T = Point.some _ _ hTbase) (hφTeq : φT = Point.some _ _ hφTbase)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hφT : ∀ i (hi : i < m), φT = Point.some _ _ (gs i hi).hφT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).hP)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).hS)
    (hP0 : P 0 = (2 : ℤ) • T + (2 : ℤ) • φT) :
    ∃ s : ℤ, P m = s • T
      ∧ (s : F) = Kimchi.Circuit.EndoScalar.toField (crumbList g m) (c.lam : F) := by
  have heig : φT = c.lam • T := by rw [hTeq, hφTeq]; exact endoStep_eigen c hTbase hφTbase
  exact endoMul_toField c.W c.short h2 h3 c.beta m g gs P T φT hT hφT hin hout hP0 c.lam heig

/-- PHASE 3 (faithful) — EndoMul ∘ EndoScalar computes `[σ]·T` for the genuine scalar.
    Given the intended scalar `σ : ℤ` that `toField` decodes (`(σ:F) = toField crumbs λ`,
    its coordinate-field representation), the gate's output `P_m = [s]·T` has `s = σ`
    once the `Shifted_value` range bounds `|s − σ| < p` — so `P_m = [σ]·T` for the honest
    integer scalar. The EndoScalar analogue of `varBaseMul_faithful`: `endoMul_toField_cm`
    gives `(s:F) = toField = (σ:F)`, and the cross-field coincidence (`intCast_inj_of_sub_lt`)
    upgrades it to `s = σ` under the range. With the eigenvalue from the curve, this closes
    Level-1 EndoMul — `[EndoScalar.toField]·T` with both the eigenvalue and the scalar
    honest, modulo the single explicit range hypothesis. -/
theorem endoMul_faithful (c : CMCurve F) {p : ℕ} [CharP F p]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → EndoStep c.W c.beta (g i))
    (P : ℕ → c.W.Point) (T φT : c.W.Point) {xT yT : F}
    (hTbase : c.W.Nonsingular xT yT) (hφTbase : c.W.Nonsingular (c.beta * xT) yT)
    (hTeq : T = Point.some _ _ hTbase) (hφTeq : φT = Point.some _ _ hφTbase)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hφT : ∀ i (hi : i < m), φT = Point.some _ _ (gs i hi).hφT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).hP)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).hS)
    (hP0 : P 0 = (2 : ℤ) • T + (2 : ℤ) • φT)
    (σ : ℤ) (hσ : (σ : F) = Kimchi.Circuit.EndoScalar.toField (crumbList g m) (c.lam : F)) :
    ∃ s : ℤ, P m = s • T
      ∧ (s : F) = Kimchi.Circuit.EndoScalar.toField (crumbList g m) (c.lam : F)
      ∧ ((s - σ).natAbs < p → P m = σ • T) := by
  obtain ⟨s, hPm, hs⟩ := endoMul_toField_cm c h2 h3 m g gs P T φT hTbase hφTbase
    hTeq hφTeq hT hφT hin hout hP0
  exact ⟨s, hPm, hs, fun hrange => by rw [hPm, intCast_inj_of_sub_lt (hs.trans hσ.symm) hrange]⟩

end Kimchi.Cycle
