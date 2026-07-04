import Kimchi.Quotient.Pinning
import Kimchi.Quotient.Aggregate
import Kimchi.Quotient.AddComplete
import Kimchi.Quotient.VarBaseMul
import Kimchi.Quotient.EndoMul

/-!
# The quotient-argument soundness

Archon-original. The headline of the commitment-free quotient argument: it composes the
ζ-pinning corollary (`Kimchi.Quotient.zH_dvd_of_evals`, `Kimchi/Quotient/Pinning.lean`), the
α-separation lemma (`Kimchi.Quotient.dvd_separation`, `Kimchi/Quotient/Aggregate.lean`) and
each gate's selector-gated lift (`Gate.<G>` `rowsSel_iff_dvd`) into a single statement per
gate — "if the aggregated eval-check passes at enough distinct `ζ` over enough distinct `α`,
then every selector-active row of the gate satisfies its `Gate.<G>.Holds`".

It is entirely **commitment-free**: the "enough distinct challenges" premises are ordinary
injectivity hypotheses on the evaluation nodes `ζ : Fin N → F` and the aggregation challenges
`α : Fin k → F`, and the degree accounting is kept abstract through a single bound `D`. There
is no group, no SRS, no Fiat–Shamir.

No gate formula is restated anywhere in this file — the per-gate soundness only reuses the
read-only `Gate.<G>.constraints` applied to the gate's poly-witness together with that gate's
`rowsSel_iff_dvd`. The EC meaning is obtained downstream (a later wave) by citing the
read-only `Gate.<G>.sound` on the selected rows.

## Contents

* `dvd_of_evalCheck` — the composed pinning→separation engine, stated over an abstract family
  of constraint polynomials with no gate content.
* `AddComplete.soundness` / `VarBaseMul.soundness` / `EndoMul.soundness` — the per-gate
  soundness statements, pure instantiations of the engine against each gate's selector-gated
  lift.

Source of truth: `blueprint/src/chapters/Kimchi_Quotient_Soundness.tex`.
-/

namespace Kimchi.Quotient

open Polynomial

/-! ## The composed pinning–separation engine -/

/-- **Divisibility from the aggregated eval-check.** Fix a primitive `n`-th root `ω`, an
injective node vector `ζ : Fin N → F`, an injective challenge vector `α : Fin k → F`, and two
families `E, t : Fin k → F[X]`. Under the abstract degree bound `D < N` on the aggregate and
on `t s · Z_H`, if the aggregated eval-check
`(aggregate (α s) E)(ζ p) = (t s · Z_H)(ζ p)` holds for every challenge `s` and node `p`, then
`Z_H ∣ E c` for every constraint index `c`.

Proof (later wave): for each `s`, `zH_dvd_of_evals` pins `Z_H ∣ aggregate (α s) E`; feeding
this to `dvd_separation` across the `k` distinct challenges yields `Z_H ∣ E c`. -/
theorem dvd_of_evalCheck {F : Type*} [Field F] {n k N : ℕ} {ω : F}
    (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin k → F) (hα : Function.Injective α)
    (E t : Fin k → Polynomial F) (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) E).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s : Fin k, ∀ p : Fin N,
        (aggregate (α s) E).eval (ζ p) = (t s * zH F n).eval (ζ p)) :
    ∀ c, zH F n ∣ E c :=
  dvd_separation hω hn α hα E
    (fun s => zH_dvd_of_evals hω hn ζ hζ (aggregate (α s) E) (t s) D
      (hCdeg s) (htdeg s) hD (hcheck s))

end Kimchi.Quotient

/-! ## Per-gate soundness -/

namespace Kimchi.Quotient.AddComplete

open Polynomial Kimchi.Quotient WeierstrassCurve.Affine

/-- **CompleteAdd quotient soundness.** With the abstract quotient-argument hypotheses over the
selector-gated family `c ↦ (columnPoly ω sel) * (constraints (polyWitness ω wTab)).get c`, every
selector-active row satisfies the CompleteAdd gate predicate.

Proof (later wave): apply `dvd_of_evalCheck` to the gated family to obtain
`∀ c, zH ∣ (columnPoly ω sel) * (constraints …).get c`; convert the `Fin length` indexing to
`∈ constraints …` membership and feed the CompleteAdd `rowsSel_iff_dvd`. -/
theorem soundness {F : Type*} [Field F] [DecidableEq F] {n N : ℕ} {ω : F}
    (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (wTab : Fin n → Fin 15 → F) (sel : Fin n → F) (hsel : ∀ i, sel i = 0 ∨ sel i = 1)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (Gate.AddComplete.constraints (polyWitness ω wTab)).length → F)
    (hα : Function.Injective α)
    (t : Fin (Gate.AddComplete.constraints (polyWitness ω wTab)).length → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (fun c => columnPoly ω sel *
        (Gate.AddComplete.constraints (polyWitness ω wTab)).get c)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (fun c => columnPoly ω sel *
        (Gate.AddComplete.constraints (polyWitness ω wTab)).get c)).eval (ζ p)
        = (t s * zH F n).eval (ζ p)) :
    ∀ i, sel i = 1 → Gate.AddComplete.Holds (rowWitness wTab i) := by
  have hdvd := dvd_of_evalCheck hω hn ζ hζ α hα
    (fun c => columnPoly ω sel * (Gate.AddComplete.constraints (polyWitness ω wTab)).get c)
    t D hD hCdeg htdeg hcheck
  apply (rowsSel_iff_dvd hω hn wTab sel hsel).mp
  intro E hE
  obtain ⟨c, rfl⟩ := List.mem_iff_get.mp hE
  exact hdvd c

/-! ## The EC meaning -/

/-- **CompleteAdd EC soundness.** The thin wrapper landing the group-law meaning: on top of the
`Holds`-level `soundness` hypotheses, fix a short-Weierstrass curve `W` and, for every
selector-active row, the two input-point nonsingularity premises, `y₁ ≠ 0` and `2 ≠ 0`. Then each
active row is exactly the incomplete-addition disjunction of `Gate.AddComplete.sound`.

Proof: fix a selected row `i`; the `Holds`-level `soundness` supplies
`Gate.AddComplete.Holds (rowWitness wTab i)`, fed with the per-row curve premises to the read-only
`Gate.AddComplete.sound`. -/
theorem soundness_point {F : Type*} [Field F] [DecidableEq F] {n N : ℕ} {ω : F}
    (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (wTab : Fin n → Fin 15 → F) (sel : Fin n → F) (hsel : ∀ i, sel i = 0 ∨ sel i = 1)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (Gate.AddComplete.constraints (polyWitness ω wTab)).length → F)
    (hα : Function.Injective α)
    (t : Fin (Gate.AddComplete.constraints (polyWitness ω wTab)).length → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (fun c => columnPoly ω sel *
        (Gate.AddComplete.constraints (polyWitness ω wTab)).get c)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (fun c => columnPoly ω sel *
        (Gate.AddComplete.constraints (polyWitness ω wTab)).get c)).eval (ζ p)
        = (t s * zH F n).eval (ζ p))
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (h1 : ∀ i, sel i = 1 → W.Nonsingular (rowWitness wTab i).x1 (rowWitness wTab i).y1)
    (h2 : ∀ i, sel i = 1 → W.Nonsingular (rowWitness wTab i).x2 (rowWitness wTab i).y2)
    (hy1 : ∀ i, sel i = 1 → (rowWitness wTab i).y1 ≠ 0) (htwo : (2 : F) ≠ 0) :
    ∀ i (hi : sel i = 1),
      ((rowWitness wTab i).inf = 1 ∧
          Point.some _ _ (h1 i hi) + Point.some _ _ (h2 i hi) = 0)
        ∨ ((rowWitness wTab i).inf = 0 ∧
            ∃ h3 : W.Nonsingular (rowWitness wTab i).x3 (rowWitness wTab i).y3,
              Point.some _ _ (h1 i hi) + Point.some _ _ (h2 i hi) = Point.some _ _ h3) := by
  intro i hi
  exact Gate.AddComplete.sound W ha (rowWitness wTab i) (h1 i hi) (h2 i hi)
    (soundness hω hn wTab sel hsel ζ hζ α hα t D hD hCdeg htdeg hcheck i hi) (hy1 i hi) htwo

end Kimchi.Quotient.AddComplete

namespace Kimchi.Quotient.VarBaseMul

open Polynomial Kimchi.Quotient WeierstrassCurve.Affine

/-- **VarBaseMul quotient soundness.** Same shape as `AddComplete.soundness` for the two-row
VarBaseMul gate (`[NeZero n]` for the cyclic successor; the poly-witness next-row cells go
through `shift`). Every selector-active row satisfies the VarBaseMul gate predicate.

Proof (later wave): `dvd_of_evalCheck` on the gated family, then the VarBaseMul
`rowsSel_iff_dvd`. -/
theorem soundness {F : Type*} [Field F] [DecidableEq F] {n N : ℕ} [NeZero n] {ω : F}
    (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (wTab : Fin n → Fin 15 → F) (sel : Fin n → F) (hsel : ∀ i, sel i = 0 ∨ sel i = 1)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (Gate.VarBaseMul.constraints (polyWitness ω wTab)).length → F)
    (hα : Function.Injective α)
    (t : Fin (Gate.VarBaseMul.constraints (polyWitness ω wTab)).length → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (fun c => columnPoly ω sel *
        (Gate.VarBaseMul.constraints (polyWitness ω wTab)).get c)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (fun c => columnPoly ω sel *
        (Gate.VarBaseMul.constraints (polyWitness ω wTab)).get c)).eval (ζ p)
        = (t s * zH F n).eval (ζ p)) :
    ∀ i, sel i = 1 → Gate.VarBaseMul.Holds (rowWitness wTab i) := by
  have hdvd := dvd_of_evalCheck hω hn ζ hζ α hα
    (fun c => columnPoly ω sel * (Gate.VarBaseMul.constraints (polyWitness ω wTab)).get c)
    t D hD hCdeg htdeg hcheck
  apply (rowsSel_iff_dvd hω hn wTab sel hsel).mp
  intro E hE
  obtain ⟨c, rfl⟩ := List.mem_iff_get.mp hE
  exact hdvd c

/-! ## The EC meaning -/

/-- **VarBaseMul EC soundness.** The thin wrapper landing the signed scalar-multiplication step: on
top of the `Holds`-level `soundness` hypotheses, fix a short-Weierstrass curve `W`
(`a₁ = a₂ = a₃ = 0`) and, for every selector-active row, the seven ladder/base-point nonsingularity
premises and the ten non-degeneracy premises of `Gate.VarBaseMul.sound`. Then each active row
computes `P₅ = 32·P₀ + c·T` for an integer `c` with `(c:F) = 2·n' − 64·n − 31` and `|c| ≤ 31`.

Proof: fix a selected row `i`; the `Holds`-level `soundness` supplies
`Gate.VarBaseMul.Holds (rowWitness wTab i)`, fed with the per-row premises to the read-only
`Gate.VarBaseMul.sound`. -/
theorem soundness_point {F : Type*} [Field F] [DecidableEq F] {n N : ℕ} [NeZero n] {ω : F}
    (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (wTab : Fin n → Fin 15 → F) (sel : Fin n → F) (hsel : ∀ i, sel i = 0 ∨ sel i = 1)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (Gate.VarBaseMul.constraints (polyWitness ω wTab)).length → F)
    (hα : Function.Injective α)
    (t : Fin (Gate.VarBaseMul.constraints (polyWitness ω wTab)).length → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (fun c => columnPoly ω sel *
        (Gate.VarBaseMul.constraints (polyWitness ω wTab)).get c)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (fun c => columnPoly ω sel *
        (Gate.VarBaseMul.constraints (polyWitness ω wTab)).get c)).eval (ζ p)
        = (t s * zH F n).eval (ζ p))
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (h0 : ∀ i, sel i = 1 → W.Nonsingular (rowWitness wTab i).x0 (rowWitness wTab i).y0)
    (h1 : ∀ i, sel i = 1 → W.Nonsingular (rowWitness wTab i).x1 (rowWitness wTab i).y1)
    (h2 : ∀ i, sel i = 1 → W.Nonsingular (rowWitness wTab i).x2 (rowWitness wTab i).y2)
    (h3 : ∀ i, sel i = 1 → W.Nonsingular (rowWitness wTab i).x3 (rowWitness wTab i).y3)
    (h4 : ∀ i, sel i = 1 → W.Nonsingular (rowWitness wTab i).x4 (rowWitness wTab i).y4)
    (h5 : ∀ i, sel i = 1 → W.Nonsingular (rowWitness wTab i).x5 (rowWitness wTab i).y5)
    (hT : ∀ i, sel i = 1 → W.Nonsingular (rowWitness wTab i).xT (rowWitness wTab i).yT)
    (hxne0 : ∀ i, sel i = 1 → (rowWitness wTab i).x0 ≠ (rowWitness wTab i).xT)
    (hxne1 : ∀ i, sel i = 1 → (rowWitness wTab i).x1 ≠ (rowWitness wTab i).xT)
    (hxne2 : ∀ i, sel i = 1 → (rowWitness wTab i).x2 ≠ (rowWitness wTab i).xT)
    (hxne3 : ∀ i, sel i = 1 → (rowWitness wTab i).x3 ≠ (rowWitness wTab i).xT)
    (hxne4 : ∀ i, sel i = 1 → (rowWitness wTab i).x4 ≠ (rowWitness wTab i).xT)
    (htne0 : ∀ i, sel i = 1 →
        2 * (rowWitness wTab i).x0 + (rowWitness wTab i).xT
          - (rowWitness wTab i).s0 * (rowWitness wTab i).s0 ≠ 0)
    (htne1 : ∀ i, sel i = 1 →
        2 * (rowWitness wTab i).x1 + (rowWitness wTab i).xT
          - (rowWitness wTab i).s1 * (rowWitness wTab i).s1 ≠ 0)
    (htne2 : ∀ i, sel i = 1 →
        2 * (rowWitness wTab i).x2 + (rowWitness wTab i).xT
          - (rowWitness wTab i).s2 * (rowWitness wTab i).s2 ≠ 0)
    (htne3 : ∀ i, sel i = 1 →
        2 * (rowWitness wTab i).x3 + (rowWitness wTab i).xT
          - (rowWitness wTab i).s3 * (rowWitness wTab i).s3 ≠ 0)
    (htne4 : ∀ i, sel i = 1 →
        2 * (rowWitness wTab i).x4 + (rowWitness wTab i).xT
          - (rowWitness wTab i).s4 * (rowWitness wTab i).s4 ≠ 0) :
    ∀ i (hi : sel i = 1),
      ∃ c : ℤ, Point.some _ _ (h5 i hi)
          = (32 : ℤ) • Point.some _ _ (h0 i hi) + c • Point.some _ _ (hT i hi)
        ∧ (c : F) = 2 * (rowWitness wTab i).nPrime - 64 * (rowWitness wTab i).n - 31
        ∧ c.natAbs ≤ 31 := by
  intro i hi
  exact Gate.VarBaseMul.sound W ha (rowWitness wTab i) (h0 i hi) (h1 i hi) (h2 i hi) (h3 i hi)
    (h4 i hi) (h5 i hi) (hT i hi) (hxne0 i hi) (hxne1 i hi) (hxne2 i hi) (hxne3 i hi) (hxne4 i hi)
    (htne0 i hi) (htne1 i hi) (htne2 i hi) (htne3 i hi) (htne4 i hi)
    (soundness hω hn wTab sel hsel ζ hζ α hα t D hD hCdeg htdeg hcheck i hi)

end Kimchi.Quotient.VarBaseMul

namespace Kimchi.Quotient.EndoMul

open Polynomial Kimchi.Quotient WeierstrassCurve.Affine

/-- **EndoMul quotient soundness.** Same shape as `AddComplete.soundness` for the two-row
EndoMul gate, with an extra endomorphism constant `endo : F` (the polynomial side uses
`C endo`, the row side `endo`). Every selector-active row satisfies the EndoMul gate predicate.

Proof (later wave): `dvd_of_evalCheck` on the gated family, then the EndoMul
`rowsSel_iff_dvd`. -/
theorem soundness {F : Type*} [Field F] [DecidableEq F] {n N : ℕ} [NeZero n] {ω : F}
    (endo : F) (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (wTab : Fin n → Fin 15 → F) (sel : Fin n → F) (hsel : ∀ i, sel i = 0 ∨ sel i = 1)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (Gate.EndoMul.constraints (C endo) (polyWitness ω wTab)).length → F)
    (hα : Function.Injective α)
    (t : Fin (Gate.EndoMul.constraints (C endo) (polyWitness ω wTab)).length → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (fun c => columnPoly ω sel *
        (Gate.EndoMul.constraints (C endo) (polyWitness ω wTab)).get c)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (fun c => columnPoly ω sel *
        (Gate.EndoMul.constraints (C endo) (polyWitness ω wTab)).get c)).eval (ζ p)
        = (t s * zH F n).eval (ζ p)) :
    ∀ i, sel i = 1 → Gate.EndoMul.Holds endo (rowWitness wTab i) := by
  have hdvd := dvd_of_evalCheck hω hn ζ hζ α hα
    (fun c => columnPoly ω sel *
      (Gate.EndoMul.constraints (C endo) (polyWitness ω wTab)).get c)
    t D hD hCdeg htdeg hcheck
  apply (rowsSel_iff_dvd endo hω hn wTab sel hsel).mp
  intro E hE
  obtain ⟨c, rfl⟩ := List.mem_iff_get.mp hE
  exact hdvd c

/-! ## The EC meaning -/

/-- **EndoMul EC soundness.** The thin wrapper landing the GLV/eigenvalue step: on top of the
`Holds`-level `soundness` hypotheses, fix a short-Weierstrass curve `W` (`a₁ = a₂ = a₃ = 0`) and,
for every selector-active row, the seven nonsingularity premises and four non-degeneracy premises
of `Gate.EndoMul.sound`. Then each active row computes `P_S = 4·P_P + c₁·T + c₂·φ(T)` for integers
`c₁, c₂`.

Proof: fix a selected row `i`; the `Holds`-level `soundness` supplies
`Gate.EndoMul.Holds endo (rowWitness wTab i)`, fed with the per-row premises to the read-only
`Gate.EndoMul.sound`. -/
theorem soundness_point {F : Type*} [Field F] [DecidableEq F] {n N : ℕ} [NeZero n] {ω : F}
    (endo : F) (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (wTab : Fin n → Fin 15 → F) (sel : Fin n → F) (hsel : ∀ i, sel i = 0 ∨ sel i = 1)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (Gate.EndoMul.constraints (C endo) (polyWitness ω wTab)).length → F)
    (hα : Function.Injective α)
    (t : Fin (Gate.EndoMul.constraints (C endo) (polyWitness ω wTab)).length → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (fun c => columnPoly ω sel *
        (Gate.EndoMul.constraints (C endo) (polyWitness ω wTab)).get c)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (fun c => columnPoly ω sel *
        (Gate.EndoMul.constraints (C endo) (polyWitness ω wTab)).get c)).eval (ζ p)
        = (t s * zH F n).eval (ζ p))
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (hT : ∀ i, sel i = 1 → W.Nonsingular (rowWitness wTab i).xT (rowWitness wTab i).yT)
    (hφT : ∀ i, sel i = 1 → W.Nonsingular (endo * (rowWitness wTab i).xT) (rowWitness wTab i).yT)
    (hP : ∀ i, sel i = 1 → W.Nonsingular (rowWitness wTab i).xP (rowWitness wTab i).yP)
    (hR : ∀ i, sel i = 1 → W.Nonsingular (rowWitness wTab i).xR (rowWitness wTab i).yR)
    (hS : ∀ i, sel i = 1 → W.Nonsingular (rowWitness wTab i).xS (rowWitness wTab i).yS)
    (hQ1 : ∀ i, sel i = 1 →
        W.Nonsingular ((1 + (endo - 1) * (rowWitness wTab i).b1) * (rowWitness wTab i).xT)
          ((2 * (rowWitness wTab i).b2 - 1) * (rowWitness wTab i).yT))
    (hQ2 : ∀ i, sel i = 1 →
        W.Nonsingular ((1 + (endo - 1) * (rowWitness wTab i).b3) * (rowWitness wTab i).xT)
          ((2 * (rowWitness wTab i).b4 - 1) * (rowWitness wTab i).yT))
    (hxne1 : ∀ i, sel i = 1 →
        (rowWitness wTab i).xP ≠ (1 + (endo - 1) * (rowWitness wTab i).b1) * (rowWitness wTab i).xT)
    (htne1 : ∀ i, sel i = 1 →
        2 * (rowWitness wTab i).xP - (rowWitness wTab i).s1 ^ 2
          + (1 + (endo - 1) * (rowWitness wTab i).b1) * (rowWitness wTab i).xT ≠ 0)
    (hxne2 : ∀ i, sel i = 1 →
        (rowWitness wTab i).xR ≠ (1 + (endo - 1) * (rowWitness wTab i).b3) * (rowWitness wTab i).xT)
    (htne2 : ∀ i, sel i = 1 →
        2 * (rowWitness wTab i).xR - (rowWitness wTab i).s3 ^ 2
          + (1 + (endo - 1) * (rowWitness wTab i).b3) * (rowWitness wTab i).xT ≠ 0) :
    ∀ i (hi : sel i = 1),
      ∃ c1 c2 : ℤ, Point.some _ _ (hS i hi)
        = (4 : ℤ) • Point.some _ _ (hP i hi) + c1 • Point.some _ _ (hT i hi)
          + c2 • Point.some _ _ (hφT i hi) := by
  intro i hi
  exact Gate.EndoMul.sound W ha endo (rowWitness wTab i)
    (soundness endo hω hn wTab sel hsel ζ hζ α hα t D hD hCdeg htdeg hcheck i hi)
    (hT i hi) (hφT i hi) (hP i hi) (hR i hi) (hS i hi) (hQ1 i hi) (hQ2 i hi)
    (hxne1 i hi) (htne1 i hi) (hxne2 i hi) (htne2 i hi)

end Kimchi.Quotient.EndoMul
