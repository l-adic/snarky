import Kimchi.Quotient.Pinning
import Kimchi.Quotient.Aggregate
import Kimchi.Quotient.AddComplete
import Kimchi.Quotient.VarBaseMul
import Kimchi.Quotient.EndoMul

/-!
# The quotient-argument soundness

The headline of the commitment-free quotient argument: it composes the
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
`rowsSel_iff_dvd`. The EC meaning of the selected rows is obtained where it is consumed —
by citing `Gate.<G>.sound` — not restated here.

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

Proof: for each `s`, `zH_dvd_of_evals` pins `Z_H ∣ aggregate (α s) E`; feeding
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

Proof: apply `dvd_of_evalCheck` to the gated family to obtain
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


end Kimchi.Quotient.AddComplete

namespace Kimchi.Quotient.VarBaseMul

open Polynomial Kimchi.Quotient WeierstrassCurve.Affine

/-- **VarBaseMul quotient soundness.** Same shape as `AddComplete.soundness` for the two-row
VarBaseMul gate (`[NeZero n]` for the cyclic successor; the poly-witness next-row cells go
through `shift`). Every selector-active row satisfies the VarBaseMul gate predicate.

Proof: `dvd_of_evalCheck` on the gated family, then the VarBaseMul
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


end Kimchi.Quotient.VarBaseMul

namespace Kimchi.Quotient.EndoMul

open Polynomial Kimchi.Quotient WeierstrassCurve.Affine

/-- **EndoMul quotient soundness.** Same shape as `AddComplete.soundness` for the two-row
EndoMul gate, with an extra endomorphism constant `endo : F` (the polynomial side uses
`C endo`, the row side `endo`). Every selector-active row satisfies the EndoMul gate predicate.

Proof: `dvd_of_evalCheck` on the gated family, then the EndoMul
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


end Kimchi.Quotient.EndoMul
