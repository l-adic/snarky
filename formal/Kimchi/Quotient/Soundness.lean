import Kimchi.Quotient.Aggregate
import Kimchi.Quotient.AddComplete
import Kimchi.Quotient.VarBaseMul
import Kimchi.Quotient.EndoMul

/-!
# The quotient-argument soundness

The headline of the commitment-free quotient argument, one statement per gate: "if the
aggregated eval-check passes at enough distinct `ζ` over enough distinct `α`, then every
selector-active row of the gate satisfies its `Gate.<G>.Holds`". Each is an immediate
specialization of the engine `Kimchi.Quotient.Argument.soundness`
(`Kimchi/Quotient/Lift.lean`) at that gate's `argument` instance.

It is entirely **commitment-free**: the "enough distinct challenges" premises are ordinary
injectivity hypotheses on the evaluation nodes `ζ : Fin N → F` and the aggregation challenges
`α : Fin k → F`, and the degree accounting is kept abstract through a single bound `D`. There
is no group, no SRS, no Fiat–Shamir.

No gate formula is restated anywhere in this file — the per-gate soundness only reuses the
read-only `Gate.<G>.constraints` applied to the gate's poly-witness together with that gate's
`argument` instance. The EC meaning of the selected rows is obtained where it is consumed —
by citing `Gate.<G>.sound` — not restated here.

## Contents

* `AddComplete.soundness` / `VarBaseMul.soundness` / `EndoMul.soundness` — the per-gate
  soundness statements, pure specializations of `Argument.soundness` at each gate's
  `argument` instance.

Source of truth: `blueprint/src/chapters/Kimchi_Quotient_Soundness.tex`.
-/

/-! ## Per-gate soundness -/

namespace Kimchi.Quotient.AddComplete

open Polynomial Kimchi.Quotient WeierstrassCurve.Affine

/-- **CompleteAdd quotient soundness.** With the abstract quotient-argument hypotheses over the
selector-gated family `c ↦ (columnPoly ω sel) * (constraints (polyWitness ω wTab)).get c`, every
selector-active row satisfies the CompleteAdd gate predicate.

Proof: specialization of `Argument.soundness` at the instance `argument`; single-row, so
`qTab := wTab` and the next-row / coefficient families are unused. -/
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
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  exact argument.soundness hω wTab wTab sel hsel ζ hζ α hα t D hD hCdeg htdeg hcheck

end Kimchi.Quotient.AddComplete

namespace Kimchi.Quotient.VarBaseMul

open Polynomial Kimchi.Quotient WeierstrassCurve.Affine

/-- **VarBaseMul quotient soundness.** Same shape as `AddComplete.soundness` for the two-row
VarBaseMul gate (`[NeZero n]` for the cyclic successor; the poly-witness next-row cells go
through `shift`). Every selector-active row satisfies the VarBaseMul gate predicate.

Proof: specialization of `Argument.soundness` at the instance `argument`. -/
theorem soundness {F : Type*} [Field F] [DecidableEq F] {n N : ℕ} [NeZero n] {ω : F}
    (hω : IsPrimitiveRoot ω n)
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
    ∀ i, sel i = 1 → Gate.VarBaseMul.Holds (rowWitness wTab i) :=
  argument.soundness hω wTab wTab sel hsel ζ hζ α hα t D hD hCdeg htdeg hcheck

end Kimchi.Quotient.VarBaseMul

namespace Kimchi.Quotient.EndoMul

open Polynomial Kimchi.Quotient WeierstrassCurve.Affine

/-- **EndoMul quotient soundness.** Same shape as `AddComplete.soundness` for the two-row
EndoMul gate, with an extra endomorphism constant `endo : F` (the polynomial side uses
`C endo`, the row side `endo`). Every selector-active row satisfies the EndoMul gate predicate.

Proof: specialization of `Argument.soundness` at the instance `argument endo`; the endo
constant transports definitionally between the two carriers. -/
theorem soundness {F : Type*} [Field F] [DecidableEq F] {n N : ℕ} [NeZero n] {ω : F}
    (endo : F) (hω : IsPrimitiveRoot ω n)
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
    ∀ i, sel i = 1 → Gate.EndoMul.Holds endo (rowWitness wTab i) :=
  (argument endo).soundness hω wTab wTab sel hsel ζ hζ α hα t D hD hCdeg htdeg hcheck

end Kimchi.Quotient.EndoMul
