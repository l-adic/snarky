import Kimchi.Quotient.Lift
import Kimchi.Gate.Generic

/-!
# The double generic gate's quotient lift

The polynomial lift of kimchi's **double** generic gate (`generic.rs`,
`CONSTRAINTS = 2`). Commitment-free, built directly on `Kimchi.Quotient.Domain`.

The row-level gate predicate is `Kimchi.Gate.Generic.Holds` (defined in
`Kimchi/Gate/Generic.lean` — the double generic gate's two cell constraints); this
file owns only the *polynomial* side — the cell map into `Gate.Generic` and the
gate's `Argument` instance over column interpolants.

## Column layout (from `generic.rs`)

A generic row carries 15 witness cells `w : Fin 15 → F` and 15 coefficient cells
`q : Fin 15 → F`. The row packs **two** generic gates: the first uses registers
`w 0, w 1, w 2` with coefficients `q 0 … q 4`; the second uses `w 3, w 4, w 5`
with coefficients `q 5 … q 9` (`q 10 … q 14` are unused here).

Source: kimchi `generic.rs` (module doc + `constraint_checks`, l.245–250):

    * w0·c0 + w1·c1 + w2·c2 + w0·w1·c3 + c4
    * w3·c5 + w4·c6 + w5·c7 + w3·w4·c8 + c9

where the `cᵢ` are the coefficients (`q` here).
-/

namespace Kimchi.Quotient.Gate.Generic

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## The `Argument` instance

The generic gate plugs into the `Argument` primitive of `Kimchi.Quotient.Lift` exactly like
the other five gates: the gate row `Gate.Generic R` is assembled from the current-row cells
(as `w`) and the coefficient cells (as `q`); the next-row family is unused (single-row). -/

/-- **Generic cell map.** Assemble a `Gate.Generic R` from current-row cells `cur` (→ `w`) and
coefficient cells `coeff` (→ `q`). -/
def cellMap {R : Type*} (cur coeff : Fin 15 → R) : Gate.Generic R :=
  ⟨coeff, cur⟩

/-- **Generic `Argument` instance.** The gate's constraint list `Gate.Generic.constraints`
read through `cellMap`; naturality is the gate module's `Generic.constraints_map` at
the underlying ring hom. -/
def argument : Argument F where
  constraints env := (cellMap env.witnessCurr env.coeff).constraints
  constraints_map f env :=
    Gate.Generic.constraints_map f.toRingHom (cellMap env.witnessCurr env.coeff)

end Kimchi.Quotient.Gate.Generic
