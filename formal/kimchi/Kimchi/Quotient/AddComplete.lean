import Kimchi.Quotient.Lift
import Kimchi.Gate.AddComplete

/-!
# Quotient lift of the CompleteAdd gate

The polynomial-algebra lift of kimchi's CompleteAdd gate, built on the generic
lift engine (`Kimchi.Quotient.Lift`) and the domain substrate (`Kimchi.Quotient.Domain`).

CompleteAdd is a **single-row** gate, so its cell map reads only the current row. The gate's
field-level constraint model (`Kimchi.Gate.AddComplete.constraints` / `Holds`) is READ-ONLY
and reused verbatim: no constraint formula is restated here — the lift is purely the
naturality of `constraints` under evaluation at the domain nodes.

## Contents

* `cellMap` — assemble a `Gate.AddComplete.Witness R` from a row `cur : Fin 15 → R`.
* `rowWitness` / `polyWitness` — the row-values and column-interpolant witnesses, both via
  the same `cellMap`.
* `argument` — the CompleteAdd `Argument F` instance (single-row layout).
* `rows_iff_dvd` — the divisibility corollary, an immediate instance of the `Argument`
  engine theorems.
-/

namespace Kimchi.Quotient.AddComplete

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## Column layout and the cell map

A CompleteAdd row occupies the 11 witness columns `0`–`10` of the size-`15` circuit table;
columns `11`–`14` are unused. Layout (kimchi `complete_add.rs`, module-doc table):

```
|  0 |  1 |  2 |  3 |  4 |  5 |  6  |    7   | 8 |   9   |    10   |
| x1 | y1 | x2 | y2 | x3 | y3 | inf | same_x | s | inf_z | x21_inv |
```
-/

/-- **CompleteAdd cell map.** Assemble a `Gate.AddComplete.Witness R` by reading the circuit
columns of a row `cur : Fin 15 → R`. -/
def cellMap {R : Type*} (cur : Fin 15 → R) : Gate.AddComplete.Witness R where
  x1     := cur 0
  y1     := cur 1
  x2     := cur 2
  y2     := cur 3
  x3     := cur 4
  y3     := cur 5
  inf    := cur 6
  sameX  := cur 7
  s      := cur 8
  infZ   := cur 9
  x21Inv := cur 10

/-- **CompleteAdd row witness.** The gate witness at row `i`, read off the circuit witness
table `wTab : Fin n → Fin 15 → F`. -/
def rowWitness (wTab : Fin n → Fin 15 → F) (i : Fin n) : Gate.AddComplete.Witness F :=
  cellMap (wTab i)

/-- **CompleteAdd poly witness.** The gate witness whose every cell is the interpolant
`columnPoly ω` of the corresponding circuit column. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin 15 → F) :
    Gate.AddComplete.Witness (Polynomial F) :=
  cellMap (fun c => columnPoly ω (fun j => wTab j c))

/-! ## The `Argument` instance -/

/-- **CompleteAdd `Argument` instance.** The gate's constraints read through the single-row
cell map (`cellMap env.witnessCurr`; the next-row and coefficient families are unused);
naturality is the gate's `Gate.AddComplete.constraints_map` at the underlying ring hom. -/
def argument : Argument F where
  constraints env := Gate.AddComplete.constraints (cellMap env.witnessCurr)
  constraints_map f env := Gate.AddComplete.constraints_map f.toRingHom (cellMap env.witnessCurr)

/-! ## Divisibility corollary -/

/-- **CompleteAdd rows hold iff divisible.** Immediate specialization of
`Argument.rows_iff_dvd` at the instance `argument`; single-row, so `qTab := wTab` and the
next-row / coefficient families are unused. -/
theorem rows_iff_dvd (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (wTab : Fin n → Fin 15 → F) :
    (∀ E ∈ Gate.AddComplete.constraints (polyWitness ω wTab), zH F n ∣ E)
      ↔ ∀ i, Gate.AddComplete.Holds (rowWitness wTab i) := by
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  exact argument.rows_iff_dvd hω wTab wTab

end Kimchi.Quotient.AddComplete
