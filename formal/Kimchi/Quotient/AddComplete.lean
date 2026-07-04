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
* `bridge` — evaluating the gate's constraint polynomials at `ω^i` reproduces the gate's
  constraints at row `i` (pure naturality).
* `rows_iff_dvd` / `rowsSel_iff_dvd` — the two divisibility corollaries, immediate instances
  of the engine theorems.

Source of truth: `blueprint/src/chapters/Kimchi_Quotient_AddComplete.tex`.
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

/-! ## The naturality bridge -/

/-- **CompleteAdd per-row bridge.** Evaluating the gate's constraint polynomials at the node
`ω^i` reproduces the gate's constraints at row `i` — pure naturality of `constraints` under
`evalRingHom (ω^i)`, discharged via `constraints_map` and `eval_columnPoly`. -/
theorem bridge (hω : IsPrimitiveRoot ω n) (wTab : Fin n → Fin 15 → F) (i : Fin n) :
    (Gate.AddComplete.constraints (polyWitness ω wTab)).map (·.eval (ω ^ (i : ℕ)))
      = Gate.AddComplete.constraints (rowWitness wTab i) := by
  -- Evaluation at `ω^i` is the ring hom `evalRingHom (ω^i)`; rewrite the plain map by it.
  have hfun : (fun E : Polynomial F => E.eval (ω ^ (i : ℕ)))
      = ⇑(evalRingHom (ω ^ (i : ℕ))) := by
    funext E; rw [Polynomial.coe_evalRingHom]
  rw [hfun, Gate.AddComplete.constraints_map]
  -- Now identify the mapped poly-witness with the row witness, cell by cell.
  congr 1
  simp only [polyWitness, rowWitness, cellMap, Gate.AddComplete.Witness.map,
    Polynomial.coe_evalRingHom, eval_columnPoly hω]

/-! ## Divisibility corollaries -/

/-- **CompleteAdd rows hold iff divisible.** Instance of the ungated engine
`rows_iff_dvd_of` at the CompleteAdd bridge. -/
theorem rows_iff_dvd (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (wTab : Fin n → Fin 15 → F) :
    (∀ E ∈ Gate.AddComplete.constraints (polyWitness ω wTab), zH F n ∣ E)
      ↔ ∀ i, Gate.AddComplete.Holds (rowWitness wTab i) := by
  -- Instantiate the ungated engine; `Holds w` is defeq to `∀ e ∈ constraints w, e = 0`.
  exact Kimchi.Quotient.rows_iff_dvd_of hω hn _
    (fun i => Gate.AddComplete.constraints (rowWitness wTab i)) (bridge hω wTab)

/-- **CompleteAdd selector-gated rows iff divisible.** Instance of the selector-gated engine
`rowsSel_iff_dvd` at the CompleteAdd bridge; the boolean selector column `S = columnPoly ω sel`
is `1` on the rows the gate occupies and `0` elsewhere. -/
theorem rowsSel_iff_dvd (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (wTab : Fin n → Fin 15 → F)
    (sel : Fin n → F) (hsel : ∀ i, sel i = 0 ∨ sel i = 1) :
    (∀ E ∈ Gate.AddComplete.constraints (polyWitness ω wTab),
        zH F n ∣ (columnPoly ω sel) * E)
      ↔ ∀ i, sel i = 1 → Gate.AddComplete.Holds (rowWitness wTab i) := by
  -- Instantiate the selector-gated engine; `Holds w` is defeq to `∀ e ∈ constraints w, e = 0`.
  exact Kimchi.Quotient.rowsSel_iff_dvd hω hn _
    (fun i => Gate.AddComplete.constraints (rowWitness wTab i)) sel hsel (bridge hω wTab)

end Kimchi.Quotient.AddComplete
