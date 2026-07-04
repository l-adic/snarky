import Kimchi.Quotient.Lift
import Kimchi.Quotient.Shifted
import Kimchi.Gate.VarBaseMul

/-!
# Quotient lift of the VarBaseMul gate

Archon-original polynomial-algebra lift of kimchi's variable-base scalar-multiplication gate.
**Commitment-free**: everything lives over an abstract field `[Field F]` with a primitive
`n`-th root of unity supplied as a hypothesis (`ω : F`, `hω : IsPrimitiveRoot ω n`).

This is a **two-row** gate: a `VBSM` row `i` followed by a `ZERO` row `i+1`. Its cell map reads
*both* rows, so the poly witness needs the next-row shift (`Kimchi.Quotient.shift`,
`Kimchi/Quotient/Shifted.lean`) in addition to the column interpolants. The gate's field-level
constraint model (`Kimchi.Gate.VarBaseMul.constraints` / `Holds`) is **read-only** and reused
verbatim: no constraint formula is restated — the lift is naturality plus the shift.

`i + 1 : Fin n` is taken **cyclically**, needing `[NeZero n]`. A two-row gate is never placed
on the last domain row, so this agrees with the intended semantics on every occupied row.

## Contents

* `cellMap` — assemble a `Gate.VarBaseMul.Witness R` from a current and next row.
* `rowWitness` / `polyWitness` — the field-valued row witness and its polynomial lift.
* `bridge` — naturality: evaluating the poly witness's constraints at `ω^i` reproduces the
  row witness's constraints.
* `rows_iff_dvd` / `rowsSel_iff_dvd` — the two engine-instance divisibility corollaries.

Source of truth: `blueprint/src/chapters/Kimchi_Quotient_VarBaseMul.tex`.
-/

namespace Kimchi.Quotient.VarBaseMul

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## Column layout and the cell map -/

/-- **VarBaseMul cell map.** For current/next rows `cur nxt : Fin 15 → R`, assemble the gate
witness by reading each column from the row the layout table assigns it (VBSM row `i` supplies
`cur`, ZERO row `i+1` supplies `nxt`):

```
row i  : xT yT x0 y0  n  n'  _  x1 y1 x2 y2 x3 y3 x4 y4   (VBSM)
row i+1: x5 y5 b0 b1 b2 b3 b4 s0 s1 s2 s3 s4  _  _  _     (ZERO)
```
-/
def cellMap {R : Type*} (cur nxt : Fin 15 → R) : Gate.VarBaseMul.Witness R where
  xT := cur 0
  yT := cur 1
  x0 := cur 2
  y0 := cur 3
  n := cur 4
  nPrime := cur 5
  x1 := cur 7
  y1 := cur 8
  x2 := cur 9
  y2 := cur 10
  x3 := cur 11
  y3 := cur 12
  x4 := cur 13
  y4 := cur 14
  x5 := nxt 0
  y5 := nxt 1
  b0 := nxt 2
  b1 := nxt 3
  b2 := nxt 4
  b3 := nxt 5
  b4 := nxt 6
  s0 := nxt 7
  s1 := nxt 8
  s2 := nxt 9
  s3 := nxt 10
  s4 := nxt 11

/-- **VarBaseMul row witness.** For a table `wTab : Fin n → Fin 15 → F` the row witness at `i`
reads the current row `i` and the next row `i+1` (cyclic, needing `[NeZero n]`). -/
def rowWitness [NeZero n] (wTab : Fin n → Fin 15 → F) (i : Fin n) :
    Gate.VarBaseMul.Witness F :=
  cellMap (wTab i) (wTab (i + 1))

/-- **VarBaseMul poly witness.** Feed `cellMap` the column interpolants on the current side and
their shifts on the next side. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin 15 → F) :
    Gate.VarBaseMul.Witness (Polynomial F) :=
  cellMap (fun c => columnPoly ω (fun j => wTab j c))
    (fun c => shift ω (columnPoly ω (fun j => wTab j c)))

/-! ## The naturality bridge -/

/-- **VarBaseMul per-row bridge.** Evaluating the poly witness's constraint polynomials at the
node `ω^i` reproduces the row witness's field-level constraints. Discharged by naturality of
`Gate.VarBaseMul.constraints_map` at `evalRingHom (ω^i)`, then `eval_columnPoly` (current side)
and `eval_shift_columnPoly` (next side). -/
theorem bridge [NeZero n] (hω : IsPrimitiveRoot ω n) (wTab : Fin n → Fin 15 → F) (i : Fin n) :
    (Gate.VarBaseMul.constraints (polyWitness ω wTab)).map (·.eval (ω ^ (i : ℕ)))
      = Gate.VarBaseMul.constraints (rowWitness wTab i) := by
  -- Evaluation at `ω^i` is the ring hom `evalRingHom (ω^i)`; rewrite the plain map by it.
  have hfun : (fun E : Polynomial F => E.eval (ω ^ (i : ℕ)))
      = ⇑(evalRingHom (ω ^ (i : ℕ))) := by
    funext E; rw [Polynomial.coe_evalRingHom]
  rw [hfun, Gate.VarBaseMul.constraints_map]
  -- Now identify the mapped poly-witness with the row witness, cell by cell: current-side cells
  -- reduce by `eval_columnPoly`, next-side (shifted) cells by `eval_shift_columnPoly`.
  congr 1
  simp only [polyWitness, rowWitness, cellMap, Gate.VarBaseMul.Witness.map,
    Polynomial.coe_evalRingHom, eval_columnPoly hω, eval_shift_columnPoly hω]

/-! ## Divisibility corollaries -/

/-- **VarBaseMul rows hold iff divisible.** The gate's constraint polynomials are all divisible
by the vanishing polynomial `Z_H` iff the gate holds on every row. Instance of the engine
`rows_iff_dvd_of` with the bridge above. -/
theorem rows_iff_dvd [NeZero n] (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (wTab : Fin n → Fin 15 → F) :
    (∀ E ∈ Gate.VarBaseMul.constraints (polyWitness ω wTab), zH F n ∣ E)
      ↔ ∀ i, Gate.VarBaseMul.Holds (rowWitness wTab i) := by
  -- Instantiate the ungated engine; `Holds w` is defeq to `∀ e ∈ constraints w, e = 0`.
  exact Kimchi.Quotient.rows_iff_dvd_of hω hn _
    (fun i => Gate.VarBaseMul.constraints (rowWitness wTab i)) (bridge hω wTab)

/-- **VarBaseMul selector-gated rows iff divisible.** With a boolean selector column
`S = columnPoly ω sel`, divisibility of `S · E` by `Z_H` is equivalent to the gate holding only
on the selected rows. Instance of the engine `rowsSel_iff_dvd` with the bridge above. -/
theorem rowsSel_iff_dvd [NeZero n] (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (wTab : Fin n → Fin 15 → F) (sel : Fin n → F) (hsel : ∀ i, sel i = 0 ∨ sel i = 1) :
    (∀ E ∈ Gate.VarBaseMul.constraints (polyWitness ω wTab),
        zH F n ∣ (columnPoly ω sel) * E)
      ↔ ∀ i, sel i = 1 → Gate.VarBaseMul.Holds (rowWitness wTab i) := by
  -- Instantiate the selector-gated engine; `Holds w` is defeq to `∀ e ∈ constraints w, e = 0`.
  exact Kimchi.Quotient.rowsSel_iff_dvd hω hn _
    (fun i => Gate.VarBaseMul.constraints (rowWitness wTab i)) sel hsel (bridge hω wTab)

end Kimchi.Quotient.VarBaseMul
