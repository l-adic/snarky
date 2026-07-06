import Kimchi.Quotient.Lift
import Kimchi.Quotient.Shifted
import Kimchi.Gate.VarBaseMul

/-!
# Quotient lift of the VarBaseMul gate

The polynomial-algebra lift of kimchi's variable-base scalar-multiplication gate.
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
* `argument` — the VarBaseMul `Argument F` instance (two-row layout).
* `rows_iff_dvd` — the divisibility corollary, an immediate instance of the `Argument`
  engine theorems.

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

/-! ## The `Argument` instance -/

/-- **VarBaseMul `Argument` instance.** The gate's constraints read through the two-row cell
map (`cellMap env.witnessCurr env.witnessNext`; the coefficient family is unused); naturality
is the gate's `Gate.VarBaseMul.constraints_map` at the underlying ring hom. -/
def argument : Argument F where
  constraints env := Gate.VarBaseMul.constraints (cellMap env.witnessCurr env.witnessNext)
  constraints_map f env :=
    Gate.VarBaseMul.constraints_map f.toRingHom (cellMap env.witnessCurr env.witnessNext)

/-! ## Divisibility corollary -/

/-- **VarBaseMul rows hold iff divisible.** The gate's constraint polynomials are all divisible
by the vanishing polynomial `Z_H` iff the gate holds on every row. Immediate specialization of
`Argument.rows_iff_dvd` at the instance `argument`. -/
theorem rows_iff_dvd [NeZero n] (hω : IsPrimitiveRoot ω n)
    (wTab : Fin n → Fin 15 → F) :
    (∀ E ∈ Gate.VarBaseMul.constraints (polyWitness ω wTab), zH F n ∣ E)
      ↔ ∀ i, Gate.VarBaseMul.Holds (rowWitness wTab i) :=
  argument.rows_iff_dvd hω wTab wTab

end Kimchi.Quotient.VarBaseMul
