import Kimchi.Quotient.Lift
import Kimchi.Gate.EndoScalar

/-!
# Quotient lift of the EndoScalar gate

The polynomial-algebra lift of kimchi's `EndoScalar` gate (the endomorphism-scalar recoder —
pure field arithmetic running Halo's Algorithm 2 over MSB-first 2-bit crumbs), packaged as a
`Kimchi.Quotient.Argument` instance.

The gate's constraint list `Gate.EndoScalar.constraints` is defined over any commutative
`F`-algebra — its interpolating-cubic coefficients (`cPoly`/`dPoly`) enter through
`algebraMap F R` — so the instance is a direct read-through of the cell map; naturality is the
gate module's `Gate.EndoScalar.constraints_map`.

`EndoScalar` is a **single-row** gate: both `n0` (input) and `n8` (output) live on the same
row, so the cell map reads the current row only (the next-row and coefficient families are
unused). The cross-row chaining of the scalar register (`n0 ↔ n8`) is a copy-constraint
concern (the permutation layer), out of scope here.

## Column layout

Source: proof-systems kimchi `endomul_scalar.rs`, witness-layout comment l.116-122
(`CONSTRAINTS = 11`):

```
|  0 |  1 |  2 |  3 |  4 |  5 |  6 |  7 |  8 |  9 | 10 | 11 | 12 | 13 | 14 | Type |
| n0 | n8 | a0 | b0 | a8 | b8 | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 |    | ENDO |
```

where each `xi` is a two-bit "crumb".

## Contents

* `cellMap` / `rowWitness` / `polyWitness` — the layout transcription and its two carrier
  instantiations.
* `argument` — the `Argument F` instance (`def:quotient_endoscalar_lift`).
-/

namespace Kimchi.Quotient.Gate.EndoScalar

open Polynomial Kimchi.Quotient

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## Column layout and the cell map -/

/-- **EndoScalar cell map.** Assemble a `Gate.EndoScalar.Witness R` by reading the circuit
columns of a row `cur : Fin 15 → R`. The eight crumbs are the literal 8-element list, so the
accumulator folds unfold directly on it (no witness reshape). -/
def cellMap {R : Type*} (cur : Fin 15 → R) : Gate.EndoScalar.Witness R where
  n0 := cur 0
  n8 := cur 1
  a0 := cur 2
  b0 := cur 3
  a8 := cur 4
  b8 := cur 5
  crumbs := [cur 6, cur 7, cur 8, cur 9, cur 10, cur 11, cur 12, cur 13]

/-- **EndoScalar row witness.** The gate witness at row `i`, read off the circuit witness
table `wTab : Fin n → Fin 15 → F`. -/
def rowWitness (wTab : Fin n → Fin 15 → F) (i : Fin n) : Gate.EndoScalar.Witness F :=
  cellMap (wTab i)

/-- **EndoScalar poly witness.** The gate witness whose every cell is the interpolant
`columnPoly ω` of the corresponding circuit column. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin 15 → F) :
    Gate.EndoScalar.Witness (Polynomial F) :=
  cellMap (fun c => columnPoly ω (fun j => wTab j c))

/-! ## The `Argument` instance -/

/-- **EndoScalar `Argument` instance.** The gate's algebra-generic constraints read through the
single-row cell map (`cellMap env.witnessCurr`; the next-row and coefficient families are
unused); naturality is the gate's `Gate.EndoScalar.constraints_map`. -/
def argument : Argument F where
  constraints env := Gate.EndoScalar.constraints (cellMap env.witnessCurr) (F := F)
  constraints_map f env := Gate.EndoScalar.constraints_map (F := F) f (cellMap env.witnessCurr)

end Kimchi.Quotient.Gate.EndoScalar
