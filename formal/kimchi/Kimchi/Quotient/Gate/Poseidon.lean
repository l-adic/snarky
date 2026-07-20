import Kimchi.Quotient.Lift
import Kimchi.Quotient.Shifted
import Kimchi.Gate.Poseidon

/-!
# Quotient lift of the Poseidon gate

The polynomial-algebra lift of kimchi's Poseidon gate, realized as a
`Kimchi.Quotient.Argument` instance. Poseidon applies five permutation rounds per row
(15 constraints = 5 rounds × 3 state elements). It is a **two-row** gate with a **permuted**
register layout, and its round constants are its coefficient row: the next-row family supplies
the output state `s5`, and the coefficient family supplies the round constants `rc`. The MDS
entries are integer literals, so the gate's plain ring-hom naturality
(`Gate.Poseidon.constraints_map`) already carries the `F`-algebra naturality the instance
needs.

## The register layout

The layout (kimchi `poseidon.rs`, module-doc table l.9--13) is a genuine permutation:

```
|  0 |  1 |  2 |  3 |  4 |  5 |  6 |  7 |  8 |  9 | 10 | 11 | 12 | 13 | 14 |
| s0 | s0 | s0 | s4 | s4 | s4 | s1 | s1 | s1 | s2 | s2 | s2 | s3 | s3 | s3 |
| s5 | s5 | s5 |    |    |    |    |    |    |    |    |    |    |    |    |
```

Note that `s4` is stored **before** `s1, s2, s3` in the register order; the output state `s5`
sits on the next row; the round constants `rc` come from the coefficient row (`rc()` l.212--217:
`coeffs[SPONGE_WIDTH * round + col]`, `SPONGE_WIDTH = 3`).

## Contents

* `cellMap` / `rcMap` — the permuted layout transcription (state cells / round constants).
* `rowWitness` / `rcRow` / `polyWitness` / `rcPoly` — their two carrier instantiations.
* `argument` — the Poseidon `Argument F` instance.
-/

namespace Kimchi.Quotient.Gate.Poseidon

open Polynomial Kimchi.Quotient

variable {F : Type*} [Field F] {n N : ℕ} {ω : F}

/-! ## The layout transcription -/

/-- **Poseidon cell map.** Assemble a `Gate.Poseidon.Witness R` from the permuted register
layout: the current row supplies `s0, s4, s1, s2, s3` (in register order), the next row
supplies the output state `s5`. -/
def cellMap {R : Type*} (cur nxt : Fin 15 → R) : Gate.Poseidon.Witness R where
  s0 := (cur 0, cur 1, cur 2)
  s4 := (cur 3, cur 4, cur 5)
  s1 := (cur 6, cur 7, cur 8)
  s2 := (cur 9, cur 10, cur 11)
  s3 := (cur 12, cur 13, cur 14)
  s5 := (nxt 0, nxt 1, nxt 2)

/-- **Poseidon round-constant map.** Read the round-constant triples off a coefficient row:
`rc j = (coeff (3j), coeff (3j+1), coeff (3j+2))`. -/
def rcMap {R : Type*} (coeff : Fin 15 → R) : Fin 5 → R × R × R := fun j =>
  (coeff ⟨3 * (j : ℕ), by have := j.isLt; omega⟩,
   coeff ⟨3 * (j : ℕ) + 1, by have := j.isLt; omega⟩,
   coeff ⟨3 * (j : ℕ) + 2, by have := j.isLt; omega⟩)

/-- **Poseidon row witness.** The state cells at rows `i` and `i + 1` (cyclic) of a witness
table. -/
def rowWitness [NeZero n] (wTab : Fin n → Fin 15 → F) (i : Fin n) : Gate.Poseidon.Witness F :=
  cellMap (wTab i) (wTab (i + 1))

/-- **Poseidon poly witness.** The state cells as column interpolants: `columnPoly` on the
current side, its `shift` on the next side. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin 15 → F) :
    Gate.Poseidon.Witness (Polynomial F) :=
  cellMap (fun c => columnPoly ω (fun j => wTab j c))
    (fun c => shift ω (columnPoly ω (fun j => wTab j c)))

/-- **Poseidon poly round constants.** The round-constant triples as coefficient-column
interpolants. -/
noncomputable def rcPoly (ω : F) (qTab : Fin n → Fin 15 → F) :
    Fin 5 → Polynomial F × Polynomial F × Polynomial F :=
  rcMap (fun c => columnPoly ω (fun j => qTab j c))

/-! ## The `Argument` instance -/

/-- **Poseidon `Argument` instance.** The gate's constraints
`Gate.Poseidon.constraints (rcMap env.coeff) (cellMap env.witnessCurr env.witnessNext)`;
naturality is the gate's ring-hom `Gate.Poseidon.constraints_map` (the MDS entries are integer
literals, so no `algebraMap`-transported parameter is involved). -/
def argument : Argument F where
  constraints env :=
    Gate.Poseidon.constraints (rcMap env.coeff) (cellMap env.witnessCurr env.witnessNext)
  constraints_map f env :=
    Gate.Poseidon.constraints_map f.toRingHom (rcMap env.coeff)
      (cellMap env.witnessCurr env.witnessNext)

end Kimchi.Quotient.Gate.Poseidon
