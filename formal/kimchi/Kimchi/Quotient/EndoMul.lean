import Kimchi.Quotient.Lift
import Kimchi.Quotient.Shifted
import Kimchi.Gate.EndoMul

/-!
# Quotient lift of the EndoMul gate

The polynomial-algebra lift of kimchi's `EndoMul` (endomorphism-optimized
`VarBaseMul`) gate, following the cell-map / bridge / corollaries pattern of
`Kimchi/Quotient/AddComplete.lean` and `Kimchi/Quotient/VarBaseMul.lean`. Like `VarBaseMul`
it is a **two-row** gate (a pair of `EVBSM` rows `i`, `i+1`), so the poly witness reads the
next-row outputs `xS, yS, n'` through the shift operator (`Kimchi/Quotient/Shifted.lean`).

Two wrinkles over `VarBaseMul`:

* The gate's constraint list is parametrized by the base-field endomorphism coefficient
  `endo`; on the polynomial side this constant is `C endo`, and evaluation at any node returns
  `endo` (`eval_C`), so the same naturality argument goes through with the constant transported.
* The modeled gate is the **upstream-fixed** revision (12 constraints, with the distinct-point
  check `(xP - xR)·(xR - xS)·inv = 1`); its `inv` witness cell is not present in the pre-fix
  layout table; the fix reads it from current-row column 2 (`env.witness_curr(2)`).

The gate's field-level constraint model (`Kimchi.Gate.EndoMul.constraints`/`Holds`) is
**read-only** and reused verbatim; no formula is restated here.

**Modeling note (the `inv` cell).** The Lean gate models the upstream-fixed revision
(o1-labs/proof-systems@64129ce4), which adds the distinct-point constraint
`(xP - xR)(xR - xS) inv = 1` with an extra witness cell `inv`. That cell does not appear in the
pre-fix layout table, whose columns `2, 3` of the current row are free. We assign
`inv = cur 2`, verified against that commit. Faithfulness aside, the bridge
is naturality of `constraints` under evaluation and holds for *any* internally consistent column
assignment (the same `cellMap` defines both witnesses). The physical column matters only for
matching kimchi's concrete circuit table, which this commitment-free layer never pins.

## Column layout

An `EndoMul` block spans two `EVBSM` rows. Its inputs (`xT, yT, xP, yP, n`, the bits
`b1..b4`, the slopes `s1, s3`, and the intermediate point `xR, yR`) live on the current row
`i`; its outputs (`xS, yS` and the updated scalar `n'`) live on the next row `i+1`.

Source: kimchi `endosclmul.rs`, module-doc layout table and `constraint_checks`.

## Contents

* `cellMap` — reads the two rows into a `Gate.EndoMul.Witness`.
* `rowWitness` / `polyWitness` — the field-valued row witness and its polynomial lift.
* `argument` — the EndoMul `Argument F` instance, parametrized by `endo : F` (two-row layout).
* `rows_iff_dvd` — the divisibility corollary, a specialization of the `Argument` engine
  theorems.

Source of truth: `blueprint/src/chapters/Kimchi_Quotient_EndoMul.tex`.
-/

namespace Kimchi.Quotient.EndoMul

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## The cell map -/

/-- **EndoMul cell map.** Read the current/next rows `cur, nxt : Fin 15 → R` into a
`Gate.EndoMul.Witness R`. Current-row cells carry the inputs, the intermediate point, the
slopes and the bits; the next-row cells `4, 5, 6` carry the outputs `xS, yS, n'`. The `inv`
cell is `cur 2`, per the fix commit (see the file preamble). -/
def cellMap {R : Type*} (cur nxt : Fin 15 → R) : Gate.EndoMul.Witness R where
  xT := cur 0
  yT := cur 1
  xP := cur 4
  yP := cur 5
  n := cur 6
  nPrime := nxt 6
  b1 := cur 11
  b2 := cur 12
  b3 := cur 13
  b4 := cur 14
  s1 := cur 9
  xR := cur 7
  yR := cur 8
  s3 := cur 10
  xS := nxt 4
  yS := nxt 5
  inv := cur 2

/-- **EndoMul row witness.** For a table `wTab : Fin n → Fin 15 → F`, read rows `i` and `i+1`
(cyclic, needing `[NeZero n]`) through `cellMap`. -/
def rowWitness [NeZero n] (wTab : Fin n → Fin 15 → F) (i : Fin n) :
    Gate.EndoMul.Witness F :=
  cellMap (wTab i) (wTab (i + 1))

/-- **EndoMul poly witness.** The polynomial lift: current-row cells become the column
interpolants `columnPoly ω (fun j => wTab j c)`, and next-row cells become their shifts
`shift ω (columnPoly ω (fun j => wTab j c))`. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin 15 → F) :
    Gate.EndoMul.Witness (Polynomial F) :=
  cellMap (fun c => columnPoly ω (fun j => wTab j c))
    (fun c => shift ω (columnPoly ω (fun j => wTab j c)))

/-! ## The `Argument` instance -/

/-- **EndoMul `Argument` instance.** Parametrized by the base-field endomorphism coefficient
`endo : F`; over an `F`-algebra `R` the constant is transported as `algebraMap F R endo`
(on `R = F[X]` this is `C endo`, cf. `Polynomial.algebraMap_eq`), which every `F`-algebra hom
fixes (`AlgHom.commutes`) — that is what makes the gate's ring-hom naturality
`Gate.EndoMul.constraints_map` land back on the same instance. The cell map reads the current
and next rows (a two-row gate; the coefficient family is unused). -/
def argument (endo : F) : Argument F where
  constraints {R} _ _ env :=
    Gate.EndoMul.constraints (algebraMap F R endo) (cellMap env.witnessCurr env.witnessNext)
  constraints_map f env := by
    have h := Gate.EndoMul.constraints_map f.toRingHom (algebraMap F _ endo)
      (cellMap env.witnessCurr env.witnessNext)
    rw [show f.toRingHom (algebraMap F _ endo) = algebraMap F _ endo from f.commutes endo] at h
    exact h

/-! ## Divisibility corollary -/

/-- **EndoMul rows hold iff divisible.** The full list of poly constraints is divisible by the
vanishing polynomial `zH` iff every `EndoMul` row-witness satisfies `Holds`. Immediate
specialization of `Argument.rows_iff_dvd` at the instance `argument endo`: the constant
transports definitionally (`algebraMap F F[X] endo` is `C endo`, `algebraMap F F endo` is
`endo`). -/
theorem rows_iff_dvd [NeZero n] (endo : F) (hω : IsPrimitiveRoot ω n)
    (wTab : Fin n → Fin 15 → F) :
    (∀ E ∈ Gate.EndoMul.constraints (C endo) (polyWitness ω wTab), zH F n ∣ E)
      ↔ ∀ i, Gate.EndoMul.Holds endo (rowWitness wTab i) :=
  (argument endo).rows_iff_dvd hω wTab wTab

end Kimchi.Quotient.EndoMul
