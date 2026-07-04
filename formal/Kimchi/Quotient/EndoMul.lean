import Kimchi.Quotient.Lift
import Kimchi.Quotient.Shifted
import Kimchi.Gate.EndoMul

/-!
# Quotient lift of the EndoMul gate

Archon-original polynomial-algebra lift of kimchi's `EndoMul` (endomorphism-optimized
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
* `bridge` — evaluating the poly constraints at the node `ω^i` reproduces the row constraints.
* `rows_iff_dvd` / `rowsSel_iff_dvd` — the two engine-instance divisibility corollaries.

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

/-! ## The naturality bridge -/

/-- **EndoMul per-row bridge.** Evaluating the poly-witness constraints (with `endo = C endo`)
at the node `ω^i` reproduces the row-witness constraints (with `endo = endo`). This is
naturality of `Gate.EndoMul.constraints_map` at `f = evalRingHom (ω^i)`, transporting `C endo`
to `endo` via `eval_C` and matching the witness cells via `eval_columnPoly` (current) and
`eval_shift_columnPoly` (next). -/
theorem bridge [NeZero n] (endo : F) (hω : IsPrimitiveRoot ω n)
    (wTab : Fin n → Fin 15 → F) (i : Fin n) :
    (Gate.EndoMul.constraints (C endo) (polyWitness ω wTab)).map (·.eval (ω ^ (i : ℕ)))
      = Gate.EndoMul.constraints endo (rowWitness wTab i) := by
  -- Evaluation at `ω^i` is the ring hom `evalRingHom (ω^i)`; rewrite the plain map by it.
  have hfun : (fun E : Polynomial F => E.eval (ω ^ (i : ℕ)))
      = ⇑(evalRingHom (ω ^ (i : ℕ))) := by
    funext E; rw [Polynomial.coe_evalRingHom]
  rw [hfun, Gate.EndoMul.constraints_map]
  -- The endo constant transports via `eval_C`; the witness cells via `eval_columnPoly`
  -- (current row) and `eval_shift_columnPoly` (next row).
  congr 1
  · rw [Polynomial.coe_evalRingHom, eval_C]
  · simp only [polyWitness, rowWitness, cellMap, Gate.EndoMul.Witness.map,
      Polynomial.coe_evalRingHom, eval_columnPoly hω, eval_shift_columnPoly hω]

/-! ## Divisibility corollaries -/

/-- **EndoMul rows hold iff divisible.** The full list of poly constraints is divisible by the
vanishing polynomial `zH` iff every `EndoMul` row-witness satisfies `Holds`. Instance of the
engine `rows_iff_dvd_of` with the bridge discharged by `bridge`. -/
theorem rows_iff_dvd [NeZero n] (endo : F) (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (wTab : Fin n → Fin 15 → F) :
    (∀ E ∈ Gate.EndoMul.constraints (C endo) (polyWitness ω wTab), zH F n ∣ E)
      ↔ ∀ i, Gate.EndoMul.Holds endo (rowWitness wTab i) := by
  -- Instantiate the ungated engine; `Holds endo w` is defeq to `∀ e ∈ constraints endo w, e = 0`.
  exact Kimchi.Quotient.rows_iff_dvd_of hω hn _
    (fun i => Gate.EndoMul.constraints endo (rowWitness wTab i)) (bridge endo hω wTab)

/-- **EndoMul selector-gated rows iff divisible.** With a boolean selector `sel : Fin n → F`
and `S = columnPoly ω sel`, divisibility of every `S · E` by `zH` is equivalent to the row
constraints holding only on the selected rows. Instance of the engine `rowsSel_iff_dvd`. -/
theorem rowsSel_iff_dvd [NeZero n] (endo : F) (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (wTab : Fin n → Fin 15 → F) (sel : Fin n → F) (hsel : ∀ i, sel i = 0 ∨ sel i = 1) :
    (∀ E ∈ Gate.EndoMul.constraints (C endo) (polyWitness ω wTab),
        zH F n ∣ (columnPoly ω sel) * E)
      ↔ ∀ i, sel i = 1 → Gate.EndoMul.Holds endo (rowWitness wTab i) := by
  -- Instantiate the selector-gated engine; `Holds endo w` is defeq to
  -- `∀ e ∈ constraints endo w, e = 0`.
  exact Kimchi.Quotient.rowsSel_iff_dvd hω hn _
    (fun i => Gate.EndoMul.constraints endo (rowWitness wTab i)) sel hsel (bridge endo hω wTab)

end Kimchi.Quotient.EndoMul
