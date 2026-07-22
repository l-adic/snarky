import Kimchi.Columns
import Kimchi.Domain
import Kimchi.Shifted
import Kimchi.Aggregate
import Kimchi.SchwartzZippel
import Kimchi.Gate.AddComplete
import Kimchi.Gate.VarBaseMul
import Kimchi.Gate.EndoMul
import Kimchi.Gate.EndoScalar
import Kimchi.Gate.Poseidon
import Kimchi.Gate.Generic

/-!
# The gate-argument primitive

The polynomial-lift interface a gate's constraints are read through. **Commitment-free**:
everything lives over an abstract field `[Field F]` with a primitive `n`-th root of unity
supplied as a hypothesis (`ω : F`, `hω : IsPrimitiveRoot ω n`, `0 < n`). No gate formula is
ever restated at this layer — a gate supplies its constraint family and reuses the one
evaluation bridge below.

## The `ArgumentEnv` / `Argument` pair

The per-gate interface mirrors kimchi's `argument.rs`:

* `ArgumentEnv R` is the cell environment a gate's constraints may read, anchored at a row —
  the current-row witness cells, the next-row witness cells (cyclic `i + 1`), and the
  current row's coefficient cells. It is the Lean counterpart of kimchi's `ArgumentEnv`
  restricted to the cell accessors (`witness_curr` / `witness_next` / `coeff`).
* `Argument F` is one gate's constraint family: a list of constraint expressions defined over
  every commutative `F`-algebra `R` from an `ArgumentEnv R`, together with its naturality
  square along `F`-algebra homomorphisms. It is the Lean counterpart of kimchi's `Argument`
  trait: `constraints` is `constraint_checks`, generic over the carrier the way
  `constraint_checks` is generic over `T : ExprOps` — kimchi runs the same code at `T = F`
  (direct row checks) and `T = E<F>` (the symbolic expressions compiled into the quotient),
  and `constraints_map` is the corresponding agreement between the two instantiations, which
  Rust gets for free by parametricity and Lean states as a proof obligation.

Genericity over `F`-algebras (rather than plain rings) is what absorbs gate **parameters**
(EndoMul's endomorphism constant, EndoScalar's interpolating-cubic coefficients): each becomes
the image under `algebraMap F R` of a fixed element of `F`, and the evaluation morphism is the
`F`-algebra hom `Polynomial.aeval (ω^i) : F[X] →ₐ[F] F`, which fixes those images.

The two carrier instantiations are packaged once, gate-independently: `rowEnv` (the field-level
cells of row `i`) and `polyEnv` (the column interpolants, with `shift` on the next-row side).
`Argument.bridge` — evaluation at a node carries `polyEnv` to `rowEnv` — is the one bridge
in the library; every per-gate bridge is that gate's `constraints_map` pasted onto it.

## Contents

* `ArgumentEnv`, `rowEnv`, `polyEnv` — the cell environment and its two carrier
  instantiations (field-level row cells, and column interpolants with `shift` on the
  next-row side).
* `Argument`, `Argument.bridge` — one gate's constraint family, and the evaluation bridge
  carrying its polynomial-side constraints to the row-side ones.
-/

namespace Kimchi.Lift

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}
/-! ## The cell environment -/

/-- **The cell environment of a gate row.** The three cell families a gate's constraints may
read, anchored at a row: the current-row witness cells, the next-row witness cells (cyclic
`i + 1`), and the current row's coefficient cells. Lean counterpart of kimchi's `ArgumentEnv`
(`argument.rs`), restricted to the cell accessors (`witness_curr` / `witness_next` /
`coeff`). -/
structure ArgumentEnv (R : Type u) where
  witnessCurr : Fin wCols → R
  witnessNext : Fin wCols → R
  coeff : Fin coeffCols → R

/-- Push a carrier map `f : R → S` through an environment, cell by cell in each family. -/
def ArgumentEnv.map {R S : Type u} (f : R → S) (env : ArgumentEnv R) : ArgumentEnv S :=
  ⟨f ∘ env.witnessCurr, f ∘ env.witnessNext, f ∘ env.coeff⟩

/-- **Row environment.** The field-level cells at row `i` of a witness table `wTab` and a
coefficient table `qTab`: current row `wTab i`, next row `wTab (i + 1)` (cyclic), coefficients
`qTab i`. -/
def rowEnv [NeZero n] (wTab qTab : Fin n → Fin coeffCols → F) (i : Fin n) : ArgumentEnv F :=
  ⟨wTab i, wTab (i + 1), qTab i⟩

/-- **Polynomial environment.** The column interpolants of the tables: `columnPoly` of each
witness column on the current side, its `shift` on the next side, and `columnPoly` of each
coefficient column on the coefficient side. -/
noncomputable def polyEnv (ω : F) (wTab qTab : Fin n → Fin coeffCols → F) :
    ArgumentEnv (Polynomial F) :=
  ⟨fun c => columnPoly ω (fun j => wTab j c),
   fun c => shift ω (columnPoly ω (fun j => wTab j c)),
   fun c => columnPoly ω (fun j => qTab j c)⟩

/-- **Environment evaluation bridge.** Evaluating the polynomial environment at the node `ω^i`
— i.e. mapping the `F`-algebra hom `aeval (ω^i)` through it — yields the row environment at
`i`: `eval_columnPoly` on the current and coefficient sides, `eval_shift_columnPoly` on the
next side. This is the one evaluation bridge in the library; every gate reaches its own bridge
by pasting its naturality square onto this equation. -/
private theorem polyEnv_map_aeval [NeZero n] (hω : IsPrimitiveRoot ω n)
    (wTab qTab : Fin n → Fin coeffCols → F) (i : Fin n) :
    (polyEnv ω wTab qTab).map ⇑(aeval (ω ^ (i : ℕ)) : Polynomial F →ₐ[F] F)
      = rowEnv wTab qTab i := by
  simp only [polyEnv, ArgumentEnv.map, rowEnv]
  congr 1
  · funext c
    simp only [Function.comp_apply, Polynomial.coe_aeval_eq_eval, eval_columnPoly hω]
  · funext c
    simp only [Function.comp_apply, Polynomial.coe_aeval_eq_eval, eval_shift_columnPoly hω]
  · funext c
    simp only [Function.comp_apply, Polynomial.coe_aeval_eq_eval, eval_columnPoly hω]

/-! ## The `Argument` primitive over `F`-algebras -/

/-- **The `Argument` primitive.** One gate's constraint family: the list of constraint
expressions read from an `ArgumentEnv R`, defined for every commutative `F`-algebra `R`,
together with its naturality square along `F`-algebra homomorphisms. Counterpart of kimchi's
`Argument` trait (`argument.rs`): `constraints` is `constraint_checks`, and `constraints_map`
is the agreement between its carrier instantiations that Rust obtains by parametricity.

Gate parameters that are fixed field elements (an endomorphism coefficient, interpolating-cubic
coefficients) enter through `algebraMap F R`, which every `f : R →ₐ[F] S` fixes
(`AlgHom.commutes`) — this is what makes a uniform naturality square possible across gates with
different parameters. -/
structure Argument (F : Type u) [Field F] where
  constraints : ∀ {R : Type u} [CommRing R] [Algebra F R], ArgumentEnv R → List R
  constraints_map : ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
      (f : R →ₐ[F] S) (env : ArgumentEnv R),
    (constraints env).map f = constraints (env.map f)

/-- **`Argument` eval bridge.** Evaluating the constraint polynomials of the polynomial
environment at the node `ω^i` reproduces the field-level constraints of the row environment:
the naturality square `constraints_map` at `aeval (ω^i)`, pasted onto `polyEnv_map_aeval`. -/
theorem Argument.bridge [NeZero n] (G : Argument F) (hω : IsPrimitiveRoot ω n)
    (wTab qTab : Fin n → Fin coeffCols → F) (i : Fin n) :
    (G.constraints (polyEnv ω wTab qTab)).map (·.eval (ω ^ (i : ℕ)))
      = G.constraints (rowEnv wTab qTab i) := by
  have hfun : (fun E : Polynomial F => E.eval (ω ^ (i : ℕ)))
      = ⇑(aeval (ω ^ (i : ℕ)) : Polynomial F →ₐ[F] F) := by
    funext E; rw [Polynomial.coe_aeval_eq_eval]
  rw [hfun, G.constraints_map, polyEnv_map_aeval hω]

end Kimchi.Lift

/-!
## The CompleteAdd gate lift

The polynomial-algebra lift of kimchi's CompleteAdd gate, built on the generic
lift engine and the domain substrate (`Kimchi.Lift.Domain`).

CompleteAdd is a **single-row** gate, so its cell map reads only the current row. The gate's
field-level constraint model (`Kimchi.Gate.AddComplete.constraints` / `Holds`) is READ-ONLY
and reused verbatim: no constraint formula is restated here — the lift is purely the
naturality of `constraints` under evaluation at the domain nodes.

## Contents

* `cellMap` — assemble a `Gate.AddComplete.Witness R` from a row `cur : Fin wCols → R`.
* `rowWitness` / `polyWitness` — the row-values and column-interpolant witnesses, both via
  the same `cellMap`.
* `argument` — the CompleteAdd `Argument F` instance (single-row layout).
-/

namespace Kimchi.Lift.Gate.AddComplete

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
columns of a row `cur : Fin wCols → R`. -/
def cellMap {R : Type*} (cur : Fin wCols → R) : Gate.AddComplete.Witness R where
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
table `wTab : Fin n → Fin wCols → F`. -/
def rowWitness (wTab : Fin n → Fin wCols → F) (i : Fin n) : Gate.AddComplete.Witness F :=
  cellMap (wTab i)

/-- **CompleteAdd poly witness.** The gate witness whose every cell is the interpolant
`columnPoly ω` of the corresponding circuit column. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin wCols → F) :
    Gate.AddComplete.Witness (Polynomial F) :=
  cellMap (fun c => columnPoly ω (fun j => wTab j c))

/-! ## The `Argument` instance -/

/-- **CompleteAdd `Argument` instance.** The gate's constraints read through the single-row
cell map (`cellMap env.witnessCurr`; the next-row and coefficient families are unused);
naturality is the gate's `Gate.AddComplete.constraints_map` at the underlying ring hom. -/
def argument : Argument F where
  constraints env := Gate.AddComplete.constraints (cellMap env.witnessCurr)
  constraints_map f env := Gate.AddComplete.constraints_map f.toRingHom (cellMap env.witnessCurr)

end Kimchi.Lift.Gate.AddComplete

/-!
## The VarBaseMul gate lift

The polynomial-algebra lift of kimchi's variable-base scalar-multiplication gate.
**Commitment-free**: everything lives over an abstract field `[Field F]` with a primitive
`n`-th root of unity supplied as a hypothesis (`ω : F`, `hω : IsPrimitiveRoot ω n`).

This is a **two-row** gate: a `VBSM` row `i` followed by a `ZERO` row `i+1`. Its cell map reads
*both* rows, so the poly witness needs the next-row shift (`Kimchi.shift`,
`Kimchi/Shifted.lean`) in addition to the column interpolants. The gate's field-level
constraint model (`Kimchi.Gate.VarBaseMul.constraints` / `Holds`) is **read-only** and reused
verbatim: no constraint formula is restated — the lift is naturality plus the shift.

`i + 1 : Fin n` is taken **cyclically**, needing `[NeZero n]`. A two-row gate is never placed
on the last domain row, so this agrees with the intended semantics on every occupied row.

## Contents

* `cellMap` — assemble a `Gate.VarBaseMul.Witness R` from a current and next row.
* `rowWitness` / `polyWitness` — the field-valued row witness and its polynomial lift.
* `argument` — the VarBaseMul `Argument F` instance (two-row layout).
-/

namespace Kimchi.Lift.Gate.VarBaseMul

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## Column layout and the cell map -/

/-- **VarBaseMul cell map.** For current/next rows `cur nxt : Fin wCols → R`, assemble the gate
witness by reading each column from the row the layout table assigns it (VBSM row `i` supplies
`cur`, ZERO row `i+1` supplies `nxt`):

```
row i  : xT yT x0 y0  n  n'  _  x1 y1 x2 y2 x3 y3 x4 y4   (VBSM)
row i+1: x5 y5 b0 b1 b2 b3 b4 s0 s1 s2 s3 s4  _  _  _     (ZERO)
```
-/
def cellMap {R : Type*} (cur nxt : Fin wCols → R) : Gate.VarBaseMul.Witness R where
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

/-- **VarBaseMul row witness.** For a table `wTab : Fin n → Fin wCols → F` the row witness at `i`
reads the current row `i` and the next row `i+1` (cyclic, needing `[NeZero n]`). -/
def rowWitness [NeZero n] (wTab : Fin n → Fin wCols → F) (i : Fin n) :
    Gate.VarBaseMul.Witness F :=
  cellMap (wTab i) (wTab (i + 1))

/-- **VarBaseMul poly witness.** Feed `cellMap` the column interpolants on the current side and
their shifts on the next side. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin wCols → F) :
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

end Kimchi.Lift.Gate.VarBaseMul

/-!
## The EndoMul gate lift

The polynomial-algebra lift of kimchi's `EndoMul` (endomorphism-optimized
`VarBaseMul`) gate, following the cell-map and `Argument`-instance pattern of the CompleteAdd and
VarBaseMul gate lifts above. Like
`VarBaseMul` it is a **two-row** gate (a pair of `EVBSM` rows `i`, `i+1`), so the poly witness
reads the next-row outputs `xS, yS, n'` through the shift operator (`Kimchi/Shifted.lean`).

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
-/

namespace Kimchi.Lift.Gate.EndoMul

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## The cell map -/

/-- **EndoMul cell map.** Read the current/next rows `cur, nxt : Fin wCols → R` into a
`Gate.EndoMul.Witness R`. Current-row cells carry the inputs, the intermediate point, the
slopes and the bits; the next-row cells `4, 5, 6` carry the outputs `xS, yS, n'`. The `inv`
cell is `cur 2`, per the fix commit (see the file preamble). -/
def cellMap {R : Type*} (cur nxt : Fin wCols → R) : Gate.EndoMul.Witness R where
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

/-- **EndoMul row witness.** For a table `wTab : Fin n → Fin wCols → F`, read rows `i` and `i+1`
(cyclic, needing `[NeZero n]`) through `cellMap`. -/
def rowWitness [NeZero n] (wTab : Fin n → Fin wCols → F) (i : Fin n) :
    Gate.EndoMul.Witness F :=
  cellMap (wTab i) (wTab (i + 1))

/-- **EndoMul poly witness.** The polynomial lift: current-row cells become the column
interpolants `columnPoly ω (fun j => wTab j c)`, and next-row cells become their shifts
`shift ω (columnPoly ω (fun j => wTab j c))`. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin wCols → F) :
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

end Kimchi.Lift.Gate.EndoMul

/-!
## The EndoScalar gate lift

The polynomial-algebra lift of kimchi's `EndoScalar` gate (the endomorphism-scalar recoder —
pure field arithmetic running Halo's Algorithm 2 over MSB-first 2-bit crumbs), packaged as a
`Kimchi.Lift.Argument` instance.

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

namespace Kimchi.Lift.Gate.EndoScalar

open Polynomial Kimchi.Lift

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## Column layout and the cell map -/

/-- **EndoScalar cell map.** Assemble a `Gate.EndoScalar.Witness R` by reading the circuit
columns of a row `cur : Fin wCols → R`. The eight crumbs are the literal 8-element list, so the
accumulator folds unfold directly on it (no witness reshape). -/
def cellMap {R : Type*} (cur : Fin wCols → R) : Gate.EndoScalar.Witness R where
  n0 := cur 0
  n8 := cur 1
  a0 := cur 2
  b0 := cur 3
  a8 := cur 4
  b8 := cur 5
  crumbs := [cur 6, cur 7, cur 8, cur 9, cur 10, cur 11, cur 12, cur 13]

/-- **EndoScalar row witness.** The gate witness at row `i`, read off the circuit witness
table `wTab : Fin n → Fin wCols → F`. -/
def rowWitness (wTab : Fin n → Fin wCols → F) (i : Fin n) : Gate.EndoScalar.Witness F :=
  cellMap (wTab i)

/-- **EndoScalar poly witness.** The gate witness whose every cell is the interpolant
`columnPoly ω` of the corresponding circuit column. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin wCols → F) :
    Gate.EndoScalar.Witness (Polynomial F) :=
  cellMap (fun c => columnPoly ω (fun j => wTab j c))

/-! ## The `Argument` instance -/

/-- **EndoScalar `Argument` instance.** The gate's algebra-generic constraints read through the
single-row cell map (`cellMap env.witnessCurr`; the next-row and coefficient families are
unused); naturality is the gate's `Gate.EndoScalar.constraints_map`. -/
def argument : Argument F where
  constraints env := Gate.EndoScalar.constraints (cellMap env.witnessCurr) (F := F)
  constraints_map f env := Gate.EndoScalar.constraints_map (F := F) f (cellMap env.witnessCurr)

end Kimchi.Lift.Gate.EndoScalar

/-!
## The Poseidon gate lift

The polynomial-algebra lift of kimchi's Poseidon gate, realized as a
`Kimchi.Lift.Argument` instance. Poseidon applies five permutation rounds per row
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

namespace Kimchi.Lift.Gate.Poseidon

open Polynomial Kimchi.Lift

variable {F : Type*} [Field F] {n N : ℕ} {ω : F}

/-! ## The layout transcription -/

/-- **Poseidon cell map.** Assemble a `Gate.Poseidon.Witness R` from the permuted register
layout: the current row supplies `s0, s4, s1, s2, s3` (in register order), the next row
supplies the output state `s5`. -/
def cellMap {R : Type*} (cur nxt : Fin wCols → R) : Gate.Poseidon.Witness R where
  s0 := (cur 0, cur 1, cur 2)
  s4 := (cur 3, cur 4, cur 5)
  s1 := (cur 6, cur 7, cur 8)
  s2 := (cur 9, cur 10, cur 11)
  s3 := (cur 12, cur 13, cur 14)
  s5 := (nxt 0, nxt 1, nxt 2)

/-- **Poseidon round-constant map.** Read the round-constant triples off a coefficient row:
`rc j = (coeff (3j), coeff (3j+1), coeff (3j+2))`. -/
def rcMap {R : Type*} (coeff : Fin coeffCols → R) : Fin 5 → R × R × R := fun j =>
  (coeff ⟨3 * (j : ℕ), by have := j.isLt; omega⟩,
   coeff ⟨3 * (j : ℕ) + 1, by have := j.isLt; omega⟩,
   coeff ⟨3 * (j : ℕ) + 2, by have := j.isLt; omega⟩)

/-- **Poseidon row witness.** The state cells at rows `i` and `i + 1` (cyclic) of a witness
table. -/
def rowWitness [NeZero n] (wTab : Fin n → Fin wCols → F) (i : Fin n) : Gate.Poseidon.Witness F :=
  cellMap (wTab i) (wTab (i + 1))

/-- **Poseidon poly witness.** The state cells as column interpolants: `columnPoly` on the
current side, its `shift` on the next side. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin wCols → F) :
    Gate.Poseidon.Witness (Polynomial F) :=
  cellMap (fun c => columnPoly ω (fun j => wTab j c))
    (fun c => shift ω (columnPoly ω (fun j => wTab j c)))

/-- **Poseidon poly round constants.** The round-constant triples as coefficient-column
interpolants. -/
noncomputable def rcPoly (ω : F) (qTab : Fin n → Fin coeffCols → F) :
    Fin 5 → Polynomial F × Polynomial F × Polynomial F :=
  rcMap (fun c => columnPoly ω (fun j => qTab j c))

/-! ## The `Argument` instance -/

/-- **Poseidon `Argument` instance**, at an MDS matrix `M` (per-curve data —
`G::sponge_params().mds`). The matrix enters every carrier through `algebraMap F R`,
which each `f : R →ₐ[F] S` fixes (`AlgHom.commutes`) — the same transport as `EndoMul`'s
endomorphism coefficient; naturality is the gate's ring-hom
`Gate.Poseidon.constraints_map` with the transported matrix rewritten back. -/
def argument (M : Gate.Poseidon.Mds F) : Argument F where
  constraints {R} _ _ env :=
    Gate.Poseidon.constraints (M.map (algebraMap F R)) (rcMap env.coeff)
      (cellMap env.witnessCurr env.witnessNext)
  constraints_map {R S} _ _ _ _ f env := by
    have hM : (M.map (algebraMap F R)).map f.toRingHom = M.map (algebraMap F S) := by
      simp [Gate.Poseidon.Mds.map]
    have h := Gate.Poseidon.constraints_map f.toRingHom (M.map (algebraMap F R))
      (rcMap env.coeff) (cellMap env.witnessCurr env.witnessNext)
    rw [hM] at h
    exact h

end Kimchi.Lift.Gate.Poseidon

/-!
## The double generic gate's quotient lift

The polynomial lift of kimchi's **double** generic gate (`generic.rs`,
`CONSTRAINTS = 2`). Commitment-free, built directly on `Kimchi.Lift.Domain`.

The row-level gate predicate is `Kimchi.Gate.Generic.Holds` (defined in
`Kimchi/Gate/Generic.lean` — the double generic gate's two cell constraints); this
file owns only the *polynomial* side — the cell map into `Gate.Generic` and the
gate's `Argument` instance over column interpolants.

## Column layout (from `generic.rs`)

A generic row carries 15 witness cells `w : Fin wCols → F` and 15 coefficient cells
`q : Fin wCols → F`. The row packs **two** generic gates: the first uses registers
`w 0, w 1, w 2` with coefficients `q 0 … q 4`; the second uses `w 3, w 4, w 5`
with coefficients `q 5 … q 9` (`q 10 … q 14` are unused here).

Source: kimchi `generic.rs` (module doc + `constraint_checks`, l.245–250):

    * w0·c0 + w1·c1 + w2·c2 + w0·w1·c3 + c4
    * w3·c5 + w4·c6 + w5·c7 + w3·w4·c8 + c9

where the `cᵢ` are the coefficients (`q` here).
-/

namespace Kimchi.Lift.Gate.Generic

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## The `Argument` instance

The generic gate plugs into the `Argument` primitive of `Kimchi.Lift` exactly like
the other five gates: the gate row `Gate.Generic R` is assembled from the current-row cells
(as `w`) and the coefficient cells (as `q`); the next-row family is unused (single-row). -/

/-- **Generic cell map.** Assemble a `Gate.Generic R` from current-row cells `cur` (→ `w`) and
coefficient cells `coeff` (→ `q`). -/
def cellMap {R : Type*} (cur : Fin wCols → R) (coeff : Fin coeffCols → R) :
    Gate.Generic R :=
  ⟨coeff, cur⟩

/-- **Generic `Argument` instance.** The gate's constraint list `Gate.Generic.constraints`
read through `cellMap`; naturality is the gate module's `Generic.constraints_map` at
the underlying ring hom. -/
def argument : Argument F where
  constraints env := (cellMap env.witnessCurr env.coeff).constraints
  constraints_map f env :=
    Gate.Generic.constraints_map f.toRingHom (cellMap env.witnessCurr env.coeff)

end Kimchi.Lift.Gate.Generic
