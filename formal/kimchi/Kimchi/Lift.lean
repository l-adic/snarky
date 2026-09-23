import Kimchi.Columns
import Kimchi.Domain
import Kimchi.Shifted
import Kimchi.Gate.AddComplete
import Kimchi.Gate.VarBaseMul
import Kimchi.Gate.EndoMul
import Kimchi.Gate.EndoScalar
import Kimchi.Gate.Poseidon
import Kimchi.Gate.Generic

/-!
# The gate-argument primitive

The polynomial-lift interface a gate's constraints are read through. Everything lives over an
abstract field `F` with a primitive `n`-th root of unity `ω` supplied as a hypothesis; no gate
formula is restated here.

## The `ArgumentEnv` / `Argument` pair

This pair mirrors kimchi's `argument.rs`.

* `ArgumentEnv R` is the cells a gate's constraints may read at a row: the current-row
  witness cells, the next-row witness cells (cyclic `i + 1`), and the current row's
  coefficient cells.
* `Argument F` is one gate's constraint list, defined over every commutative `F`-algebra `R`,
  together with its naturality square `constraints_map` along `F`-algebra homomorphisms.
  Upstream runs one generic constraint function both on field values (the row checks) and on
  symbolic expressions (the quotient) and gets their agreement by parametricity; here that
  agreement is a proof obligation.

Genericity over `F`-algebras rather than rings absorbs gate parameters (the EndoMul
endomorphism coefficient, the EndoScalar cubic coefficients, the Poseidon MDS matrix): each
enters as `algebraMap F R` of a fixed element, which every `F`-algebra hom fixes.

`rowEnv` (the cells of row `i`) and `polyEnv` (the column interpolants, with `shift` on the
next-row side) are the two carrier instantiations. `Argument.bridge` — evaluation at `ω ^ i`
carries `polyEnv` to `rowEnv` — is the one evaluation bridge; a gate reaches its own by
supplying `constraints_map`.

## Gate instances

Each gate section below defines a `cellMap` reading the gate's column layout and an
`argument` instance. The layouts transcribe kimchi's `complete_add.rs`, `varbasemul.rs`,
`endosclmul.rs`, `endomul_scalar.rs`, `poseidon.rs` and `generic.rs`.
-/

namespace Kimchi

/-! ## The column embeddings

The wired columns are the first `permCols` witness columns, and the σ batch carries the
first `sigmaRows` of the `permCols` σ columns (the last is consumed by the linearization).
These `abbrev`s name every inclusion between the column index types; each is definitionally
the anonymous `⟨i, _⟩`. -/

/-- Wired column `i` as a witness column. -/
abbrev permCol (i : Fin permCols) : Fin wCols := ⟨i, by omega⟩

/-- Batched σ column `i` as a witness column. -/
abbrev sigmaCol (i : Fin sigmaRows) : Fin wCols := ⟨i, by omega⟩

/-- Batched σ column `i` among the `permCols` σ columns. -/
abbrev sigmaPermCol (i : Fin sigmaRows) : Fin permCols := ⟨i, by omega⟩

end Kimchi

namespace Kimchi.Lift

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}
/-! ## The cell environment -/

/-- The cells a gate's constraints may read at a row: current-row witness, next-row witness
(cyclic `i + 1`), and current-row coefficients. -/
structure ArgumentEnv (R : Type u) where
  /-- The current-row witness cells. -/
  witnessCurr : Fin wCols → R
  /-- The next-row witness cells, cyclic `i + 1`. -/
  witnessNext : Fin wCols → R
  /-- The current row's coefficient cells. -/
  coeff : Fin coeffCols → R

/-- Apply `f` to every cell. -/
def ArgumentEnv.map {R S : Type u} (f : R → S) (env : ArgumentEnv R) : ArgumentEnv S :=
  ⟨f ∘ env.witnessCurr, f ∘ env.witnessNext, f ∘ env.coeff⟩

/-- The cells at row `i` of the witness table `wTab` and coefficient table `qTab`. -/
private def rowEnv [NeZero n] (wTab : Fin n → Fin wCols → F) (qTab : Fin n → Fin coeffCols → F)
    (i : Fin n) : ArgumentEnv F :=
  ⟨wTab i, wTab (i + 1), qTab i⟩

/-- The column interpolants of the tables, with `shift` on the next-row side. -/
noncomputable def polyEnv (ω : F) (wTab : Fin n → Fin wCols → F)
    (qTab : Fin n → Fin coeffCols → F) :
    ArgumentEnv (Polynomial F) :=
  ⟨fun c => columnPoly ω (fun j => wTab j c),
   fun c => shift ω (columnPoly ω (fun j => wTab j c)),
   fun c => columnPoly ω (fun j => qTab j c)⟩

/-- Evaluating `polyEnv` at the node `ω ^ i` gives `rowEnv` at `i`: `eval_columnPoly` on the
current and coefficient sides, `eval_shift_columnPoly` on the next side. -/
private theorem polyEnv_map_aeval [NeZero n] (hω : IsPrimitiveRoot ω n)
    (wTab : Fin n → Fin wCols → F) (qTab : Fin n → Fin coeffCols → F) (i : Fin n) :
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

/-- **The `Argument` primitive.** One gate's constraint list, read from an `ArgumentEnv R` for
every commutative `F`-algebra `R`, with its naturality square along `F`-algebra homs. Gate
parameters enter through `algebraMap F R`, which every `R →ₐ[F] S` fixes (`AlgHom.commutes`). -/
structure Argument (F : Type u) [Field F] where
  /-- The gate's constraint expressions over the carrier `R`. -/
  constraints : ∀ {R : Type u} [CommRing R] [Algebra F R], ArgumentEnv R → List R
  /-- Naturality: mapping the constraints along `f` reads them from the mapped cells. -/
  constraints_map : ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
      (f : R →ₐ[F] S) (env : ArgumentEnv R),
    (constraints env).map f = constraints (env.map f)

/-- **Evaluation bridge.** Evaluating a gate's constraints over `polyEnv` at the node `ω ^ i`
gives its constraints over `rowEnv` at `i`: `constraints_map` at `aeval (ω ^ i)`, pasted onto
`polyEnv_map_aeval`. -/
theorem Argument.bridge [NeZero n] (G : Argument F) (hω : IsPrimitiveRoot ω n)
    (wTab : Fin n → Fin wCols → F) (qTab : Fin n → Fin coeffCols → F) (i : Fin n) :
    (G.constraints (polyEnv ω wTab qTab)).map (·.eval (ω ^ (i : ℕ)))
      = G.constraints (rowEnv wTab qTab i) := by
  have hfun : (fun E : Polynomial F => E.eval (ω ^ (i : ℕ)))
      = ⇑(aeval (ω ^ (i : ℕ)) : Polynomial F →ₐ[F] F) := by
    funext E; rw [Polynomial.coe_aeval_eq_eval]
  rw [hfun, G.constraints_map, polyEnv_map_aeval hω]

end Kimchi.Lift

/-!
## The CompleteAdd gate lift

A single-row gate: the cell map reads the current row only.
-/

namespace Kimchi.Lift.Gate.AddComplete

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## Column layout and the cell map

A CompleteAdd row occupies witness columns `0`–`10`; the remaining columns are unused.

```
|  0 |  1 |  2 |  3 |  4 |  5 |  6  |   7   | 8 |  9   |   10   |
| x1 | y1 | x2 | y2 | x3 | y3 | inf | sameX | s | infZ | x21Inv |
```
-/

/-- The CompleteAdd witness read off a row `cur`. -/
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

/-- The CompleteAdd witness at row `i` of the table `wTab`. -/
def rowWitness (wTab : Fin n → Fin wCols → F) (i : Fin n) : Gate.AddComplete.Witness F :=
  cellMap (wTab i)

/-- The CompleteAdd witness whose cells are the column interpolants. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin wCols → F) :
    Gate.AddComplete.Witness (Polynomial F) :=
  cellMap (fun c => columnPoly ω (fun j => wTab j c))

/-! ## The `Argument` instance -/

/-- The CompleteAdd `Argument`: naturality is `Gate.AddComplete.constraints_map` at the
underlying ring hom. -/
def argument : Argument F where
  constraints env := Gate.AddComplete.constraints (cellMap env.witnessCurr)
  constraints_map f env := Gate.AddComplete.constraints_map f.toRingHom (cellMap env.witnessCurr)

end Kimchi.Lift.Gate.AddComplete

/-!
## The VarBaseMul gate lift

A two-row gate: the cell map reads row `i` and row `i + 1`, so the polynomial witness takes
the next-row side through `shift`. The next row is cyclic, which agrees with the intended
reading on every occupied row since a two-row gate never sits on the last domain row.
-/

namespace Kimchi.Lift.Gate.VarBaseMul

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## Column layout and the cell map -/

/-- The VarBaseMul witness read off the rows `cur` (row `i`) and `nxt` (row `i + 1`):

```
row i  : xT yT x0 y0  n  n'  _  x1 y1 x2 y2 x3 y3 x4 y4
row i+1: x5 y5 b0 b1 b2 b3 b4 s0 s1 s2 s3 s4  _  _  _
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

/-- The VarBaseMul witness at rows `i` and `i + 1` of the table `wTab`. -/
def rowWitness [NeZero n] (wTab : Fin n → Fin wCols → F) (i : Fin n) :
    Gate.VarBaseMul.Witness F :=
  cellMap (wTab i) (wTab (i + 1))

/-- The VarBaseMul witness over the column interpolants, shifted on the next-row side. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin wCols → F) :
    Gate.VarBaseMul.Witness (Polynomial F) :=
  cellMap (fun c => columnPoly ω (fun j => wTab j c))
    (fun c => shift ω (columnPoly ω (fun j => wTab j c)))

/-! ## The `Argument` instance -/

/-- The VarBaseMul `Argument`: naturality is `Gate.VarBaseMul.constraints_map` at the
underlying ring hom. -/
def argument : Argument F where
  constraints env := Gate.VarBaseMul.constraints (cellMap env.witnessCurr env.witnessNext)
  constraints_map f env :=
    Gate.VarBaseMul.constraints_map f.toRingHom (cellMap env.witnessCurr env.witnessNext)

end Kimchi.Lift.Gate.VarBaseMul

/-!
## The EndoMul gate lift

A two-row gate like VarBaseMul: the inputs, the intermediate point, the slopes and the bits sit
on row `i`, the outputs `xS, yS, n'` on row `i + 1`. The endomorphism coefficient `endo`
enters as `algebraMap F R endo`.

The distinct-point constraint's `inv` cell is read from current-row column `2`, which no
other cell uses. The bridge holds for any column choice, since one
`cellMap` defines both witnesses; the column matters only for matching kimchi's concrete
circuit table, which this layer never pins.
-/

namespace Kimchi.Lift.Gate.EndoMul

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## The cell map -/

/-- The EndoMul witness read off the rows `cur` (row `i`) and `nxt` (row `i + 1`). -/
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

/-- The EndoMul witness at rows `i` and `i + 1` of the table `wTab`. -/
def rowWitness [NeZero n] (wTab : Fin n → Fin wCols → F) (i : Fin n) :
    Gate.EndoMul.Witness F :=
  cellMap (wTab i) (wTab (i + 1))

/-- The EndoMul witness over the column interpolants, shifted on the next-row side. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin wCols → F) :
    Gate.EndoMul.Witness (Polynomial F) :=
  cellMap (fun c => columnPoly ω (fun j => wTab j c))
    (fun c => shift ω (columnPoly ω (fun j => wTab j c)))

/-! ## The `Argument` instance -/

/-- The EndoMul `Argument` at the endomorphism coefficient `endo`: naturality is
`Gate.EndoMul.constraints_map`, with the transported coefficient fixed by `AlgHom.commutes`. -/
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

A single-row gate: the input `n0` and output `n8` share a row, and chaining `n8` into the next
row's `n0` is left to the permutation. Layout:

```
|  0 |  1 |  2 |  3 |  4 |  5 |  6 |  7 |  8 |  9 | 10 | 11 | 12 | 13 | 14 |
| n0 | n8 | a0 | b0 | a8 | b8 | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 |    |
```

where each `xi` is a two-bit crumb.
-/

namespace Kimchi.Lift.Gate.EndoScalar

open Polynomial Kimchi.Lift

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## Column layout and the cell map -/

/-- The EndoScalar witness read off a row `cur`. The crumbs are a literal list, so the
accumulator folds unfold directly on it. -/
def cellMap {R : Type*} (cur : Fin wCols → R) : Gate.EndoScalar.Witness R where
  n0 := cur 0
  n8 := cur 1
  a0 := cur 2
  b0 := cur 3
  a8 := cur 4
  b8 := cur 5
  crumbs := [cur 6, cur 7, cur 8, cur 9, cur 10, cur 11, cur 12, cur 13]

/-- The EndoScalar witness at row `i` of the table `wTab`. -/
def rowWitness (wTab : Fin n → Fin wCols → F) (i : Fin n) : Gate.EndoScalar.Witness F :=
  cellMap (wTab i)

/-- The EndoScalar witness whose cells are the column interpolants. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin wCols → F) :
    Gate.EndoScalar.Witness (Polynomial F) :=
  cellMap (fun c => columnPoly ω (fun j => wTab j c))

/-! ## The `Argument` instance -/

/-- The EndoScalar `Argument`: naturality is `Gate.EndoScalar.constraints_map`. -/
def argument : Argument F where
  constraints env := Gate.EndoScalar.constraints (cellMap env.witnessCurr) (F := F)
  constraints_map f env := Gate.EndoScalar.constraints_map (F := F) f (cellMap env.witnessCurr)

end Kimchi.Lift.Gate.EndoScalar

/-!
## The Poseidon gate lift

A two-row gate applying five permutation rounds: the current row holds the states `s0`–`s4`,
the next row the output state `s5`, and the coefficient row the round constants. The layout is
permuted, with `s4` stored before `s1`:

```
|  0 |  1 |  2 |  3 |  4 |  5 |  6 |  7 |  8 |  9 | 10 | 11 | 12 | 13 | 14 |
| s0 | s0 | s0 | s4 | s4 | s4 | s1 | s1 | s1 | s2 | s2 | s2 | s3 | s3 | s3 |
| s5 | s5 | s5 |    |    |    |    |    |    |    |    |    |    |    |    |
```
-/

namespace Kimchi.Lift.Gate.Poseidon

open Polynomial Kimchi.Lift

variable {F : Type*} [Field F] {n N : ℕ} {ω : F}

/-! ## The layout transcription -/

/-- The Poseidon witness read off the rows `cur` (row `i`) and `nxt` (row `i + 1`). -/
def cellMap {R : Type*} (cur nxt : Fin wCols → R) : Gate.Poseidon.Witness R where
  s0 := (cur 0, cur 1, cur 2)
  s4 := (cur 3, cur 4, cur 5)
  s1 := (cur 6, cur 7, cur 8)
  s2 := (cur 9, cur 10, cur 11)
  s3 := (cur 12, cur 13, cur 14)
  s5 := (nxt 0, nxt 1, nxt 2)

/-- The round constants of round `j`: coefficient cells `3j`, `3j + 1`, `3j + 2`. -/
def rcMap {R : Type*} (coeff : Fin coeffCols → R) : Fin 5 → R × R × R := fun j =>
  (coeff ⟨3 * (j : ℕ), by have := j.isLt; omega⟩,
   coeff ⟨3 * (j : ℕ) + 1, by have := j.isLt; omega⟩,
   coeff ⟨3 * (j : ℕ) + 2, by have := j.isLt; omega⟩)

/-- The Poseidon witness at rows `i` and `i + 1` of the table `wTab`. -/
def rowWitness [NeZero n] (wTab : Fin n → Fin wCols → F) (i : Fin n) : Gate.Poseidon.Witness F :=
  cellMap (wTab i) (wTab (i + 1))

/-- The Poseidon witness over the column interpolants, shifted on the next-row side. -/
noncomputable def polyWitness (ω : F) (wTab : Fin n → Fin wCols → F) :
    Gate.Poseidon.Witness (Polynomial F) :=
  cellMap (fun c => columnPoly ω (fun j => wTab j c))
    (fun c => shift ω (columnPoly ω (fun j => wTab j c)))

/-- The round constants over the coefficient-column interpolants. -/
noncomputable def rcPoly (ω : F) (qTab : Fin n → Fin coeffCols → F) :
    Fin 5 → Polynomial F × Polynomial F × Polynomial F :=
  rcMap (fun c => columnPoly ω (fun j => qTab j c))

/-! ## The `Argument` instance -/

/-- The Poseidon `Argument` at the MDS matrix `M`: naturality is
`Gate.Poseidon.constraints_map`, with the transported matrix fixed by the algebra hom. -/
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
## The generic gate lift

A single-row gate reading the current-row witness cells as `w` and the coefficient cells as
`q`; the row packs two generic gates (see `Gate.Generic.constraints`).
-/

namespace Kimchi.Lift.Gate.Generic

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## The `Argument` instance -/

/-- The generic gate row with witness cells `cur` and coefficient cells `coeff`. -/
def cellMap {R : Type*} (cur : Fin wCols → R) (coeff : Fin coeffCols → R) :
    Gate.Generic R :=
  ⟨coeff, cur⟩

/-- The generic `Argument`: naturality is `Gate.Generic.constraints_map` at the underlying
ring hom. -/
def argument : Argument F where
  constraints env := (cellMap env.witnessCurr env.coeff).constraints
  constraints_map f env :=
    Gate.Generic.constraints_map f.toRingHom (cellMap env.witnessCurr env.coeff)

end Kimchi.Lift.Gate.Generic
