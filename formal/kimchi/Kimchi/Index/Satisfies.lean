import Kimchi.Index.Basic
import Kimchi.Lift

/-!
# Satisfiability: a witness table against an index

What it means for a `15 × n` witness table to satisfy a circuit: every row's gate
predicate holds (`rowSatisfies` — dispatch on the row's gate type, reusing each gate's
`Holds` through the quotient layer's `rowWitness` layout transcriptions and, for
Poseidon, the `rcMap` round-constant view of the coefficient row), the copy constraints
hold along the wiring (every permuted cell equals its wired-to cell — trivially true on
identity-wired cells, so quantified over the whole grid), and the public rows pin the
first witness column to the public input.

**There is no hand-written checker.** `Satisfies` is the definition; executability is a
derived `Decidable` instance — every gate's `Holds` is `∀ e ∈ constraints, e = 0`, so
each branch is decided by `List.decidableBAll`, and the conjunction over rows and cells
by the `Fintype` instances. `decide` is the checker, generated from the predicate
itself; fixture scripts evaluate it and nothing else.
-/

namespace Kimchi.Index

open Kimchi.Lift
open Kimchi.Lift.Gate

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ} [NeZero n]

/-- The public value at a row: the input for the public rows, zero beyond them. -/
def pubAt (idx : Index F n) (pub : Fin idx.publicCount → F) (i : Fin n) : F :=
  if h : (i : ℕ) < idx.publicCount then pub ⟨(i : ℕ), h⟩ else 0

/-- Row `i` satisfies its gate: dispatch on the stored gate type. `zero` rows constrain
nothing; `generic` reads its coefficients and current-row cells with the row's public
value folded in (`Generic.withPublic` — the layout knowledge lives with the gate); the
remaining gates go through their
quotient-layer `rowWitness` layout transcriptions (two-row where the gate spans two
rows); Poseidon's round constants are its coefficient row (`rcMap`); `endoMul` consumes
the index's `endoBase`. -/
def rowSatisfies (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (i : Fin n) : Prop :=
  match (idx.gates i).typ with
  | .zero => True
  | .generic =>
      Gate.Generic.Holds (Gate.Generic.withPublic ⟨idx.coeffTable i, wTab i⟩
        (pubAt idx pub i))
  | .poseidon =>
      Gate.Poseidon.Holds idx.mds (Poseidon.rcMap (idx.coeffTable i))
        (Poseidon.rowWitness wTab i)
  | .completeAdd => Gate.AddComplete.Holds (AddComplete.rowWitness wTab i)
  | .varBaseMul => Gate.VarBaseMul.Holds (VarBaseMul.rowWitness wTab i)
  | .endoMul => Gate.EndoMul.Holds idx.endoBase (EndoMul.rowWitness wTab i)
  | .endoScalar => Gate.EndoScalar.Holds (EndoScalar.rowWitness wTab i)

/-- The value of a permuted cell: column `c.1` (of the seven) at row `c.2`. -/
def cellValue (wTab : Fin n → Fin wCols → F) (c : Fin permCols × Fin n) : F :=
  wTab c.2 (Fin.castLE (by omega) c.1)

/-- A witness table satisfies an index at a public input: every row's gate holds, every
permuted cell equals its wired-to cell, and the public rows pin the first column. -/
def Satisfies (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) : Prop :=
  (∀ i, rowSatisfies idx pub wTab i)
    ∧ (∀ c : Fin permCols × Fin n, cellValue wTab (idx.wiringMap c) = cellValue wTab c)
    ∧ (∀ i : Fin idx.publicCount,
        wTab ⟨(i : ℕ), by have h1 := idx.public_le; have h2 := idx.zk_le; omega⟩ 0 = pub i)

instance (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (i : Fin n) :
    Decidable (rowSatisfies idx pub wTab i) := by
  unfold rowSatisfies
  split <;> infer_instance

instance (idx : Index F n) (pub : Fin idx.publicCount → F) (wTab : Fin n → Fin wCols → F) :
    Decidable (Satisfies idx pub wTab) := by
  unfold Satisfies
  infer_instance

end Kimchi.Index
