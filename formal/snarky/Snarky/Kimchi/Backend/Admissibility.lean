import Snarky.Kimchi.Constraint
import Kimchi.Columns

/-!
# Admissibility of a source for the wired fragment

The definitions the scope checker decides and the wired fragment's lifting theorem assumes:
where each constraint's gate rows place its operands, the variables those operands name, and
the scoping condition on a source list, its public variables and the counter. They are
executable data over the production constraints, shared by the checker and the proofs, and
import no part of the lowering's proof development.

## Main definitions

- `KimchiConstraint.rowOperands`: the operands a constraint's gate rows place, row by row and
  cell by cell.
- `KimchiConstraint.termVars`, `KimchiConstraint.unwiredVars`, `occurrences`: the variables a
  constraint's operands name, its bare operands in the unwired columns, and every variable a
  source and its public variables name.
- `KimchiConstraint.Wired`, `KimchiConstraint.Wired.Scoped`: membership in the wired fragment,
  a Poseidon block of the shape `5w + 1` and cells in the unwired columns bare or empty, and
  the scoping condition: every constraint wired, every named variable below the counter, and
  every operand of an unwired column occurring once.
-/

open Kimchi

namespace Snarky.Kimchi

open Snarky

variable {F : Type}

variable [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]

/-! ## Operand layouts -/

/-- The variables an operand's affine form names, in term order. -/
def _root_.Snarky.CVar.termVars (x : CVar F) : List Variable :=
  x.reduceToAffineExpression.terms.map Prod.fst

/-- The variables a `Basic` constraint's operands name, with repetition. -/
def _root_.Snarky.Basic.termVars : Basic F → List Variable
  | .r1cs a b c => a.termVars ++ b.termVars ++ c.termVars
  | .equal a b => a.termVars ++ b.termVars
  | .square a b => a.termVars ++ b.termVars
  | .boolean x => x.termVars

/-- The variable a bare-variable operand names; `none` for any other form. -/
def _root_.Snarky.CVar.var? (x : CVar F) : Option Variable :=
  match x with
  | .var v => some v
  | _ => none

/-- A row's fifteen cells from a prefix of placed operands, the rest empty. -/
def cellsOf (ops : List (Option (FVar F))) : Vector (Option (FVar F)) wCols :=
  ⟨⟨ops.take wCols ++ List.replicate (wCols - (ops.take wCols).length) none⟩, by
    show (ops.take wCols ++ List.replicate (wCols - (ops.take wCols).length) none).length = wCols
    simp only [List.length_append, List.length_replicate, List.length_take]
    omega⟩

/-- The operands a Poseidon block's rows place: five states per row in the permuted register
order `s0 s4 s1 s2 s3`, a trailing single state in the terminal row's first three cells, and
nothing for a shorter tail, as the reducer chunks them. -/
def Poseidon.rowOperandsList :
    List (FVar F × FVar F × FVar F) → List (Vector (Option (FVar F)) wCols)
  | [] => []
  | [s] => [cellsOf (PoseidonConstraint.finalCells s)]
  | q0 :: q1 :: q2 :: q3 :: q4 :: rest =>
    cellsOf (PoseidonConstraint.windowCells q0 q1 q2 q3 q4) :: rowOperandsList rest
  | _ => []

/-- The operands a constraint's gate rows place, row by row and cell by cell, `none` for an
empty cell: what each reducer writes, before reduction. A `Basic` constraint places no gate
row. -/
def KimchiConstraint.rowOperandsList : KimchiConstraint F → List (Vector (Option (FVar F)) wCols)
  | .basic _ => []
  | .addComplete c => [cellsOf (c.operands.toList.map some)]
  | .poseidon c => Poseidon.rowOperandsList c.state
  | .varBaseMul rounds => rounds.flatMap fun r => [cellsOf r.cellsA, cellsOf r.cellsB]
  | .endoScalar rounds => rounds.map fun r => cellsOf (r.operands.toList.map some)
  | .endoMul c =>
    (c.state.map fun r => cellsOf ([r.t.x, r.t.y, r.inv].map some ++
      none :: [r.p.x, r.p.y, r.nAcc, r.r.x, r.r.y, r.s1, r.s3, r.bit0, r.bit1, r.bit2,
        r.bit3].map some)) ++
    [cellsOf (none :: none :: none :: none :: [c.s.x, c.s.y, c.nAcc].map some)]
  | .pad vs => [cellsOf (padCells vs)]

/-- The rows a constraint's gate emits. -/
def KimchiConstraint.rowCount (c : KimchiConstraint F) : Nat :=
  c.rowOperandsList.length

/-- The placed operands as a vector of rows: position `(i, j)` is row `i`'s cell `j`. -/
def KimchiConstraint.rowOperands (c : KimchiConstraint F) :
    Vector (Vector (Option (FVar F)) wCols) c.rowCount :=
  ⟨⟨c.rowOperandsList⟩, rfl⟩

/-- The variables a cell's operand names; none for an empty cell. -/
def cellTerms : Option (FVar F) → List Variable
  | some x => x.termVars
  | none => []

/-- The variables a constraint's operands name, with repetition: a `Basic` constraint's
operands, or every term of every operand a gate's rows place. -/
def KimchiConstraint.termVars : KimchiConstraint F → List Variable
  | .basic b => b.termVars
  | c => c.rowOperands.toList.flatMap fun row => row.toList.flatMap cellTerms

/-- The bare operands a constraint places in the unwired columns `7` to `14`. -/
def KimchiConstraint.unwiredVars (c : KimchiConstraint F) : List Variable :=
  c.rowOperands.toList.flatMap fun row =>
    (row.toList.drop permCols).filterMap fun o => o.bind CVar.var?

/-! ## The fragment -/

/-- The fragment's condition on a constructor. Every constructor is admitted; a Poseidon block
under the shape `5w + 1`, which places every state and keeps every window's successor inside
the block. -/
private def KimchiConstraint.Admitted : KimchiConstraint F → Prop
  | .poseidon c => c.state.length % 5 = 1
  | _ => True

private instance KimchiConstraint.decidableAdmitted (c : KimchiConstraint F) :
    Decidable c.Admitted := by
  unfold KimchiConstraint.Admitted
  split <;> infer_instance

/-- A cell's operand is bare, or the cell is empty. -/
def bareCell : Option (FVar F) → Prop
  | some x => x.var?.isSome = true
  | none => True

private instance decidableBareCell (o : Option (FVar F)) : Decidable (bareCell o) := by
  unfold bareCell
  split <;> infer_instance

/-- A constraint the lowering wires: a Poseidon block of the shape `5w + 1`, and any
constructor's operands in the unwired columns `7` to `14` bare variables. -/
def KimchiConstraint.Wired (c : KimchiConstraint F) : Prop :=
  c.Admitted ∧ ∀ row ∈ c.rowOperands.toList, ∀ j : Fin wCols, permCols ≤ j.val → bareCell row[j]

instance KimchiConstraint.decidableWired (c : KimchiConstraint F) : Decidable c.Wired := by
  unfold KimchiConstraint.Wired
  infer_instance

/-- Every variable the source and the public variables name, with repetition: each
constraint's term variables in order, then the public variables. -/
def occurrences (source : List (KimchiConstraint F)) (publicVars : List Variable) :
    List Variable :=
  source.flatMap KimchiConstraint.termVars ++ publicVars

/-- The scoping condition under which any table satisfying the fragment's index determines
a valuation: every constraint is wired, every named variable is below the counter, and every
operand of an unwired column occurs exactly once among the term occurrences and the public
variables. -/
structure KimchiConstraint.Wired.Scoped (nv : Variable) (source : List (KimchiConstraint F))
    (publicVars : List Variable) : Prop where
  /-- Every constraint is in the fragment. -/
  wired : ∀ c ∈ source, c.Wired
  /-- Every variable the source or the public input names is below the counter. -/
  below : ∀ v ∈ occurrences source publicVars, v < nv
  /-- Every operand of an unwired column occurs exactly once among the term occurrences and
  the public variables. -/
  unwiredOnce : ∀ c ∈ source, ∀ v ∈ c.unwiredVars, (occurrences source publicVars).count v = 1

instance (nv : Variable) (source : List (KimchiConstraint F)) (publicVars : List Variable) :
    Decidable (KimchiConstraint.Wired.Scoped nv source publicVars) :=
  decidable_of_iff
    ((∀ c ∈ source, c.Wired) ∧ (∀ v ∈ occurrences source publicVars, v < nv) ∧
      ∀ c ∈ source, ∀ v ∈ c.unwiredVars, (occurrences source publicVars).count v = 1)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

end Snarky.Kimchi
