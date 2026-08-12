import Snarky.Backend.Compile
import Snarky.Kimchi.Backend.Assemble

/-!
# Whole-circuit compilation at the kimchi backend

The base `compileBody` program is backend-generic (it speaks `BasicSystem`), so the
kimchi entry points are the generic interpreters at `kimchiOps` on exactly the same
op tree the base `compile`/`solve` run: `kimchiCompile` builds and flushes the queue,
`kimchiSolve` seeds the public-input slots and proves, and `kimchiGateData` carries a
compiled circuit through row dispatch and the CS assembly — the full pure pipeline
the CS-equality seam compares against the fixture corpus. Public slots are the base
convention: inputs at `0 … A.size−1`, outputs following, and all of them are the
assembly's public-input rows.
-/

namespace Snarky.Kimchi

open Snarky

variable {F : Type} {a b avar bvar : Type}

/-- Compile a circuit at the kimchi backend (the base `compile` at `kimchiOps`,
queue flushed). -/
private def kimchiCompile [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F]
    [DecidableEq F] [A : CircuitType F a avar]
    [CheckedType F (KimchiConstraint F) avar] [B : CircuitType F b bvar]
    (rc : ℕ → F × F × F) (main : avar → CircuitM F (KimchiConstraint F) bvar) :
    BuiltWith (KimchiGate F) (AuxState F) bvar :=
  finalizeWith (kimchiOps rc)
    (buildWith (kimchiOps rc) (compileBody (a := a) (b := b) main)
      (A.size + B.size) initialAuxState)

/-- Solve a circuit at the kimchi backend (the base `solve` at `kimchiOps`): seed the
input slots, prove, decode the output. -/
def kimchiSolve [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F]
    [DecidableEq F] [A : CircuitType F a avar]
    [CheckedType F (KimchiConstraint F) avar] [B : CircuitType F b bvar]
    (rc : ℕ → F × F × F) (main : avar → CircuitM F (KimchiConstraint F) bvar)
    (input : a) : Except EvalError (b × Assignments F) :=
  match Assignments.empty.extendPairs
      ((allocRange 0 A.size).toList.zip (A.valueToFields input).toList) with
  | .error e => .error e
  | .ok env₀ =>
    match proveWith (kimchiOps rc) (compileBody (a := a) (b := b) main)
        (A.size + B.size) env₀ with
    | .error e => .error e
    | .ok p =>
      match readVar (val := b) p.result p.assignments with
      | .error e => .error e
      | .ok outVal => .ok (outVal, p.assignments)

/-- The full pure pipeline: compile, dispatch the gates to rows, and assemble —
returning the rows (public rows included), the gate table, and the public size. -/
def kimchiGateData [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F]
    [DecidableEq F] [A : CircuitType F a avar]
    [CheckedType F (KimchiConstraint F) avar] [B : CircuitType F b bvar]
    (rc : ℕ → F × F × F) (main : avar → CircuitM F (KimchiConstraint F) bvar) :
    List (KimchiRow F) × List (AssembledGate F) × Nat :=
  let built := kimchiCompile (a := a) (b := b) rc main
  let rows := built.constraints.flatMap (toKimchiRows (F := F))
  makeGateData ((allocRange 0 (A.size + B.size)).toList) rows
    built.aux.wireState.unionFind

end Snarky.Kimchi
