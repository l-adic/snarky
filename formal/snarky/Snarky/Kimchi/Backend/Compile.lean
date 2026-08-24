import Snarky.Compile
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
def kimchiCompile [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F]
    [DecidableEq F] [A : CircuitType F a avar]
    [CheckedType F (KimchiConstraint F) avar] [B : CircuitType F b bvar]
    (main : avar → CircuitM F (KimchiConstraint F) bvar) :
    BuiltWith (KimchiGate F) (AuxState F) bvar :=
  finalizeWith kimchiOps
    (buildWith kimchiOps (compileBody (a := a) (b := b) main)
      (A.size + B.size) initialAuxState)

/-- Solve a circuit at the kimchi backend (the base `solve` at `kimchiOps`): seed the
input slots, prove, decode the output. -/
def kimchiSolve [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F]
    [DecidableEq F] [A : CircuitType F a avar]
    [CheckedType F (KimchiConstraint F) avar] [B : CircuitType F b bvar]
    (main : avar → CircuitM F (KimchiConstraint F) bvar)
    (input : a) : Except EvalError (b × Assignments F) :=
  match Assignments.empty.extendPairs
      ((allocRange 0 A.size).toList.zip (A.valueToFields input).toList) with
  | .error e => .error e
  | .ok env₀ =>
    match proveWith kimchiOps (compileBody (a := a) (b := b) main)
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
    (main : avar → CircuitM F (KimchiConstraint F) bvar) :
    List (KimchiRow F) × List (AssembledGate F) × Nat :=
  let built := kimchiCompile (a := a) (b := b) main
  let rows := built.constraints.flatMap (toKimchiRows (F := F))
  makeGateData ((allocRange 0 (A.size + B.size)).toList) rows
    built.aux.wireState.unionFind

/-! ## Seam coherence at the pipeline level

The ops-record discharge (`kimchiOps_lockstep`/`kimchiOps_proveExtends`,
`Constraint.lean`), read at this module's own entry points through the generic
whole-program theorems. -/

/-- **Compile/solve allocation agreement at the kimchi backend**: a successful
prover run of the compiled body pins the compilation's counter — `kimchiCompile` and
the run behind `kimchiSolve` number their variables identically, so every variable
id the emitted rows can mention is an index the prover numbered.
`buildWith_proveWith_nextVar` at `kimchiOps_lockstep`, through the
counter-transparent queue flush. -/
theorem kimchiCompile_solve_nextVar [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F]
    [Neg F] [DecidableEq F] [A : CircuitType F a avar]
    [CheckedType F (KimchiConstraint F) avar] [B : CircuitType F b bvar]
    (main : avar → CircuitM F (KimchiConstraint F) bvar) {env₀ : Assignments F}
    {p : Proved F bvar}
    (h : proveWith kimchiOps (compileBody (a := a) (b := b) main)
        (A.size + B.size) env₀ = .ok p) :
    (kimchiCompile (a := a) (b := b) main).nextVar = p.nextVar := by
  unfold kimchiCompile
  rw [finalizeWith_nextVar]
  exact buildWith_proveWith_nextVar kimchiOps_lockstep h initialAuxState

/-- **The kimchi solve decodes its public slots** — the kimchi counterpart of the
base `solve_complete`'s slot clause: a successful solve returns a table reading the
given input at the input slots and the returned output at the output slots. The seed
survives the run and the output back-fill wrote the slots the wiring ties to the
circuit's result — `proveWith_compileBody_slots` at `kimchiOps_proveExtends`. -/
theorem kimchiSolve_publicSlots [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F]
    [Neg F] [DecidableEq F] [A : CircuitType F a avar]
    [CheckedType F (KimchiConstraint F) avar] [B : CircuitType F b bvar]
    (main : avar → CircuitM F (KimchiConstraint F) bvar) (input : a)
    {outVal : b} {env : Assignments F}
    (h : kimchiSolve (a := a) (b := b) main input = .ok (outVal, env)) :
    (∀ i (hi : i < A.size), env i = some ((A.valueToFields input)[i])) ∧
      ∀ j (hj : j < B.size),
        env (A.size + j) = some ((B.valueToFields outVal)[j]) := by
  unfold kimchiSolve at h
  rcases hseed : Assignments.empty.extendPairs
      ((allocRange 0 A.size).toList.zip (A.valueToFields input).toList)
    with e | env₀ <;> rw [hseed] at h
  · cases h
  · dsimp only at h
    rcases hp : proveWith kimchiOps (compileBody (a := a) (b := b) main)
        (A.size + B.size) env₀ with e | p <;> rw [hp] at h
    · cases h
    · dsimp only at h
      rcases hr : readVar (val := b) p.result p.assignments with e | outv <;>
        rw [hr] at h
      · cases h
      · cases h
        exact proveWith_compileBody_slots kimchiOps_proveExtends hseed hp hr

end Snarky.Kimchi
