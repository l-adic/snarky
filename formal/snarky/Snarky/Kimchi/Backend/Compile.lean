import Snarky.Compile
import Snarky.Kimchi.Backend.Assemble

/-!
# Whole-circuit compilation at the kimchi backend

The base `compileBody` program is backend-generic (it speaks `BasicSystem`), so the
kimchi entry points run the reduction as a POST-PASS over what the base `compile`
and `solve` produce, rather than through a per-constraint hook inside the
interpreters: `kimchiCompile` folds the builder's reduction over the compiled
constraint list, `kimchiSolve` folds the prover's reduction over the same list from
the table a base solve returned, and `kimchiGateData` carries a compiled circuit
through row dispatch and the CS assembly — the full pure pipeline the CS-equality
seam compares against the fixture corpus.

The reduction's internal variables come from the compiled system's final counter,
which is the prover's too (`prove_build_agrees`), so the two folds see the same
counter and walk the same list in emission order. They land above the circuit's own
variables instead of interleaved with them, which renames variables and leaves the
row sequence alone.
-/

namespace Snarky.Kimchi

open Snarky

variable {F : Type} {a b avar bvar : Type}

/-- A compiled kimchi circuit: the result, the gates in emission order, the counter
past every variable either side numbered, and the reduction's final aux state. -/
structure KimchiBuilt (F : Type) (α : Type) where
  /-- The compiled program's result. -/
  result : α
  /-- The emitted gates, in order. -/
  gates : List (KimchiGate F)
  /-- The next-variable counter after the reduction. -/
  nextVar : Variable
  /-- The reduction's aux state: gate queue, wiring, constant cache. -/
  aux : AuxState F

/-- One constraint's builder-side reduction: the generic rows it flushed, then the
wrapped gate. -/
def reduceStep [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F] [DecidableEq F]
    (nv : Variable) (aux : AuxState F) (con : KimchiConstraint F) :
    List (KimchiGate F) × Variable × AuxState F :=
  let red := reduceAsBuilder nv aux (KimchiConstraint.reduce con)
  (red.2.1.map .plonk ++ [red.1], red.2.2.1, red.2.2.2)

/-- Fold the builder's reduction over a compiled constraint list. -/
def reduceGates [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F] [DecidableEq F] :
    List (KimchiConstraint F) → Variable → AuxState F →
      List (KimchiGate F) × Variable × AuxState F
  | [], nv, aux => ([], nv, aux)
  | con :: cons, nv, aux =>
    let step := reduceStep nv aux con
    let rest := reduceGates cons step.2.1 step.2.2
    (step.1 ++ rest.1, rest.2.1, rest.2.2)

/-- Fold the prover's reduction over the same list, filling the internal variables. -/
def reduceTable [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F] [DecidableEq F] :
    List (KimchiConstraint F) → ProverReductionState F →
      Except EvalError (ProverReductionState F)
  | [], s => .ok s
  | con :: cons, s =>
    match reduceAsProver s (KimchiConstraint.reduce con) with
    | .error e => .error e
    | .ok (_, s') => reduceTable cons s'

/-- A built circuit reduced to kimchi gates: the builder's reduction folded over the
constraint list from the build's counter, the odd queued constraint flushed into one more
packed row. -/
def reduceBuilt [Field F] [DecidableEq F] {α : Type} (built : Built (KimchiConstraint F) α) :
    KimchiBuilt F α :=
  let red := reduceGates built.constraints built.nextVar initialAuxState
  let flush := (finalizeGateQueue red.2.2.queuedGenericGate).map KimchiGate.plonk
  ⟨built.result, red.1 ++ flush.toList, red.2.1, { red.2.2 with queuedGenericGate := none }⟩

/-- Compile a circuit at the kimchi backend: the base compilation, reduced. -/
def kimchiCompile [Field F] [DecidableEq F] [CircuitType F a avar]
    [CheckedType F (KimchiConstraint F) a avar] [CircuitType F b bvar]
    (main : avar → CircuitM F (KimchiConstraint F) bvar) : KimchiBuilt F (bvar × bvar) :=
  reduceBuilt (compile (a := a) (b := b) main)

/-- A built circuit's table completed by the prover's reduction: the internal variables
the gates introduced, from the build's counter. -/
def reduceSolved [Field F] [DecidableEq F] {α : Type} (built : Built (KimchiConstraint F) α)
    (env : Assignments F) : Except EvalError (Assignments F) :=
  match reduceTable built.constraints ⟨built.nextVar, env⟩ with
  | .error e => .error e
  | .ok s => .ok s.assignments

/-- Solve a circuit at the kimchi backend: the base solve, then the prover's
reduction over the compiled constraints from the compilation's counter. -/
def kimchiSolve [Field F] [DecidableEq F] [CircuitType F a avar]
    [CheckedType F (KimchiConstraint F) a avar] [CircuitType F b bvar]
    (main : avar → CircuitM F (KimchiConstraint F) bvar) (input : a) :
    Except EvalError (b × Assignments F) :=
  match solve (a := a) (b := b) main input with
  | .error e => .error e
  | .ok (outVal, env) =>
    match reduceSolved (compile (a := a) (b := b) main) env with
    | .error e => .error e
    | .ok env' => .ok (outVal, env')

/-- The variables backing a bundle of plain variables — the witnessed public output
slots, whose ids the assembly needs but whose numbering it does not care about. -/
def bundleVars [Add F] [Mul F] [Zero F] [CircuitType F b bvar] (v : bvar) :
    List Variable :=
  (CircuitType.varToFields (val := b) v).toList.filterMap fun (cv : CVar F) =>
    match cv with
    | CVar.var w => some w
    | _ => none

/-- The rows and the assembled gate table of a reduced circuit at given public variables:
the gates dispatched to rows, the wiring assembled over the reduction's union-find. -/
def gateDataOf [Field F] [DecidableEq F] {α : Type} (kb : KimchiBuilt F α)
    (pubVars : List Variable) : List (KimchiRow F) × List (AssembledGate F) × List Variable :=
  let rows := kb.gates.flatMap (toKimchiRows (F := F))
  let assembled := makeGateData pubVars rows kb.aux.wireState.unionFind
  (assembled.1, assembled.2.1, pubVars)

/-- The full pure pipeline: compile, dispatch the gates to rows, and assemble. Returns
the rows (public rows included), the gate table, and the public variables as a list,
since the public slots are not a prefix of the numbering here.

The public rows are the input slots then the output slots, `A.size + B.size` of them.
The compiled program witnessed the output slots, so their ids sit above the circuit's
rather than between its inputs and its body; the assembly resolves that renaming
through the wiring. -/
def kimchiGateData [Field F] [DecidableEq F] [A : CircuitType F a avar]
    [CheckedType F (KimchiConstraint F) a avar] [B : CircuitType F b bvar]
    (main : avar → CircuitM F (KimchiConstraint F) bvar) :
    List (KimchiRow F) × List (AssembledGate F) × List Variable :=
  let built := kimchiCompile (a := a) (b := b) main
  gateDataOf built ((allocRange 0 A.size).toList ++ bundleVars (F := F) (b := b) built.result.2)

end Snarky.Kimchi
