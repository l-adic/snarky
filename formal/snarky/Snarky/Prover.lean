import Snarky.Builder

/-!
# The witness prover

Port of `Snarky.Backend.Prover` (packages/snarky/src/Snarky/Backend/Prover.purs,
`runCircuitProver`/`proverOps`): interpret a `CircuitM` tree by *running* the witness
computations against the accumulating assignment, checking each constraint as it is added
(PS `proverConstraint`), and erroring out on the first failure.

As with the builder, the PS interpreter state (`ProverState f`, mutable refs) becomes
explicit arguments and results: `prove` takes the next-variable counter and the current
assignment and returns the result with the final counter and assignment — the exact
mirror of `build : CircuitM F c α → Nat → α × Nat × List c`, which is what makes the
interpreter-agreement laws in `Snarky.Laws` read (and prove) symmetrically.

Deviations from PS, both in the direction of stronger invariants:
- assignment is guarded (`Assignments.extendPairs`): re-assigning a variable is an error,
  so a prover run is monotone in `Assignments.Le` — the fact the completeness theorem
  (`Snarky.Laws.prove_sound`) rests on;
- the constraint check is a parameter `holds : c → Assignments F → Bool` rather than a
  `SolveCircuit` class method, keeping `c` fully abstract.

Written with explicit `match` (not `do`) so the `Snarky.Laws` proofs can `split` on every
intermediate result.
-/

namespace Snarky

variable {F c : Type u}

/-- The prover's output: the computation's result, the final next-variable counter, and
the final assignment — the mirror of `Built`, with the witness table where the builder
has the constraints. -/
structure Proved (F : Type u) (α : Type v) where
  /-- The computation's result value. -/
  result : α
  /-- The next-variable counter after the run — in lockstep with `Built.nextVar`. -/
  nextVar : Nat
  /-- The final assignment: every variable the run allocated, mapped to its witness value. -/
  assignments : Assignments F

/-- Interpret a circuit as a prover run: allocate variables in lockstep with `build`, run
witness computations to fill the assignment, and check every added constraint with
`holds`. Succeeds with the result, the final counter, and the final assignment iff every
witness computation succeeds, no variable is assigned twice, and every constraint holds
when added. -/
def prove (holds : c → Assignments F → Bool) :
    CircuitM F c α → Nat → Assignments F → Except EvalError (Proved F α)
  | .pure a, nv, env => .ok ⟨a, nv, env⟩
  | .freshOp k, nv, env => prove holds (k nv) (nv + 1) env
  | .addConstraintOp con k, nv, env =>
    if holds con env then prove holds k nv env
    else .error .unsatisfiedConstraint
  | .existsOp n wit k, nv, env =>
    match wit env with
    | .error e => .error e
    | .ok xs =>
      match env.extendPairs ((allocRange nv n).toList.zip xs.toList) with
      | .error e => .error e
      | .ok env' => prove holds (k (allocRange nv n)) (nv + n) env'
  | .assignOp vs wit k, nv, env =>
    match wit env with
    | .error e => .error e
    | .ok xs =>
      match env.extendPairs (vs.toList.zip xs.toList) with
      | .error e => .error e
      | .ok env' => prove holds k nv env'
  | .labelOp _ k, nv, env => prove holds k nv env

end Snarky
