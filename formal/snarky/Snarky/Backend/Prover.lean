import Snarky.Backend.Builder

/-!
# The witness prover

Port of `Snarky.Backend.Prover` (packages/snarky/src/Snarky/Backend/Prover.purs,
`runCircuitProver`/`proverOps`): interpret a `CircuitM` tree by *running* the witness
computations against the accumulating assignment. As with the builder, the PS mutable
`ProverState` becomes explicit arguments and results, mirroring `build` so the
interpreter-agreement laws in `Snarky.Laws` read (and prove) symmetrically. Written with
explicit `match` (not `do`) so those proofs can `split` on every intermediate result.

## The semantic strengthening: constraints are always checked

The PS PRODUCTION prover does not check constraints at all — "they're assumed validated
during compilation" (module header); `SolveCircuit (Basic f)`'s `proverConstraint` is a
no-op outside debug mode, and validity is the proof system's concern. `prove` instead
checks every constraint at emission time with `holds`, unconditionally: it is PS's
DEBUG-mode semantics (minus message rendering) made total. That is deliberate — it is
what gives `Snarky.Laws.prove_sound` its content: a successful run is a satisfiability
certificate for the built system, not just a witness table.

Consequence, shared with PS debug mode (whose `debugCheck` also fails on unassigned
variables): a constraint may only be emitted once its variables are witnessed —
"witness before constrain". Not a restriction the PRODUCTION PS prover has (it checks
nothing); lifting it (deferring checks to the end of the run) is a design change to take
up only if a ported gadget hits it (plan §6).

## Further dispositions

- The constraint check is a pure parameter `holds : c → Assignments F → Bool`, not the
  PS `SolveCircuit` class (D5). Note the class is more than a checker: `proverConstraint`
  is a STATE TRANSFORM — backends like kimchi allocate and assign intermediates while
  reducing constraints at prove time. `holds` covers the checking fragment; the reducing
  fragment is the un-ported backend seam.
- Assignment is guarded (`Assignments.extendPairs`): re-assigning is an error, so prover
  runs are monotone in `Assignments.Le` (`prove_assignments_le`) — enforcing what PS
  `allocAssignments`/`Assignments.set` promise by write-once contract.
- `debug`, `labelStack`, `contextualize`, and `runWitness`'s error-wrapping are the
  error-attribution machinery; they follow the inert `labelOp` (plan §6). The advice
  handler threading in `runWitness` is the dropped advice row (`Circuit/DSL/Monad`).

The public surface is the port surface: `Proved` and `prove`. No PS QuickCheck property
targets the prover alone; the suite exercises it through solve round trips, and its laws
here are the Lean-only interpreter theorems in `Snarky.Laws`.
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
