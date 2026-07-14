import Snarky.Kimchi.Backend
import Snarky.Laws

/-!
# The soundness bridge: a successful prover run is a satisfied Kimchi gate list

The headline of the port's Kimchi bridge. `Snarky.prove_sound` says a successful prover
run's final assignment satisfies every constraint the builder emits; `holds_iff_row`
(from `Snarky.Kimchi.Backend`) says each such constraint, evaluated, is a satisfying
Generic gate row. Composing them: **a DSL circuit whose prover run succeeds translates to
a list of `Kimchi.Gate.Generic` rows that all `Hold`** (`satisfies_of_prove`) — i.e. the
DSL builds genuine, satisfiable Kimchi Generic-gate circuits, and the prover's witness is
a satisfying assignment for them.

`Gate.Generic.Holds` is the predicate `Kimchi.Index.rowSatisfies` uses for generic rows,
so this lands on the same semantics the rest of the Kimchi stack (quotient, verifier)
consumes. As in `Backend.lean`, the bridge is to the **un-wired** gate list; copy
constraints (variable sharing as wiring) are the deferred `Index` step. The executable
demos live in `Snarky.Kimchi.Example`.
-/

namespace Snarky.Kimchi

open Snarky

variable {F : Type*} [Field F] [DecidableEq F]

/-- Translate a whole constraint list into a Generic gate circuit against an assignment:
each constraint becomes one row (`GateConstraint.toRow`), `none` if any operand fails to
evaluate. The failure case exists because `env` is arbitrary here — a constraint can
mention a variable `env` never assigned; after a *successful prover run* it cannot fire,
and that is a theorem (`toCircuit_sound` produces the `some`), not a default. Structural
recursion (not `mapM`) so it reduces under `decide` and inducts cleanly. -/
def toCircuit : List (GateConstraint F) → Assignments F → Option (List (Kimchi.Gate.Generic F))
  | [], _ => some []
  | con :: rest, env =>
    match con.toRow env with
    | some row => (toCircuit rest env).map (row :: ·)
    | none => none

/-- If every constraint in a list holds against `env`, the list translates to a Generic
gate circuit that is satisfied — the list-level lift of `holds_iff_row`. -/
theorem toCircuit_sound {L : List (GateConstraint F)} {env : Assignments F}
    (hall : ∀ con ∈ L, con.holds env = true) :
    ∃ rows, toCircuit L env = some rows ∧ Kimchi.Gate.Satisfies rows := by
  induction L with
  | nil => exact ⟨[], rfl, by intro g hg; cases hg⟩
  | cons con rest ih =>
    obtain ⟨row, hrow, hholds⟩ :=
      (con.holds_iff_row env).mp (hall con (List.mem_cons_self ..))
    obtain ⟨rows, hrows, hsat⟩ := ih fun c hc => hall c (List.mem_cons_of_mem _ hc)
    refine ⟨row :: rows, ?_, ?_⟩
    · simp only [toCircuit, hrow, hrows, Option.map_some]
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hholds
      · exact hsat g hg

/-- **The soundness bridge.** If the prover run of a DSL circuit (over the Kimchi
Generic-gate backend) succeeds, then the constraints the builder emits translate — against
the prover's final assignment — to a list of Generic gate rows that all `Hold`. The DSL
produces satisfiable Kimchi Generic-gate circuits, and the prover's witness satisfies
them. -/
theorem satisfies_of_prove {α : Type*} {m : CircuitM F (GateConstraint F) α}
    {nv nv' : Nat} {env env' : Assignments F} {x : α}
    (h : prove GateConstraint.holds m nv env = .ok ⟨x, nv', env'⟩) :
    ∃ rows, toCircuit (build m nv).constraints env' = some rows
      ∧ Kimchi.Gate.Satisfies rows :=
  toCircuit_sound
    (prove_sound (holds := GateConstraint.holds)
      (fun _con _ _ hle hh => GateConstraint.holds_mono hle hh) h)

end Snarky.Kimchi
