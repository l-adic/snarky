import Snarky.Circuit.DSL.Monad

/-!
# The constraint builder

Port of `Snarky.Backend.Builder` (packages/snarky/src/Snarky/Backend/Builder.purs):
interpret a `CircuitM` tree by allocating variables and collecting constraints,
DISCARDING every witness computation — exactly the PS builder, whose `existsOp` is
`\n _ -> allocVars n` and whose `assignOp` is a no-op. PS's own comment corroborates the
advice story recorded in `Circuit/DSL/Monad`: its handler parameter is "unused — advice
is only reachable from witness computations, which the builder never runs".

Instead of threading a `CircuitBuilderState` record through `Effect` refs
(`runCircuitBuilder`/`builderOps`), `build` is a pure function from the next-variable
counter to the result, the final counter, and the emitted constraints. That collapses
most of the PS module; the disposition of the rest:

- `Constraints c` (the reverse-order `List` accumulator with `snocConstraint`/
  `constraintsToArray`) is a PS performance vehicle — O(1) append vs `Array.snoc`'s
  O(n²). The pure recursion gets emission order by consing each constraint onto the
  *suffix*'s list, O(1) with no accumulator type at all.
- `Labeled c` (constraint + label-stack context), the `labelStack`/`debug`/`varMetadata`
  state fields, and `allocVars`'s debug-mode metadata write are the error-attribution
  machinery behind the PS debug mode; they follow `labelOp` (inert here — plan §6) if it
  ever gains semantics.
- `CircuitBuilderState.publicInputs` belongs to the compile pipeline (`Backend/Compile`,
  walk step 14); `aux` belongs to the backend seam below.
- The `CompileCircuit` class (`appendBuilderConstraint`/`finalize`/
  `initialBuilderState`), its `Basic` instance, and `emptyBuilderState` are the
  backend-gate compilation seam — deliberately not ported (plan D5): `build` stops at
  DSL-level constraints, the natural comparison point against a PS-side dump.

The public surface is the port surface: `Built`, `build`, `constraints`, and
`allocRange` (PS exports its counterpart `allocVars`; `Compile` consumes it). Note
`allocRange` MUST be public regardless: `prove` shares it, and that sharing is what makes
the interpreters' allocation agreement (`Snarky.Laws.prove_build_agrees`) hold by
construction.

No PS QuickCheck property targets the builder alone (the suite exercises it through
compile/solve round trips); the builder's laws here are the Lean-only interpreter
theorems in `Snarky.Laws`, which is what the deep embedding exists for.
-/

namespace Snarky

variable {F c : Type u}

/-- The `n` variables `start, start+1, …, start+n-1` — sequential allocation, shared
verbatim by `build` and `prove` so the interpreters agree on numbering by construction.

Interpreter plumbing, not a DSL allocation interface: circuits allocate via
`fresh`/`existsVars`/`witness` and never see a counter. The explicit `start` is the pure
rendering of PS `allocVars`'s threaded `CircuitBuilderState` (whose `nextVar` field is
equally caller-visible there); only the interpreters — and later `Backend/Compile`,
seeding from `0` — supply it. -/
def allocRange (start n : Nat) : Vector Variable n :=
  Vector.ofFn fun i => start + i.val

/-- The builder's output: the computation's result, the final next-variable counter, and
the emitted constraints in emission order (the pure image of PS `runCircuitBuilder`'s
`Tuple a (CircuitBuilderState c aux)`). -/
structure Built (c : Type u) (α : Type v) where
  /-- The computation's result value. -/
  result : α
  /-- The next-variable counter after the run — the first variable a continuation would get. -/
  nextVar : Nat
  /-- The constraints the run emitted, in emission order. -/
  constraints : List c

/-- Interpret a circuit as its constraint system: from a next-variable counter, produce
the result, the final counter, and the constraints in emission order. Witness payloads are
never inspected — see `Snarky.Laws.build_eq_of_eraseWitness`. -/
def build : CircuitM F c α → Nat → Built c α
  | .pure a, n => ⟨a, n, []⟩
  | .freshOp k, n => build (k n) (n + 1)
  | .addConstraintOp con k, n =>
    let r := build k n
    ⟨r.result, r.nextVar, con :: r.constraints⟩
  | .existsOp m _ k, n => build (k (allocRange n m)) (n + m)
  | .assignOp _ _ k, n => build k n
  | .labelOp _ k, n => build k n

/-- The constraints of a circuit, counting variables from `0` (PS `compile`'s view of the
finished `CircuitBuilderState`). -/
def constraints (m : CircuitM F c α) : List c :=
  (build m 0).constraints

/-- **Building a sequence splits**: the tail builds from the head's result and final
counter, and the constraints concatenate in emission order — the composition law gadget
soundness chains through (`Snarky.Laws`, D12). -/
theorem build_bind (m : CircuitM F c α) (f : α → CircuitM F c β) (nv : Nat) :
    build (m >>= f) nv =
      ⟨(build (f (build m nv).result) (build m nv).nextVar).result,
       (build (f (build m nv).result) (build m nv).nextVar).nextVar,
       (build m nv).constraints
         ++ (build (f (build m nv).result) (build m nv).nextVar).constraints⟩ := by
  show build (CircuitM.bind m f) nv = _
  induction m generalizing nv with
  | pure a => rfl
  | freshOp k ih => exact ih ..
  | addConstraintOp con k ih =>
    simp only [CircuitM.bind, build, ih, List.cons_append]
  | existsOp n wit k ih => exact ih ..
  | assignOp vs wit k ih => exact ih ..
  | labelOp s k ih => exact ih ..

end Snarky
