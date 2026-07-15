import Snarky.Monad

/-!
# The constraint builder

Port of `Snarky.Backend.Builder` (packages/snarky/src/Snarky/Backend/Builder.purs,
`runCircuitBuilder`/`builderOps`): interpret a `CircuitM` tree by allocating variables and
collecting constraints, discarding every witness computation — exactly the PS builder,
whose `existsOp` is `\n _ -> allocVars n` and whose `assignOp` is a no-op.

Instead of threading a `CircuitBuilderState` record through `Effect` refs, `build` is a
pure function from the next-variable counter to the result, the final counter, and the
emitted constraints in order. (The PS builder also compiles DSL constraints to backend
gates on the fly via `CompileCircuit`; that compilation step is deliberately out of scope
here — `build` returns the DSL-level constraints, the natural first comparison point
against a PS-side dump.)
-/

namespace Snarky

variable {F c : Type u}

/-- The `n` variables `start, start+1, …, start+n-1` — sequential allocation, shared
verbatim by `build` and `prove` so the interpreters agree on numbering by construction. -/
def allocRange (start n : Nat) : Vector Variable n :=
  Vector.ofFn fun i => start + i.val

/-- The builder's output: the computation's result, the final next-variable counter, and
the emitted constraints in emission order (the pure image of PS `runCircuitBuilder`'s
`Tuple a (CircuitBuilderState c aux)`). -/
structure Built (c : Type u) (α : Type v) where
  result : α
  nextVar : Nat
  constraints : List c

/-- Interpret a circuit as its constraint system: from a next-variable counter, produce
the result, the final counter, and the constraints in emission order. Witness payloads are
never inspected — see `Snarky.Laws.build_eq_of_sameShape`. -/
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

end Snarky
