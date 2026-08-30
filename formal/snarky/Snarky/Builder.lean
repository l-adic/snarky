import Snarky.Circuit

/-!
# The constraint builder

Interpret a `CircuitM` tree by allocating variables and collecting constraints,
discarding every witness computation — the PS builder, whose `existsOp` handler only
allocates, as a pure function from the next-variable counter to the result, the final
counter, and the emitted constraints.
-/

namespace Snarky

universe u v

variable {F c : Type u} {α β : Type v}

/-- The `n` variables `start, start+1, …, start+n-1`. -/
def allocRange (start n : Nat) : Vector Variable n :=
  ⟨⟨List.range' start n⟩, by simp⟩

@[simp] theorem getElem_allocRange (start n i : Nat) (hi : i < n) :
    (allocRange start n)[i] = start + i := by
  simp [allocRange]

/-- The builder's output: the result, the final next-variable counter, and the emitted
constraints in emission order. -/
structure Built (c : Type u) (α : Type v) where
  /-- The computation's result value. -/
  result : α
  /-- The next-variable counter after the run. -/
  nextVar : Nat
  /-- The constraints the run emitted, in emission order. -/
  constraints : List c

/-- Interpret a circuit as its constraint system. -/
def build : CircuitM F c α → Nat → Built c α
  | .pure a, n => ⟨a, n, []⟩
  | .addConstraintOp con k, n =>
    let r := build k n
    ⟨r.result, r.nextVar, con :: r.constraints⟩
  | .existsOp m _ k, n => build (k (allocRange n m)) (n + m)

/-- Building a sequence splits: the tail builds from the head's result and final
counter, and the constraints concatenate in emission order. -/
theorem build_bind (m : CircuitM F c α) (f : α → CircuitM F c β) (nv : Nat) :
    build (m >>= f) nv =
      ⟨(build (f (build m nv).result) (build m nv).nextVar).result,
       (build (f (build m nv).result) (build m nv).nextVar).nextVar,
       (build m nv).constraints
         ++ (build (f (build m nv).result) (build m nv).nextVar).constraints⟩ := by
  show build (CircuitM.bind m f) nv = _
  induction m generalizing nv with
  | pure a => rfl
  | addConstraintOp con k ih =>
    simp only [CircuitM.bind, build, ih, List.cons_append]
  | existsOp n wit k ih => exact ih ..

end Snarky
