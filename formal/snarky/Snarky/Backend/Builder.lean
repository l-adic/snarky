import Snarky.Circuit.DSL.Monad

/-!
# The constraint builder

Port of `Snarky.Backend.Builder` (packages/snarky/src/Snarky/Backend/Builder.purs):
interpret a `CircuitM` tree by allocating variables and collecting constraints,
DISCARDING every witness computation — exactly the PS builder, whose `existsOp` handler
only allocates and whose `assignOp` is a no-op. Instead of threading a mutable
`CircuitBuilderState` through `Effect` refs, `build` is a pure function from the
next-variable counter to the result, the final counter, and the emitted constraints.

Disposition of the PS module's remainder (ledger: `formal/docs/snarky-ps-alignment.md`):
the reverse-order `Constraints c` accumulator is a PS performance vehicle (the pure
recursion gets emission order by consing onto the suffix); `Labeled c`, the
`labelStack`/`debug`/`varMetadata` fields, and debug-mode metadata are error-attribution
machinery following the inert `labelOp`; the `CompileCircuit` class and
`emptyBuilderState` are a backend-compilation seam deliberately not ported — `build`
stops at DSL-level constraints.

Lean-only, beside their subject: `build_bind` (building a sequence splits at the bind)
and witness-independence (`build_eraseWitness` — the constraint system provably cannot
depend on witness data).
-/

namespace Snarky

variable {F c : Type u}

/-- The `n` variables `start, start+1, …, start+n-1` — sequential allocation.
Interpreter plumbing, not a DSL allocation interface: circuits allocate via
`existsVars`/`witness` and never see a counter. The explicit `start` is the
pure rendering of PS `allocVars`'s threaded `CircuitBuilderState`. -/
def allocRange (start n : Nat) : Vector Variable n :=
  Vector.ofFn fun i => start + i.val

/-- Every variable the range allocates lies inside it. -/
theorem mem_allocRange {start n v : Nat} (h : v ∈ (allocRange start n).toList) :
    start ≤ v ∧ v < start + n := by
  simp only [allocRange, Vector.toList_ofFn, List.mem_ofFn] at h
  obtain ⟨i, hi⟩ := h
  omega

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
never inspected — see `build_eq_of_eraseWitness` below. -/
def build : CircuitM F c α → Nat → Built c α
  | .pure a, n => ⟨a, n, []⟩
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

/-- Building a `pure` emits nothing: the result passes through, the counter is
untouched, and the constraint list is empty. -/
@[circuitVal] theorem build_pure (a : α) (nv : Nat) :
    build (pure a : CircuitM F c α) nv = ⟨a, nv, []⟩ := rfl

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
  | assignOp vs wit k ih => exact ih ..
  | labelOp s k ih => exact ih ..

/-! ## Witness-independence -/

/-- Strip every witness payload from the tree, leaving the circuit's shape: the
`AsProver` computations at `existsOp`/`assignOp` nodes are replaced by the trivially
failing one. Two circuits differ only in their witness code exactly when their erasures
are equal — for literal circuit terms that equality is `rfl`. -/
def eraseWitness : CircuitM F c α → CircuitM F c α
  | .pure a => .pure a
  | .addConstraintOp con k => .addConstraintOp con (eraseWitness k)
  | .existsOp n _ k =>
    .existsOp n (AsProver.throw "erased") fun vs => eraseWitness (k vs)
  | .assignOp vs _ k =>
    .assignOp vs (AsProver.throw "erased") (eraseWitness k)
  | .labelOp s k => .labelOp s (eraseWitness k)

/-- Witness-independence of the builder: `build` factors through `eraseWitness` —
the constraint system (and the result, and the variable numbering) depends only on the
shape of the circuit, never on the witness computations stored at `existsOp`/`assignOp`
nodes. -/
theorem build_eraseWitness (m : CircuitM F c α) : ∀ n, build (eraseWitness m) n = build m n := by
  induction m with
  | pure a => intro n; rfl
  | addConstraintOp con k ih => intro n; simp only [eraseWitness, build, ih n]
  | existsOp k wit K ih => intro n; simp only [eraseWitness, build]; exact ih _ (n + k)
  | assignOp vs wit k ih => intro n; simp only [eraseWitness, build]; exact ih n
  | labelOp s k ih => intro n; simp only [eraseWitness, build]; exact ih n

/-- Circuits with equal erasures build identically — the two-circuit corollary. -/
theorem build_eq_of_eraseWitness {m m' : CircuitM F c α}
    (h : eraseWitness m = eraseWitness m') (n : Nat) : build m n = build m' n := by
  rw [← build_eraseWitness m, h, build_eraseWitness]

end Snarky
