import Snarky.Backend.Ops
import Snarky.Kimchi.Constraint.GenericPlonk
import Snarky.Kimchi.Constraint.AddComplete
import Snarky.Kimchi.Constraint.EndoScalar
import Snarky.Kimchi.Constraint.VarBaseMul
import Snarky.Kimchi.Constraint.EndoMul
import Snarky.Kimchi.Constraint.Poseidon

/-!
# The kimchi constraint type and its interpreters

Port of `Snarky.Constraint.Kimchi`
(packages/snarky-kimchi/src/Snarky/Constraint/Kimchi.purs): the backend's constraint
sum `KimchiConstraint`, the emitted-gate sum `KimchiGate` with its row dispatch, the
`BasicSystem` instance, and the backend seams — PS's `CompileCircuit`/`SolveCircuit`
instances become the ops record `kimchiOps` plugged into the ONE generic interpreter
pair (`Snarky/Backend/Ops.lean`), exactly the PS architecture. The one-counter decision
(`Constraint/Reduction.lean`'s module docstring) lives in the ops: each constraint's
reduction borrows
and returns the SHARED variable counter, whose interleaved numbering is fixture
bytes.

Name map: `KimchiConstraint`/`KimchiGate` keep their names, constructors dropped
to lowerCamel without the `Kimchi` prefix (`KimchiBasic` → `.basic`, …,
`KimchiPad` → `.pad`; `KimchiGateNoOp` → `.noOp`);
`reducePad` keeps its name; the per-instance `go` dispatch is factored into
the one class-polymorphic `KimchiConstraint.reduce` both ops run
(`appendConstraint` = `reduceAsBuilder` of it, `proveConstraint` = `reduceAsProver`
of it — the PS instances inline the same dispatch twice); `finalize` is the ops
record's field.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- The Poseidon parameters ride in the payload (the payload-data deviation in
  `Constraint/Poseidon.lean`), so the reduction seam takes no parameter for them.
  The `KimchiVerify` marker class is not ported: it bundles per-curve endo/Poseidon
  data for PS instance resolution, and the Lean side passes that data explicitly.
- `eval` is not ported (PS keeps it as a vacuous `pure true` stub of the deleted
  Rust cross-check); `postCondition` is not ported (a test-harness check that wired
  classes carry consistent values; no analogue is stated here). The PS prover's
  `debug` branch is likewise gone in production semantics (PS's own comment:
  superseded by the circuit-diffs byte-equality).
- The prover seam checks nothing per constraint (the PS PRODUCTION semantics): a
  kimchi constraint emits rows, not a checkable predicate, and validation is the row
  laws plus the fixture seam. This diverges from the base `prove`'s deliberate
  checking strengthening; the closest kimchi analogue of `prove_complete` is the
  ops-coherence lockstep, undischarged here (closing paragraph).
- Labels are not threaded (the base embedding's `labelOp` is inert).

The composition laws come for free from the generic interpreter
(`buildWith_bind`/`proveWith_bind`), and the cross-seam laws are stated there as the
ops-coherence facts `BackendOps.Lockstep`/`BackendOps.ProveExtends` with their
whole-program consequences (`buildWith_proveWith_nextVar`/`proveWith_extends`).
They are not discharged for `kimchiOps` here: doing so is per-gate content — both
instances of `KimchiConstraint.reduce` must branch identically and advance the
counter identically.
-/

namespace Snarky.Kimchi

open Snarky

/-- The kimchi backend's constraint type (PS `KimchiConstraint`): the DSL's `Basic`
vocabulary plus the per-gate constraints and the padding row (see `.pad`). -/
inductive KimchiConstraint (F : Type u) where
  /-- A `Basic` constraint, reduced through the generic-gate fan-out. -/
  | basic (c : Basic F)
  /-- A complete-addition constraint. -/
  | addComplete (c : AddComplete F)
  /-- A Poseidon block constraint. -/
  | poseidon (c : PoseidonConstraint F)
  /-- A variable-base scalar-multiplication constraint. -/
  | varBaseMul (c : VarBaseMul F)
  /-- A challenge-decomposition constraint. -/
  | endoScalar (c : EndoScalar F)
  /-- An endomorphism-optimized scalar-multiplication constraint. -/
  | endoMul (c : EndoMul F)
  /-- Pad the circuit by one row: a Generic-kind row with no coefficients, so the
  generic equation is degenerate (`0 = 0`) and the row's only content is its wiring
  (seven cells — the permutable width). The consumers are PS-side: the chunk-test
  circuits push row counts past a domain boundary with it. No Lean circuit emits
  it. -/
  | pad (vs : Vector (FVar F) 7)
  deriving Repr, DecidableEq

/-- The emitted-gate sum (PS `KimchiGate`): what one constraint reduces to — the
per-gate row carriers, or nothing (`Basic` constraints emit through the batching
queue instead). -/
inductive KimchiGate (F : Type u) where
  /-- One packed generic row. -/
  | plonk (r : Rows F)
  /-- One complete-addition row. -/
  | addComplete (r : Rows F)
  /-- A Poseidon block's rows. -/
  | poseidon (rs : List (KimchiRow F))
  /-- A scalar multiplication's row pairs. -/
  | varBaseMul (rs : List (KimchiRow F × KimchiRow F))
  /-- A challenge decomposition's rows. -/
  | endoScalar (rs : List (KimchiRow F))
  /-- An endomorphism multiplication's rows. -/
  | endoMul (rs : List (KimchiRow F))
  /-- No direct rows (a reduced `Basic` constraint). -/
  | noOp
  deriving Repr, DecidableEq

/-- Row dispatch (the PS `ToKimchiRows (KimchiGate f)` instance). -/
instance : ToKimchiRows F (KimchiGate F) where
  toKimchiRows
    | .plonk r => toKimchiRows r
    | .addComplete r => toKimchiRows r
    | .poseidon rs => toKimchiRows rs
    | .varBaseMul rs => toKimchiRows rs
    | .endoScalar rs => toKimchiRows rs
    | .endoMul rs => toKimchiRows rs
    | .noOp => []

/-- The DSL's constraint constructors, into the kimchi sum (the PS `BasicSystem`
instance). -/
instance : BasicSystem F (KimchiConstraint F) where
  r1cs l r o := .basic (.r1cs l r o)
  equal a b := .basic (.equal a b)
  square a c := .basic (.square a c)
  boolean x := .basic (.boolean x)

variable {F : Type} {m : Type → Type}

/-- Pin the padding row's seven operands into its emitted row (PS `reducePad`). -/
private def reducePad [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] (vs : Vector (FVar F) 7) : m (Rows F) := do
  let v0 ← reduceToVariable vs[0]
  let v1 ← reduceToVariable vs[1]
  let v2 ← reduceToVariable vs[2]
  let v3 ← reduceToVariable vs[3]
  let v4 ← reduceToVariable vs[4]
  let v5 ← reduceToVariable vs[5]
  let v6 ← reduceToVariable vs[6]
  pure (mkPadRow ⟨⟨[v0, v1, v2, v3, v4, v5, v6]⟩, by simp⟩)

/-- The one dispatch both interpreters run (the PS instances' `go`, factored): reduce
a constraint through its gate's reducer and wrap the rows. `Basic` constraints emit
into the batching queue and wrap as `noOp`. -/
def KimchiConstraint.reduce [Add F] [Mul F] [Sub F] [Zero F] [One F] [Neg F]
    [DecidableEq F] [Monad m] [PlonkReductionM F m] :
    KimchiConstraint F → m (KimchiGate F)
  | .basic c => do
    Snarky.Kimchi.reduce c
    pure .noOp
  | .addComplete c => .addComplete <$> c.reduce
  | .poseidon c => .poseidon <$> c.reduce
  | .varBaseMul c => .varBaseMul <$> VarBaseMul.reduce c
  | .endoScalar c => .endoScalar <$> EndoScalar.reduce c
  | .endoMul c => .endoMul <$> c.reduce
  | .pad vs => .plonk <$> reducePad vs

/-! ## The backend ops (PS's two instances, as one record) -/

/-- The kimchi backend's ops (the PS `CompileCircuit`/`SolveCircuit` instances):
each constraint runs the one dispatch — in the builder for `appendConstraint`
(emitting first the batched generic rows the reduction flushed, then the wrapped
gate), in the prover for `proveConstraint` (extending the table, checking nothing —
the PS production semantics; see the module docstring) — and `finalize` flushes the
odd queued constraint into one more packed row. -/
def kimchiOps [Add F] [Mul F] [Sub F] [Zero F] [One F] [Neg F] [Div F]
    [DecidableEq F] :
    BackendOps F (KimchiGate F) (KimchiConstraint F) (AuxState F) where
  appendConstraint con n aux :=
    let red := reduceAsBuilder n aux (KimchiConstraint.reduce con)
    (red.2.1.map .plonk ++ [red.1], red.2.2.1, red.2.2.2)
  proveConstraint con nv env :=
    match reduceAsProver ⟨nv, env⟩ (KimchiConstraint.reduce con) with
    | .error e => .error e
    | .ok (_, s') => .ok (s'.nextVariable, s'.assignments)
  finalize aux :=
    ((finalizeGateQueue aux.queuedGenericGate).map .plonk,
     { aux with queuedGenericGate := none })

end Snarky.Kimchi
