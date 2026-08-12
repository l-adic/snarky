import Snarky.Circuit.CVar
import Snarky.Kimchi.UnionFind

/-!
# The kimchi backend's data layer

Port of `Snarky.Constraint.Kimchi.Types`
(packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/Types.purs): the row and state
types everything in the kimchi backend reduces into — the queued generic constraint, the
15-column gate row, the wire state (internal variables, union-find, cached constants),
and the `ToKimchiRows` emission class.

Name map: every export keeps its name (`GenericPlonkConstraint`, `AuxState`,
`initialAuxState`, `GateKind`, `KimchiRow`, `KimchiWireRow`, `emptyKimchiWireState`,
`ToKimchiRows`/`toKimchiRows`), except `KimchiRow.variables` → `vars` (`variables` is a
deprecated command token in Lean 4); `GateKind`'s constructors drop to lowerCamel
(`GenericPlonkGate` → `.genericPlonk`, `AddCompleteGate` → `.addComplete`,
`PoseidonGate` → `.poseidon`, `VarBaseMul` → `.varBaseMul`, `EndoMul` → `.endoMul`,
`EndoScalar` → `.endoScalar`, `Zero` → `.zero`), matching `Kimchi.GateType`'s style.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- `KimchiRow.coeffs` stays a `List F` of UNFIXED length, exactly PS's `Array f`, because
  the length is semantic, not a register file: the EC and `zero` reducers emit EMPTY
  coefficient arrays (those gates have no coefficients), Poseidon emits exactly 15 (the
  round constants), and generic rows emit none or the packed constraint coefficients —
  matching production's variable-length `CircuitGate.coeffs` and the fixture bytes,
  which record `[]`, not fifteen zeros — the byte contract. PS's "15-column coefficient row" comment
  names the maximum width, not an invariant. The 15-slot `vars` vector IS typed, as in
  PS — every row genuinely has 15 witness cells.
- The wire state's mutable pieces are pure: `Data.UnionFind.Mutable` renders as
  `Snarky.Kimchi.UnionFind` (see its docstring for why dropping the mutation is
  semantics-preserving), PS `Set Variable` as a `List` (the one insertion site adds a
  strictly-fresh variable, so a cons is set-faithful; the dump only tests membership),
  and PS `Map f Variable` as an assoc list with first-match lookup — order-faithful:
  the only in-code consumer is `lookup`, and the circuit-diffs dumper sorts by variable
  before serialising (settled at the reduction step, `Constraint/Reduction.lean`).
- `initialAuxState` is a pure value — PS runs in `Effect` only to allocate the mutable
  union-find.
- `GateKind` is the EMITTER's tag, deliberately not `Kimchi.GateType`: the two enums
  are near-isomorphic, but identifying them would pull the kimchi library into the
  constraint layer, which stays free of `Kimchi` imports; no `GateKind → Kimchi.GateType`
  mapping is defined here.

The package's own test surface (`test/Test/Snarky/Circuit/Kimchi/GenericTest.purs`)
exercises the circuit layer, not this data layer.
The union-find spec rows live as `decide` examples beside the structure.
-/

namespace Snarky.Kimchi

open Snarky

/-- One queued generic constraint (PS `GenericPlonkConstraint`):
`cl·l + cr·r + co·o + m·(l·r) + c = 0` over three optional variable slots. Two of these
pack into one Generic gate row — the queue lives in `AuxState.queuedGenericGate`. -/
structure GenericPlonkConstraint (F : Type u) where
  /-- Left slot's coefficient. -/
  cl : F
  /-- Left slot's variable, if any. -/
  vl : Option Variable
  /-- Right slot's coefficient. -/
  cr : F
  /-- Right slot's variable, if any. -/
  vr : Option Variable
  /-- Output slot's coefficient. -/
  co : F
  /-- Output slot's variable, if any. -/
  vo : Option Variable
  /-- The multiplication coefficient (on `l·r`). -/
  m : F
  /-- The constant term. -/
  c : F
  deriving Repr, DecidableEq

/-- The gate tag on an emitted coefficient row (PS `GateKind`). The emitter's enum, not
`Kimchi.GateType` — the mapping between the two lands with the CS assembly (see the
module docstring). -/
inductive GateKind where
  /-- A packed Generic gate row (PS `GenericPlonkGate`). -/
  | genericPlonk
  /-- A complete-addition row (PS `AddCompleteGate`). -/
  | addComplete
  /-- A Poseidon block row (PS `PoseidonGate`). -/
  | poseidon
  /-- A variable-base scalar-multiplication row. -/
  | varBaseMul
  /-- An endomorphism scalar-multiplication row. -/
  | endoMul
  /-- An endo-scalar decomposition row. -/
  | endoScalar
  /-- The zero gate — unconstrained rows (final states, padding). -/
  | zero
  deriving Repr, DecidableEq

/-- One emitted gate row (PS `KimchiRow`): the gate tag, the 15 witness-cell variable
slots, and the coefficient row. -/
structure KimchiRow (F : Type u) where
  /-- The gate tag. -/
  kind : GateKind
  /-- The 15 witness-cell variable slots (`none` = unconstrained cell). PS names this
  `variables`; that is a (deprecated) command token in Lean 4, hence the rename. -/
  vars : Vector (Option Variable) 15
  /-- The coefficient row. Deliberately length-unfixed, as in PS — the fixtures record
  varying lengths (see the module docstring). -/
  coeffs : List F
  deriving Repr, DecidableEq

/-- The wire-placement state (PS `KimchiWireRow`): which variables the reduction
allocated internally, the union-find whose partition becomes the wiring permutation, and
the constant-dedup cache. -/
structure KimchiWireRow (F : Type u) where
  /-- Variables the reduction allocated (as opposed to user allocations). -/
  internalVariables : List Variable
  /-- The union-find over variables; its partition becomes the wiring permutation. -/
  unionFind : UnionFind
  /-- Constant values already given a pinned variable, for dedup (PS `Map f Variable`;
  first-match assoc lookup here). -/
  cachedConstants : List (F × Variable)
  deriving Repr, DecidableEq

/-- The empty wire state around a given union-find (PS `emptyKimchiWireState`). -/
private def emptyKimchiWireState (uf : UnionFind) : KimchiWireRow F :=
  { internalVariables := [], unionFind := uf, cachedConstants := [] }

/-- The backend's auxiliary compile state (PS `AuxState`): the wire state plus the
one-slot queue holding an unpacked generic constraint awaiting its row partner. -/
structure AuxState (F : Type u) where
  /-- The wire-placement state. -/
  wireState : KimchiWireRow F
  /-- A generic constraint waiting to be packed with a second one into a row. -/
  queuedGenericGate : Option (GenericPlonkConstraint F)
  deriving Repr, DecidableEq

/-- The initial auxiliary state (PS `initialAuxState`, minus the `Effect` that only
allocated the mutable union-find). -/
def initialAuxState : AuxState F :=
  { wireState := emptyKimchiWireState .empty, queuedGenericGate := none }

/-- Row emission (PS `ToKimchiRows`): reduce a constraint to its gate rows. -/
class ToKimchiRows (F : Type u) (α : Type u) where
  /-- The gate rows a constraint emits, in emission order. -/
  toKimchiRows : α → List (KimchiRow F)

export ToKimchiRows (toKimchiRows)

/-- A row list is its own emission — the carrier the multi-row reducers return (PS
re-declares a per-module `Rows` newtype over an array for its instance head; Lean uses
the bare list). -/
instance : ToKimchiRows F (List (KimchiRow F)) where
  toKimchiRows := id

/-! ## Examples -/

/-- The initial state is genuinely empty: no internals, no queue, an empty partition. -/
example : (initialAuxState (F := Nat)).wireState.unionFind.equivalenceClasses = []
    ∧ (initialAuxState (F := Nat)).queuedGenericGate = none := by decide

end Snarky.Kimchi
