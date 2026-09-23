import Snarky.CVar
import Snarky.Kimchi.UnionFind

/-!
# The kimchi backend's data layer

Transcribes packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/Types.purs: the types the
kimchi backend reduces into — the queued generic constraint, the gate row, the wire state,
and the `ToKimchiRows` emission class. Names are kept, except that `KimchiRow.vars` renames
a field whose upstream name is a Lean command keyword, and `GateKind`'s constructors are
lowerCamel, as in `Kimchi.Index.GateType`.

## Deviations from the source

- `KimchiRow.coeffs` is a `List` of unfixed length, because the fixtures record the length:
  EC, endo and `zero` rows carry `[]`, not zeros; a Poseidon round row carries its
  `coeffCols` round constants; a generic row carries none (padding) or one or two packed
  constraints' coefficients. The `vars` vector is typed: every row has `wCols` cells.
- The wire state is pure: the mutable union-find becomes `UnionFind`, the internal-variable
  set a `List` (its one insertion adds a fresh variable), and the constant cache an assoc
  list read by first-match lookup.
- `GateKind` stays apart from `Kimchi.Index.GateType` so this layer imports no `Kimchi` module;
  `PicklesFixture.kindType` maps one to the other.
-/

namespace Snarky.Kimchi

open Snarky

/-- One queued generic constraint, `cl·l + cr·r + co·o + m·(l·r) + c = 0` over three
optional variable slots. Two pack into one Generic gate row, via
`AuxState.queuedGenericGate`. -/
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


/-- The gate tag on an emitted row. -/
inductive GateKind where
  /-- A packed Generic gate row. -/
  | genericPlonk
  /-- A complete-addition row. -/
  | addComplete
  /-- A Poseidon block row. -/
  | poseidon
  /-- A variable-base scalar-multiplication row. -/
  | varBaseMul
  /-- An endomorphism scalar-multiplication row. -/
  | endoMul
  /-- An endo-scalar decomposition row. -/
  | endoScalar
  /-- The zero gate: an unconstrained row holding a block's final state. -/
  | zero

/-- One emitted gate row. -/
structure KimchiRow (F : Type u) where
  /-- The gate tag. -/
  kind : GateKind
  /-- The witness-cell variables; `none` leaves a cell unconstrained. -/
  vars : Vector (Option Variable) 15
  /-- The coefficient row, of per-gate length (see the module docstring). -/
  coeffs : List F

/-- The wire-placement state. -/
structure KimchiWireRow (F : Type u) where
  /-- Variables the reduction allocated, as opposed to the user. -/
  internalVariables : List Variable
  /-- The union-find over variables; its partition becomes the wiring permutation. -/
  unionFind : UnionFind
  /-- Constants already given a variable, for dedup; read by first-match lookup. -/
  cachedConstants : List (F × Variable)


/-- The empty wire state around a given union-find. -/
private def emptyKimchiWireState (uf : UnionFind) : KimchiWireRow F :=
  { internalVariables := [], unionFind := uf, cachedConstants := [] }

/-- The backend's auxiliary compile state: the wire state and a one-slot generic-constraint
queue. -/
structure AuxState (F : Type u) where
  wireState : KimchiWireRow F
  /-- A generic constraint waiting to be packed with a second one into a row. -/
  queuedGenericGate : Option (GenericPlonkConstraint F)


/-- The initial auxiliary state: an empty union-find and an empty queue. -/
def initialAuxState : AuxState F :=
  { wireState := emptyKimchiWireState .empty, queuedGenericGate := none }

/-- Row emission: a constraint's gate rows. -/
class ToKimchiRows (F : Type u) (α : Type u) where
  /-- The gate rows a constraint emits, in emission order. -/
  toKimchiRows : α → List (KimchiRow F)

export ToKimchiRows (toKimchiRows)

/-- A row list emits itself. -/
instance : ToKimchiRows F (List (KimchiRow F)) where
  toKimchiRows := id

end Snarky.Kimchi
