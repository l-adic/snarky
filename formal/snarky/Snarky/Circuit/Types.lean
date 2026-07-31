import Snarky.Circuit.CVar

/-!
# Circuit types

Port of `Snarky.Circuit.Types` (packages/snarky/src/Snarky/Circuit/Types.purs): the
value/variable duality — `CircuitType` encodes a value type as field elements and pairs it
with its variable-bundle form — plus the `FVar`/`BoolVar` base instances and their
round-trip laws.

Deviations from the PS original (per `formal/docs/snarky-ps-alignment.md`):
- The field-vector size is type-level (`Vector F size` vs PS `Array f` + the runtime
  `sizeInFields` contract), so the length obligations disappear; the `outParam` on `var`
  models the PS fundep `a f -> var`, while the reverse fundep `var -> f` is not modeled.
- The PS value wrappers `F f` and `Bool a` are not needed: Lean's class resolution
  dispatches on the plain field type and core `Bool` directly, so `val` is unwrapped. The
  wrapper-lifting instances (`PrimeField (F f)`, `HasEndo (F f)`, `FieldSizeInBits (F f)`)
  therefore have no analogue; `FieldSizeInBits` resurfaces with `SizedF` (plan §6).
- Instance coverage is the base pair only (`F`, `Bool`); the PS `Unit`,
  `NoInput`/`NoOutput`, `Tuple`, `Const`, `Product`, `Vector`, and `Record` instances land
  with their first consumers (the `IfThenElse` gadgets, walk step 10; `Backend/Compile`,
  step 14 — `NoInput`/`NoOutput`'s JSON instances are not ported); `UnChecked` is here,
  with its no-op `CheckedType` instance beside the class in `Circuit/DSL/Monad`.
- The generic/rowlist deriving machinery (`GCircuitType`/`RCircuitType`, the `generic*`
  helpers) is out of scope (D8) — Lean would grow a `deriving` handler instead.
- `CheckedType` is NOT here: its PS home is `Circuit/DSL/Monad.purs`, where it moves at
  walk step 5 (transitionally it sits in `Snarky.Types`).

Public results: the round-trip laws `fvar_value_roundTrip`, `fvar_var_roundTrip`,
`boolVar_value_roundTrip`, and `boolVar_var_roundTrip` — the PS
`Test.Snarky.Circuit.Types` QuickCheck spec as theorems (D9), for the instances above;
the generic-derived rows of that spec's table await the deriving machinery.
-/

namespace Snarky

/-! ## The class -/

/-- A bidirectional encoding of a value type `val` as `size` field elements, together with
its variable-bundle counterpart `var` (PS `CircuitType f a var`). -/
class CircuitType (F : Type u) (val : Type u) (var : outParam (Type u)) where
  /-- The number of field elements a `val` encodes to (PS `sizeInFields`, made type-level). -/
  size : Nat
  /-- Encode a value as its `size` field elements (PS `valueToFields`). -/
  valueToFields : val → Vector F size
  /-- Decode a value from its `size` field elements (PS `fieldsToValue`). -/
  fieldsToValue : Vector F size → val
  /-- Flatten a variable bundle into its `size` underlying `CVar`s (PS `varToFields`). -/
  varToFields : var → Vector (CVar F) size
  /-- Rebuild a variable bundle from `size` underlying `CVar`s (PS `fieldsToVar`). -/
  fieldsToVar : Vector (CVar F) size → var

/-! ## Field and boolean variables -/

/-- A single field element as a circuit value (PS `FVar f` is a wrapped `CVar`). -/
abbrev FVar (F : Type u) := CVar F

instance : CircuitType F F (FVar F) where
  size := 1
  valueToFields x := #v[x]
  fieldsToValue v := v[0]
  varToFields x := #v[x]
  fieldsToVar v := v[0]

/-- A boolean as a circuit variable (PS `BoolVar f = CVar f (Bool Variable)`).

Representation deviation: PS makes the distinction type-level — a phantom `Bool` tag on
the variable-index parameter of the `CVar` bifunctor (the exported `Bool` constructor
tags individual VARIABLES; a `BoolVar` expression is still built through the typed
algebra). Here `CVar` is monomorphic (see `Circuit/CVar`), so the tag becomes a nominal
wrapper on the expression root. The constructor is PRIVATE: introduction flows through
`CircuitType.fieldsToVar`, whose callers owe the `CheckedType.check` emission (`witness`
pays it). How the `DSL/Boolean` gadgets introduce their results is decided when they are
ported (walk step 10), against the PS originals — no blanket escape hatch exists. -/
structure BoolVar (F : Type u) where
  private mk ::
  /-- The underlying field expression, constrained to `{0, 1}` by `CheckedType.check`. -/
  toCVar : CVar F

instance [Zero F] [One F] [DecidableEq F] : CircuitType F Bool (BoolVar F) where
  size := 1
  valueToFields b := #v[if b then 1 else 0]
  fieldsToValue v := decide (v[0] ≠ 0)
  varToFields b := #v[b.toCVar]
  fieldsToVar v := ⟨v[0]⟩

/-- Wrap a type to skip its `check` constraints (PS `UnChecked a`): the encoding
delegates to the wrapped instance, and the `CheckedType` instance (in `Circuit/DSL/Monad`)
is a no-op. Use when the constraints are guaranteed elsewhere. -/
structure UnChecked (α : Type u) where
  /-- The wrapped value or variable bundle. -/
  val : α

instance [inst : CircuitType F val var] : CircuitType F (UnChecked val) (UnChecked var) where
  size := inst.size
  valueToFields v := inst.valueToFields v.val
  fieldsToValue fs := ⟨inst.fieldsToValue fs⟩
  varToFields v := inst.varToFields v.val
  fieldsToVar fs := ⟨inst.fieldsToVar fs⟩

/-! ## Round-trip laws (D9)

The PS suite checks these by QuickCheck over a table of types; for the base instances
they are theorems. The value→fields→value direction is the lawful one (fields→value is
lossy for `Bool` by design: any nonzero reads as `true`). -/

/-- A field value survives the round trip through its field encoding. -/
theorem fvar_value_roundTrip (x : F) :
    CircuitType.fieldsToValue (F := F) (var := FVar F)
      (CircuitType.valueToFields (F := F) (var := FVar F) x) = x := rfl

/-- A field variable bundle survives the round trip through its `CVar`s. -/
theorem fvar_var_roundTrip (x : FVar F) :
    CircuitType.fieldsToVar (F := F) (val := F)
      (CircuitType.varToFields (F := F) (val := F) x) = x := rfl

/-- A boolean survives the round trip through its field encoding — given `1 ≠ 0`, i.e.
the field is nontrivial. -/
theorem boolVar_value_roundTrip [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)]
    (b : Bool) :
    CircuitType.fieldsToValue (F := F) (var := BoolVar F)
      (CircuitType.valueToFields (F := F) (var := BoolVar F) b) = b := by
  cases b with
  | false => exact decide_eq_false fun h => h rfl
  | true => exact decide_eq_true one_ne_zero

/-- A boolean variable bundle survives the round trip through its `CVar`s. -/
theorem boolVar_var_roundTrip [Zero F] [One F] [DecidableEq F] (v : BoolVar F) :
    CircuitType.fieldsToVar (F := F) (val := Bool)
      (CircuitType.varToFields (F := F) (val := Bool) v) = v := rfl

end Snarky
