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
- Instance coverage is the base pair (`F`, `Bool`) plus `Prod` (PS `Tuple`, landed with
  its first consumer: `DSL/Field.equals`'s witness pair, walk step 9); the PS `Unit`,
  `NoInput`/`NoOutput`, `Const`, `Product`, `Vector`, and `Record` instances land
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

Representation deviation: PS tags the variable-index parameter of the `CVar` bifunctor
with the exported newtype `Bool`, and its gadgets retag freely with `Safe.Coerce` —
representation-safe, but ambient. Here `CVar` is monomorphic (see `Circuit/CVar`), the
tag is a nominal wrapper with a PRIVATE constructor, and introduction has exactly two
doors:

- `witness` at `Bool` — pays the `boolean` constraint through `CheckedType`; at
  `UnChecked Bool` it skips it, declared in the type. Both are verbatim PS (`xor_`
  witnesses its result at `UnChecked Boolean` for exactly this reason).
- `BoolVar.unchecked` — the single explicit rendering of PS's `coerce` introduction,
  for PURE retaggings only (a negation, a constant answer): each call site owes a
  booleanity argument from its surrounding constraints (e.g. `Snarky.equals_sound`).

(`CircuitType.fieldsToVar` at `Bool` also builds the wrapper — it must, `witness`
factors through it — but it is implementation surface, not a gadget door; PS has the
same shape, its `Bool` instance being itself a `coerce`.) -/
structure BoolVar (F : Type u) where
  private mk ::
  /-- The underlying field expression, constrained to `{0, 1}` by `CheckedType.check`. -/
  toCVar : CVar F

/-- Forgetting the tag is free: `↑b` eliminates a `BoolVar` to its field expression —
the direction PS coerces on every arithmetic operand. Only INTRODUCTION is guarded, and
deliberately not a coercion: the elaborator inserts `↑` silently on type mismatches,
which would turn any mistyped expression into an unchecked boolean. -/
instance : Coe (BoolVar F) (CVar F) := ⟨BoolVar.toCVar⟩

/-- Retag an expression as boolean WITHOUT a constraint — the explicit rendering of
PS's `coerce` introduction (see the `BoolVar` docstring). For pure retaggings whose
booleanity the caller's constraints already force; witnessed booleans go through
`witness` at `Bool` or `UnChecked Bool` instead. -/
def BoolVar.unchecked (x : CVar F) : BoolVar F := ⟨x⟩

/-- The field encoding of a boolean — the single entry of `CircuitType Bool`'s
`valueToFields`, named so the gadget laws can state their conclusions
through it (the relation the faithfulness arc composes over). -/
def bit [Zero F] [One F] (b : Bool) : F := if b then 1 else 0

instance [Zero F] [One F] [DecidableEq F] : CircuitType F Bool (BoolVar F) where
  size := 1
  valueToFields b := #v[bit b]
  fieldsToValue v := decide (v[0] ≠ 0)
  varToFields b := #v[b.toCVar]
  fieldsToVar v := ⟨v[0]⟩

/-- The encoding is multiplicative: bits multiply as booleans conjoin. -/
theorem bit_mul [MulZeroOneClass F] (a b : Bool) :
    (bit a : F) * bit b = bit (a && b) := by
  cases a <;> cases b <;> simp [bit]

/-- A field value that encodes a bit is `0` or `1`. -/
theorem bit_cases {av : F} {ab : Bool} [Zero F] [One F]
    (h : av = bit ab) : av = 0 ∨ av = 1 := by
  cases ab <;> simp [bit] at h <;> [exact Or.inl h; exact Or.inr h]

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

/-- Pairs encode as the concatenation of their components' encodings (PS `CircuitType`
instance for `Tuple`), first component first. -/
instance {a b av bv : Type u} [A : CircuitType F a av] [B : CircuitType F b bv] :
    CircuitType F (a × b) (av × bv) where
  size := A.size + B.size
  valueToFields p := A.valueToFields p.1 ++ B.valueToFields p.2
  fieldsToValue fs :=
    ( A.fieldsToValue ((fs.take A.size).cast (by omega)),
      B.fieldsToValue ((fs.drop A.size).cast (by omega)) )
  varToFields p := A.varToFields p.1 ++ B.varToFields p.2
  fieldsToVar fs :=
    ( A.fieldsToVar ((fs.take A.size).cast (by omega)),
      B.fieldsToVar ((fs.drop A.size).cast (by omega)) )

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
