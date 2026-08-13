import Snarky.Circuit.CVar

/-!
# Circuit types

Port of `Snarky.Circuit.Types` (packages/snarky/src/Snarky/Circuit/Types.purs): the
value/variable duality — `CircuitType` encodes a value type as field elements and pairs it
with its variable-bundle form — plus the `FVar`/`BoolVar` base instances and their
round-trip laws.

Deviations from the PS original (ledger: `formal/docs/snarky-ps-alignment.md`):
- The field-vector size is type-level (`Vector F size` vs PS `Array f` + the runtime
  `sizeInFields` contract), so the length obligations disappear; the `outParam` on `var`
  models the PS fundep `a f -> var`, while the reverse fundep `var -> f` is not modeled.
- The PS value wrappers `F f` and `Bool a` are not needed: Lean's class resolution
  dispatches on the plain field type and core `Bool` directly, so `val` is unwrapped. The
  wrapper-lifting instances (`PrimeField (F f)`, `HasEndo (F f)`, `FieldSizeInBits (F f)`)
  therefore have no analogue.
- Instance coverage is the base pair (`F`, `Bool`), `Prod` (PS `Tuple`), sized
  vectors (PS `Vector`), and the size-0 `PUnit` (PS `Unit`); the PS
  `NoInput`/`NoOutput`, `Const`, `Product`, and `Record` instances are not yet
  ported. `UnChecked` is here.
- The generic/rowlist deriving machinery (`GCircuitType`/`RCircuitType`, the `generic*`
  helpers) is not ported — Lean would grow a `deriving` handler instead.
- `CheckedType` is not here: its PS home is `Circuit/DSL/Monad.purs`.

The round-trip laws (`fvar_value_roundTrip`, `fvar_var_roundTrip`,
`boolVar_value_roundTrip`, `boolVar_var_roundTrip`) are the PS
`Test.Snarky.Circuit.Types` QuickCheck spec as theorems, for the instances above.
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
  booleanity argument from its surrounding constraints.

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

/-- Retagging is invisible to the field reading: `↑(unchecked x)` is `x`. -/
@[circuitVal] theorem BoolVar.toCVar_unchecked (x : CVar F) :
    (BoolVar.unchecked x).toCVar = x := rfl

-- `CVar.val`'s equations fire on constructors only, so an opaque operand is left
-- alone. Tagged here because a simp attribute cannot be used in its declaring file.
attribute [circuitVal] CVar.val

/-- The field encoding of a boolean — the single entry of `CircuitType Bool`'s
`valueToFields`. -/
def bit [Zero F] [One F] (b : Bool) : F := if b then 1 else 0

instance [Zero F] [One F] [DecidableEq F] : CircuitType F Bool (BoolVar F) where
  size := 1
  valueToFields b := #v[bit b]
  fieldsToValue v := decide (v[0] ≠ 0)
  varToFields b := #v[b.toCVar]
  fieldsToVar v := ⟨v[0]⟩

/-- The encoding of `true`. -/
@[circuitVal] theorem bit_true [Zero F] [One F] : (bit true : F) = 1 := rfl

/-- The encoding of `false`. -/
@[circuitVal] theorem bit_false [Zero F] [One F] : (bit false : F) = 0 := rfl

/-- The encoding is multiplicative: bits multiply as booleans conjoin. -/
@[circuitVal] theorem bit_mul [MulZeroOneClass F] (a b : Bool) :
    (bit a : F) * bit b = bit (a && b) := by
  cases a <;> cases b <;> simp [bit]

/-- The encoding is injective where `1 ≠ 0`: a field value encodes at most one bit. -/
theorem bit_inj [Zero F] [One F] (h1 : (1 : F) ≠ 0) {a b : Bool}
    (h : (bit a : F) = bit b) : a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd h.symm h1
  · exact absurd h h1
  · rfl

/-- A field value that encodes a bit is `0` or `1`. -/
theorem bit_cases {av : F} {ab : Bool} [Zero F] [One F]
    (h : av = bit ab) : av = 0 ∨ av = 1 := by
  cases ab <;> simp [bit] at h <;> [exact Or.inl h; exact Or.inr h]

/-- Wrap a type to skip its `check` constraints (PS `UnChecked a`): the encoding
delegates to the wrapped instance, and the `CheckedType` instance is a no-op. Use when
the constraints are guaranteed elsewhere. -/
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

/-- The size-0 encoding (PS `CircuitType f Unit Unit`): the interface type of a
statement input or output that carries nothing. A circuit compiled at output `PUnit`
claims NO public output slots — how a pure knowledge statement (assert, return nothing)
is expressed. -/
instance : CircuitType F PUnit PUnit where
  size := 0
  valueToFields _ := #v[]
  fieldsToValue _ := PUnit.unit
  varToFields _ := #v[]
  fieldsToVar _ := PUnit.unit

/-- Element `i`'s block sits inside the flattening: the index bound of the vector
instance's decode direction. -/
private theorem mul_add_lt {i j n sz : Nat} (hi : i < n) (hj : j < sz) :
    i * sz + j < n * sz :=
  calc i * sz + j < (i + 1) * sz := by rw [Nat.succ_mul]; omega
    _ ≤ n * sz := Nat.mul_le_mul_right sz hi

/-- Sized vectors encode as the concatenation of their elements' encodings, in index
order (PS `CircuitType` instance for `Vector`); decoding reads element `i`'s fields
back off block `i`. -/
instance instCircuitTypeVector {val var : Type u} [A : CircuitType F val var]
    {n : Nat} : CircuitType F (Vector val n) (Vector var n) where
  size := n * A.size
  valueToFields v := (v.map A.valueToFields).flatten
  fieldsToValue fs := Vector.ofFn fun i =>
    A.fieldsToValue (Vector.ofFn fun j =>
      fs[i.1 * A.size + j.1]'(mul_add_lt i.isLt j.isLt))
  varToFields v := (v.map A.varToFields).flatten
  fieldsToVar fs := Vector.ofFn fun i =>
    A.fieldsToVar (Vector.ofFn fun j =>
      fs[i.1 * A.size + j.1]'(mul_add_lt i.isLt j.isLt))

/-! ## Round-trip laws

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

/-! ## The encoding laws -/

/-- The encoding laws of a `CircuitType`: decoding inverts encoding, on the value and
the variable side. A separate `Prop` class over the operational one (the
`LawfulBasicSystem` pattern) because the base instances are total while a law can
carry a genuine extra hypothesis — `Bool`'s value law needs a nontrivial ring, since
one field element cannot encode two values when `0 = 1`. -/
class LawfulCircuitType (F val var : Type) [CircuitType F val var] : Prop where
  /-- Decoding an encoded value gives it back. -/
  value_roundTrip : ∀ v : val,
    CircuitType.fieldsToValue (F := F) (var := var)
      (CircuitType.valueToFields (F := F) (var := var) v) = v
  /-- Flattening a rebuilt variable bundle gives the `CVar`s back — the inverse the
  witness leaf reads through, since a witnessed bundle is built by `fieldsToVar`. -/
  vars_roundTrip : ∀ cvs : Vector (CVar F) (CircuitType.size F val),
    CircuitType.varToFields (F := F) (val := val)
      (CircuitType.fieldsToVar (F := F) (val := val) cvs) = cvs

/-- A one-entry vector is its own entry's singleton. -/
private theorem vector_singleton_eta {α : Type u} (v : Vector α 1) : #v[v[0]] = v := by
  ext i hi
  have : i = 0 := by omega
  subst this
  simp

instance instLawfulCircuitTypeF : LawfulCircuitType F F (FVar F) :=
  ⟨fvar_value_roundTrip, vector_singleton_eta⟩

instance instLawfulCircuitTypeBool [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)] :
    LawfulCircuitType F Bool (BoolVar F) :=
  ⟨boolVar_value_roundTrip, vector_singleton_eta⟩

instance instLawfulCircuitTypeUnChecked {val var : Type} [CircuitType F val var]
    [LawfulCircuitType F val var] :
    LawfulCircuitType F (UnChecked val) (UnChecked var) where
  value_roundTrip v := congrArg UnChecked.mk (LawfulCircuitType.value_roundTrip v.val)
  vars_roundTrip cvs := LawfulCircuitType.vars_roundTrip (val := val) cvs

/-- Taking a concatenation's first block gives it back. -/
private theorem cast_take_append {α : Type u} {m k : Nat} (v : Vector α m)
    (w : Vector α k) {h : min m (m + k) = m} : ((v ++ w).take m).cast h = v := by
  ext i hi
  simp [hi]

/-- Dropping a concatenation's first block leaves the second. -/
private theorem cast_drop_append {α : Type u} {m k : Nat} (v : Vector α m)
    (w : Vector α k) {h : m + k - m = k} : ((v ++ w).drop m).cast h = w := by
  ext i hi
  simp

/-- A vector is its first `m` entries followed by the rest. -/
private theorem take_append_drop {α : Type u} {m k : Nat} (fs : Vector α (m + k))
    {h₁ : min m (m + k) = m} {h₂ : m + k - m = k} :
    ((fs.take m).cast h₁ ++ (fs.drop m).cast h₂) = fs := by
  ext i hi
  simp only [Vector.getElem_append, Vector.getElem_cast, Vector.getElem_take,
    Vector.getElem_drop]
  split
  · rfl
  · congr 1
    omega

instance instLawfulCircuitTypeProd {a b av bv : Type} [A : CircuitType F a av]
    [B : CircuitType F b bv] [LawfulCircuitType F a av] [LawfulCircuitType F b bv] :
    LawfulCircuitType F (a × b) (av × bv) where
  value_roundTrip p := by
    show (A.fieldsToValue
          (((A.valueToFields p.1 ++ B.valueToFields p.2).take A.size).cast _),
        B.fieldsToValue
          (((A.valueToFields p.1 ++ B.valueToFields p.2).drop A.size).cast _)) = p
    rw [cast_take_append, cast_drop_append, LawfulCircuitType.value_roundTrip,
      LawfulCircuitType.value_roundTrip]
  vars_roundTrip cvs := by
    show A.varToFields (A.fieldsToVar _) ++ B.varToFields (B.fieldsToVar _) = cvs
    rw [LawfulCircuitType.vars_roundTrip (val := a),
      LawfulCircuitType.vars_roundTrip (val := b), take_append_drop]

instance instLawfulCircuitTypeVector {val var : Type} [A : CircuitType F val var]
    [LawfulCircuitType F val var] {n : Nat} :
    LawfulCircuitType F (Vector val n) (Vector var n) where
  value_roundTrip v := by
    ext i hi
    show (Vector.ofFn fun i' : Fin n =>
        A.fieldsToValue (Vector.ofFn fun j : Fin A.size =>
          ((v.map A.valueToFields).flatten)[i'.1 * A.size + j.1]'(
            mul_add_lt i'.isLt j.isLt)))[i]
      = v[i]
    simp only [Vector.getElem_ofFn]
    have hinner : (Vector.ofFn fun j : Fin A.size =>
        ((v.map A.valueToFields).flatten)[i * A.size + j.1]'(mul_add_lt hi j.isLt))
        = A.valueToFields v[i] := by
      ext j hj
      have hdiv : (i * A.size + j) / A.size = i := by
        rw [Nat.mul_comm i A.size, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj,
          Nat.add_zero]
      have hmod : (i * A.size + j) % A.size = j := by
        rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hj]
      simp only [Vector.getElem_ofFn, Vector.getElem_flatten, Vector.getElem_map,
        hdiv, hmod]
    rw [hinner]
    exact LawfulCircuitType.value_roundTrip v[i]
  vars_roundTrip cvs := by
    ext i hi
    show ((Vector.ofFn fun i' : Fin n =>
        A.fieldsToVar (Vector.ofFn fun j : Fin A.size =>
          cvs[i'.1 * A.size + j.1]'(mul_add_lt i'.isLt j.isLt))).map
        A.varToFields).flatten[i]
      = cvs[i]
    simp only [Vector.getElem_flatten, Vector.getElem_map, Vector.getElem_ofFn]
    simp only [LawfulCircuitType.vars_roundTrip (val := val), Vector.getElem_ofFn]
    congr 1
    exact Nat.div_add_mod' i A.size

end Snarky
