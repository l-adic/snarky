import Mathlib.Algebra.NeZero
import Mathlib.Logic.Equiv.Defs
import Snarky.CVar
import Snarky.Types.Vector

/-!
# Typed encodings

A value type's bidirectional encoding as field elements, its variable-bundle
counterpart, and the concrete encodings: field elements and booleans. Pure data — no
interpreter is in scope here.
-/

namespace Snarky

universe u v

/-- A bidirectional encoding of a value type `val` as `size` field elements, together
with its variable-bundle counterpart `var`, and its round-trip laws. -/
class CircuitType (F : Type u) (val : Type u) (var : outParam (Type u)) where
  /-- The number of field elements a `val` encodes to. -/
  size : Nat
  /-- Encode a value as its `size` field elements. -/
  valueToFields : val → Vector F size
  /-- Decode a value from its `size` field elements. -/
  fieldsToValue : Vector F size → val
  /-- Flatten a variable bundle into its `size` underlying `CVar`s. -/
  varToFields : var → Vector (CVar F) size
  /-- Rebuild a variable bundle from `size` underlying `CVar`s. -/
  fieldsToVar : Vector (CVar F) size → var
  /-- Decoding an encoded value gives it back. -/
  value_roundTrip : ∀ a : val, fieldsToValue (valueToFields a) = a
  /-- Flattening a rebuilt variable bundle gives the `CVar`s back. -/
  var_roundTrip : ∀ cvs : Vector (CVar F) size, varToFields (fieldsToVar cvs) = cvs

section FVar

variable {F : Type}

instance instCircuitTypeFVar : CircuitType F F (FVar F) where
  size := 1
  valueToFields x := #v[x]
  fieldsToValue v := v[0]
  varToFields x := #v[x]
  fieldsToVar v := v[0]
  value_roundTrip _ := rfl
  var_roundTrip := vector_singleton_eta

@[simp] theorem CircuitType.fieldsToVar_fvar (v : Vector (CVar F) 1) :
    CircuitType.fieldsToVar (val := F) v = v[0] := rfl

end FVar

section BoolVar

variable {F : Type u}

/-- A field expression tagged as boolean. Only introduction is guarded — and
deliberately not a coercion: the elaborator inserts `↑` silently on type mismatches,
which would turn any mistyped expression into an unchecked boolean. -/
structure BoolVar (F : Type u) where
  private mk ::
  /-- The underlying field expression. -/
  toCVar : CVar F

/-- Forgetting the tag is free: `↑b` eliminates a `BoolVar` to its field expression. -/
instance : Coe (BoolVar F) (CVar F) := ⟨BoolVar.toCVar⟩

/-- Retag an expression as boolean without a constraint — for expressions whose
booleanity the caller's constraints already force. -/
def BoolVar.unchecked (x : CVar F) : BoolVar F := ⟨x⟩

/-- Retagging is invisible to the field reading. -/
@[simp] theorem BoolVar.coe_unchecked (x : CVar F) :
    ((BoolVar.unchecked x : BoolVar F) : CVar F) = x := rfl

/-- The field encoding of a boolean. -/
def bit [Zero F] [One F] (b : Bool) : F := if b then 1 else 0

end BoolVar

section BoolVarInstance

variable {F : Type}

instance instCircuitTypeBool [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)] :
    CircuitType F Bool (BoolVar F) where
  size := 1
  valueToFields b := #v[bit b]
  fieldsToValue v := decide (v[0] ≠ 0)
  varToFields b := #v[b.toCVar]
  fieldsToVar v := ⟨v[0]⟩
  value_roundTrip b := by cases b <;> simp [bit]
  var_roundTrip := vector_singleton_eta

end BoolVarInstance

section Unit

variable {F : Type}

/-- The empty encoding. -/
instance instCircuitTypeUnit : CircuitType F Unit Unit where
  size := 0
  valueToFields _ := #v[]
  fieldsToValue _ := ()
  varToFields _ := #v[]
  fieldsToVar _ := ()
  value_roundTrip _ := rfl
  var_roundTrip v := by ext i hi; exact absurd hi (Nat.not_lt_zero _)

@[simp] theorem CircuitType.varToFields_unit :
    CircuitType.varToFields (F := F) (val := Unit) () = #v[] := rfl

@[simp] theorem CircuitType.valueToFields_unit :
    CircuitType.valueToFields (F := F) (var := Unit) () = #v[] := rfl

end Unit

/-! ## The product former -/

section Product

variable {F a va b vb : Type u}

/-- Encodings multiply: the fields concatenate. -/
instance instCircuitTypeProd [CircuitType F a va] [CircuitType F b vb] :
    CircuitType F (a × b) (va × vb) where
  size := CircuitType.size F a + CircuitType.size F b
  valueToFields p := CircuitType.valueToFields p.1 ++ CircuitType.valueToFields p.2
  fieldsToValue f :=
    (CircuitType.fieldsToValue (splitVec f).1, CircuitType.fieldsToValue (splitVec f).2)
  varToFields p := CircuitType.varToFields (val := a) p.1 ++ CircuitType.varToFields (val := b) p.2
  fieldsToVar f :=
    (CircuitType.fieldsToVar (val := a) (splitVec f).1, CircuitType.fieldsToVar (val := b)
      (splitVec f).2)
  value_roundTrip p := by
    obtain ⟨x, y⟩ := p
    show (CircuitType.fieldsToValue (splitVec (CircuitType.valueToFields (F := F) x
        ++ CircuitType.valueToFields (F := F) y)).1, CircuitType.fieldsToValue (splitVec
        (CircuitType.valueToFields (F := F) x ++ CircuitType.valueToFields (F := F) y)).2)
      = (x, y)
    rw [splitVec_append, CircuitType.value_roundTrip, CircuitType.value_roundTrip]
  var_roundTrip f := by
    show CircuitType.varToFields (F := F) (val := a) (CircuitType.fieldsToVar (splitVec f).1)
        ++ CircuitType.varToFields (F := F) (val := b) (CircuitType.fieldsToVar (splitVec f).2) = f
    rw [CircuitType.var_roundTrip, CircuitType.var_roundTrip, append_splitVec]

@[simp] theorem CircuitType.size_prod [CircuitType F a va] [CircuitType F b vb] :
    CircuitType.size F (a × b) = CircuitType.size F a + CircuitType.size F b := rfl

@[simp] theorem CircuitType.valueToFields_prod [CircuitType F a va] [CircuitType F b vb]
    (x : a) (y : b) :
    CircuitType.valueToFields (F := F) (var := va × vb) (x, y)
      = CircuitType.valueToFields (F := F) x ++ CircuitType.valueToFields (F := F) y := rfl

@[simp] theorem CircuitType.varToFields_prod [CircuitType F a va] [CircuitType F b vb]
    (v : va) (w : vb) :
    CircuitType.varToFields (F := F) (val := a × b) (v, w)
      = CircuitType.varToFields (F := F) (val := a) v
        ++ CircuitType.varToFields (F := F) (val := b) w := rfl

@[simp] theorem CircuitType.fieldsToValue_prod [CircuitType F a va] [CircuitType F b vb]
    (f : Vector F (CircuitType.size F a + CircuitType.size F b)) :
    CircuitType.fieldsToValue (F := F) (var := va × vb) f
      = (CircuitType.fieldsToValue (F := F) (var := va) (splitVec f).1,
         CircuitType.fieldsToValue (F := F) (var := vb) (splitVec f).2) := rfl

end Product

/-! ## The vector former -/

section VectorFormer

variable {F a va : Type u}

/-- Encodings iterate: the entries' fields flatten. -/
instance instCircuitTypeVector [CircuitType F a va] {n : Nat} :
    CircuitType F (Vector a n) (Vector va n) where
  size := n * CircuitType.size F a
  valueToFields xs := (mapVec CircuitType.valueToFields xs).flatten
  fieldsToValue f := mapVec CircuitType.fieldsToValue (chunkVec f)
  varToFields vs := (mapVec (CircuitType.varToFields (val := a)) vs).flatten
  fieldsToVar f := mapVec (CircuitType.fieldsToVar (val := a)) (chunkVec f)
  value_roundTrip xs := by
    show mapVec CircuitType.fieldsToValue
      (chunkVec (mapVec (CircuitType.valueToFields (F := F)) xs).flatten) = xs
    rw [chunkVec_flatten]
    ext i hi
    simp [CircuitType.value_roundTrip]
  var_roundTrip f := by
    show (mapVec (CircuitType.varToFields (F := F) (val := a))
      (mapVec (CircuitType.fieldsToVar (F := F) (val := a)) (chunkVec f))).flatten = f
    have h : mapVec (CircuitType.varToFields (F := F) (val := a))
        (mapVec (CircuitType.fieldsToVar (F := F) (val := a)) (chunkVec f)) = chunkVec f := by
      ext i hi
      simp [CircuitType.var_roundTrip]
    rw [h, flatten_chunkVec]

@[simp] theorem CircuitType.size_vector [CircuitType F a va] {n : Nat} :
    CircuitType.size F (Vector a n) = n * CircuitType.size F a := rfl

@[simp] theorem CircuitType.valueToFields_vector [CircuitType F a va] {n : Nat} (xs : Vector a n) :
    CircuitType.valueToFields (F := F) (var := Vector va n) xs
      = (mapVec (CircuitType.valueToFields (F := F)) xs).flatten := rfl

@[simp] theorem CircuitType.varToFields_vector [CircuitType F a va] {n : Nat} (vs : Vector va n) :
    CircuitType.varToFields (F := F) (val := Vector a n) vs
      = (mapVec (CircuitType.varToFields (F := F) (val := a)) vs).flatten := rfl

@[simp] theorem CircuitType.fieldsToValue_vector [CircuitType F a va] {n : Nat}
    (f : Vector F (n * CircuitType.size F a)) :
    CircuitType.fieldsToValue (F := F) (var := Vector va n) f
      = mapVec (CircuitType.fieldsToValue (F := F) (var := va)) (chunkVec f) := rfl

end VectorFormer

/-! ## Transport along an equivalence -/

section UnChecked

variable {F val var : Type}

/-- Wrap a bundle to void its check: the encoding is the wrapped one, and the
`CheckedType` instance emits nothing. For values whose constraints are guaranteed
elsewhere. -/
structure UnChecked (α : Type u) where
  /-- The wrapped value or variable bundle. -/
  val : α

/-- The wrapper is invisible to the encoding. -/
instance instCircuitTypeUnChecked [inst : CircuitType F val var] :
    CircuitType F (UnChecked val) (UnChecked var) where
  size := inst.size
  valueToFields v := inst.valueToFields v.val
  fieldsToValue fs := ⟨inst.fieldsToValue fs⟩
  varToFields v := inst.varToFields v.val
  fieldsToVar fs := ⟨inst.fieldsToVar fs⟩
  value_roundTrip v := congrArg UnChecked.mk (inst.value_roundTrip v.val)
  var_roundTrip cvs := inst.var_roundTrip cvs

end UnChecked

section Equiv

variable {F a va b vb : Type u}

/-- A type isomorphic to an encoded type is encoded through the isomorphism — a struct's
instance, derived from its product decomposition. -/
@[reducible] def CircuitType.ofEquiv [inst : CircuitType F a va] (ev : b ≃ a) (ew : vb ≃ va) :
    CircuitType F b vb where
  size := inst.size
  valueToFields x := inst.valueToFields (ev x)
  fieldsToValue f := ev.symm (inst.fieldsToValue f)
  varToFields v := inst.varToFields (ew v)
  fieldsToVar f := ew.symm (inst.fieldsToVar f)
  value_roundTrip x := by simp [inst.value_roundTrip]
  var_roundTrip f := by simp [inst.var_roundTrip]

/-- A shape over leaf types — a struct polymorphic in its entries — decomposed once,
`S a ≃ T a` at every `a`: its encoding at a leaf is the decomposition's, applied at the
value and at the bundle. -/
@[reducible] def CircuitType.ofShape {S T : Type u → Type u} {val var : Type u}
    [CircuitType F (T val) (T var)] (e : ∀ a, S a ≃ T a) : CircuitType F (S val) (S var) :=
  CircuitType.ofEquiv (e val) (e var)

end Equiv

end Snarky
