import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.ZMod.Basic
import Pasta.CompElliptic
import Pasta.Shifted
import Snarky.Witness

/-!
# Shifted scalar types

Port of packages/snarky-kimchi/src/Snarky/Types/Shifted.purs: wrappers marking a scalar as
shifted, carried in a form whose true value the consuming ladder recovers (`n` is the field
size in bits).

- `Type1 t` stands for `2·t + 2^n + 1`, used when the scalar field is no larger than the
  circuit field; `varBaseMul` consumes it.
- `Type2 t` stands for `t + 2^n`, used when the scalar field is the larger of the pair.
- `SplitField (sDiv2, sOdd)` stands for `2·sDiv2 + sOdd + 2^n`; `scaleFast2` consumes it.

The decodes are generic over the ring, so `n` is an explicit argument; the circuit decodes
are affine and emit no constraint.
-/

namespace Snarky

open CompElliptic.Fields.Pasta

/-- A scalar carried shifted: the wrapped value `t` stands for `2·t + 2^n + 1`. Phantom: the
ladder consuming it realizes the shift. -/
structure Type1 (α : Type u) where
  /-- The shifted representative. -/
  val : α

/-- The `Type1` decode `2·t + 2^n + 1`, over any semiring: the circuit field for a wire,
`ℤ` for a group scalar. -/
def Type1.fromShifted {R : Type u} [Semiring R] (n : ℕ) (t : Type1 R) : R :=
  Pasta.Shifted.unshiftType1 n t.val

/-- The `Type1` decode in circuit: the affine `2·t + 2^n + 1`, emitting no constraint. -/
def Type1.fromShiftedCircuit {F : Type} [Field F] [DecidableEq F] (n : ℕ)
    (t : Type1 (FVar F)) : FVar F :=
  CVar.add_ (CVar.scale_ 2 t.val) (.const (2 ^ n + 1))

/-- The circuit decode reads as the decode of the reading. -/
@[simp] theorem Type1.val_fromShiftedCircuit {F : Type} [Field F] [DecidableEq F] (n : ℕ)
    (t : Type1 (FVar F)) (V : Valuation F) :
    (Type1.fromShiftedCircuit n t).val V = Type1.fromShifted n ⟨t.val.val V⟩ := by
  simp [Type1.fromShiftedCircuit, Type1.fromShifted, Pasta.Shifted.unshiftType1, CVar.val,
    add_assoc]

/-- The `Type1` encode in circuit: the affine `(s − 2^n − 1) / 2`, emitting no constraint. -/
def Type1.ofFieldCircuit {F : Type} [Field F] [DecidableEq F] (n : ℕ) (s : FVar F) : FVar F :=
  CVar.scale_ 2⁻¹ (CVar.sub_ s (.const (2 ^ n + 1)))

/-- The circuit encode reads as the encode of the reading. -/
@[simp] theorem Type1.val_ofFieldCircuit {F : Type} [Field F] [DecidableEq F] (n : ℕ)
    (s : FVar F) (V : Valuation F) :
    (Type1.ofFieldCircuit n s).val V = Pasta.Shifted.shiftType1 n (s.val V) := by
  simp only [Type1.ofFieldCircuit, CVar.val_scale_, CVar.val_sub_, CVar.val,
    Pasta.Shifted.shiftType1, div_eq_mul_inv]
  ring

/-- A scalar carried shifted by `2^n`: the wrapped value `t` stands for `t + 2^n`. -/
structure Type2 (α : Type u) where
  /-- The shifted representative. -/
  val : α

/-- The `Type2` decode `t + 2^n`. -/
def Type2.fromShifted {R : Type u} [Semiring R] (n : ℕ) (t : Type2 R) : R :=
  t.val + 2 ^ n

/-- The `Type2` decode in circuit: the affine `t + 2^n`, emitting no constraint. -/
def Type2.fromShiftedCircuit {F : Type} [Field F] (n : ℕ) (t : Type2 (FVar F)) : FVar F :=
  CVar.add_ t.val (.const (2 ^ n))

/-- The circuit decode reads as the decode of the reading. -/
@[simp] theorem Type2.val_fromShiftedCircuit {F : Type} [Field F] (n : ℕ) (t : Type2 (FVar F))
    (V : Valuation F) :
    (Type2.fromShiftedCircuit n t).val V = Type2.fromShifted n ⟨t.val.val V⟩ := by
  simp [Type2.fromShiftedCircuit, Type2.fromShifted, CVar.val]

/-- A scalar carried as a half and a parity bit, standing for `2·sDiv2 + sOdd + 2^n`.
Phantom like `Type1`: `scaleFast2`'s ladder realizes the shift. -/
structure SplitField (α : Type u) (β : Type v) where
  /-- The halved representative. -/
  sDiv2 : α
  /-- The parity bit. -/
  sOdd : β

/-! ## The deployed Pasta codec

The deployed pair is an `Fp` scalar carried `Type1` in `Fq` (`p < q`, `n = 255`). -/

/-- The carrier is phantom: a `Type1` is its representative. -/
def Type1.equivCarrier {α : Type} : Type1 α ≃ α where
  toFun t := t.val
  invFun v := ⟨v⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A `Type1` encodes as its one cell. -/
instance instCircuitTypeType1 {F : Type} : CircuitType F (Type1 F) (Type1 (FVar F)) :=
  CircuitType.ofEquiv Type1.equivCarrier Type1.equivCarrier

/-- The integer scalar a `Type1 Fq` stands for: `Type1.fromShifted 255` over `ℤ` at the
canonical representative. -/
def Type1.toScalarZ (t : Type1 Fq) : ℤ :=
  Type1.fromShifted 255 (⟨(t.val.val : ℤ)⟩ : Type1 ℤ)

end Snarky
