import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.ZMod.Basic
import Pasta.CompElliptic
import Pasta.Shifted
import Snarky.Witness

/-!
# Shifted scalar types

Port of `Snarky.Types.Shifted`
(packages/snarky-kimchi/src/Snarky/Types/Shifted.purs): the wrappers marking a scalar
as SHIFTED — carried in a form whose true value the consuming ladder recovers.
`Type1 t` stands for the scalar `2·t + 2^n + 1` (`n` the field size in bits), the
representation used when the scalar field is no larger than the circuit field;
`varBaseMul`'s ladder consumes it. `SplitField (sDiv2, sOdd)` carries a scalar as a
half and a parity bit, standing for `2·sDiv2 + sOdd + 2^n`; `scaleFast2`'s ladder
consumes it.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- The carriers ported are the `Type1` newtype and the `SplitField` pair the `varBaseMul`
  laws speak about, and the `Type2` newtype the pickles verifiers unshift their deferred
  values through, each with its `fromShifted` decode; the circuit-side decodes
  `fromShiftedCircuit` are the affine unshifts. PS's `Shifted` class and the
  forbidden-values checks are consumed only by the pickles modules and arrive with them.
- PS bakes the width `n` into each field's `Shifted` instance (via `FieldSizeInBits`);
  the decodes here are generic, so `n` is an explicit argument.
-/

namespace Snarky

open CompElliptic.Fields.Pasta

/-- A scalar carried shifted (PS `Type1`): the wrapped value `t` stands for
`2·t + 2^n + 1`. Phantom: the ladder consuming it realizes the shift. -/
structure Type1 (α : Type u) where
  /-- The shifted representative. -/
  val : α

/-- The `Type1` decode (PS `fromShifted`): the representative `t` stands for
`2·t + 2^n + 1` (PS `shift1`: shift constant `2^n + 1`, scale `1/2`). `varBaseMul` is
an optimization that computes exactly the image of this operator, and the laws state
its results through it, over whichever ring the consumer reads in (`F` for the wire
pin, `ℤ` for the group scalar). -/
def Type1.fromShifted {R : Type u} [Semiring R] (n : ℕ) (t : Type1 R) : R :=
  Pasta.Shifted.unshiftType1 n t.val

/-- The `Type1` decode in circuit (PS `fromShiftedType1Circuit`): the affine `2·t + 2^n + 1`,
emitting no constraint. -/
def Type1.fromShiftedCircuit {F : Type} [Field F] [DecidableEq F] (n : ℕ)
    (t : Type1 (FVar F)) : FVar F :=
  CVar.add_ (CVar.scale_ 2 t.val) (.const (2 ^ n + 1))

/-- The circuit decode reads as the decode of the reading. -/
@[simp] theorem Type1.val_fromShiftedCircuit {F : Type} [Field F] [DecidableEq F] (n : ℕ)
    (t : Type1 (FVar F)) (V : Valuation F) :
    (Type1.fromShiftedCircuit n t).val V = Type1.fromShifted n ⟨t.val.val V⟩ := by
  simp [Type1.fromShiftedCircuit, Type1.fromShifted, Pasta.Shifted.unshiftType1, CVar.val,
    add_assoc]

/-- The `Type1` encode in circuit (PS `ofFieldType1Circuit`, OCaml `Type1.of_field`): the
affine `(s − 2^n − 1) / 2`, emitting no constraint. -/
def Type1.ofFieldCircuit {F : Type} [Field F] [DecidableEq F] (n : ℕ) (s : FVar F) : FVar F :=
  CVar.scale_ 2⁻¹ (CVar.sub_ s (.const (2 ^ n + 1)))

/-- The circuit encode reads as the encode of the reading. -/
@[simp] theorem Type1.val_ofFieldCircuit {F : Type} [Field F] [DecidableEq F] (n : ℕ)
    (s : FVar F) (V : Valuation F) :
    (Type1.ofFieldCircuit n s).val V = Pasta.Shifted.shiftType1 n (s.val V) := by
  simp only [Type1.ofFieldCircuit, CVar.val_scale_, CVar.val_sub_, CVar.val,
    Pasta.Shifted.shiftType1, div_eq_mul_inv]
  ring

/-- A scalar carried shifted by `2^n` (PS `Type2`): the wrapped value `t` stands for
`t + 2^n`, the representation used when the scalar field is the larger of the pair. -/
structure Type2 (α : Type u) where
  /-- The shifted representative. -/
  val : α

/-- The `Type2` decode (PS `fromShifted`): the representative `t` stands for `t + 2^n`. -/
def Type2.fromShifted {R : Type u} [Semiring R] (n : ℕ) (t : Type2 R) : R :=
  t.val + 2 ^ n

/-- The `Type2` decode in circuit (PS `fromShiftedType2Circuit`): the affine `t + 2^n`,
emitting no constraint. -/
def Type2.fromShiftedCircuit {F : Type} [Field F] (n : ℕ) (t : Type2 (FVar F)) : FVar F :=
  CVar.add_ t.val (.const (2 ^ n))

/-- The circuit decode reads as the decode of the reading. -/
@[simp] theorem Type2.val_fromShiftedCircuit {F : Type} [Field F] (n : ℕ) (t : Type2 (FVar F))
    (V : Valuation F) :
    (Type2.fromShiftedCircuit n t).val V = Type2.fromShifted n ⟨t.val.val V⟩ := by
  simp [Type2.fromShiftedCircuit, Type2.fromShifted, CVar.val]

/-- A scalar carried as a half and a parity bit (PS `SplitField`), standing shifted
for `2·sDiv2 + sOdd + 2^n`. Phantom like `Type1`: `scaleFast2`'s ladder realizes the
shift. -/
structure SplitField (α : Type u) (β : Type v) where
  /-- The halved representative. -/
  sDiv2 : α
  /-- The parity bit. -/
  sOdd : β

/-! ## The deployed Pasta codec

PS declares its `Shifted` codec (`toShifted`/`fromShifted`) per concrete field pair,
never over an abstract modulus pair. The pair the laws speak about is an `Fp` scalar
carried `Type1` in `Fq` (`p < q`, `n = 255`): shift by genuine field arithmetic in the
scalar field, transport across the boundary by canonical representative (PS
`toBigInt`/`fromBigInt`), and decode by the same `fromShifted` operator read over `ℤ`. -/

/-- The carrier is phantom: a `Type1` is its representative. -/
def Type1.equivCarrier {α : Type} : Type1 α ≃ α where
  toFun t := t.val
  invFun v := ⟨v⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A `Type1` encodes as its one cell (PS's generic instance). -/
instance instCircuitTypeType1 {F : Type} : CircuitType F (Type1 F) (Type1 (FVar F)) :=
  CircuitType.ofEquiv Type1.equivCarrier Type1.equivCarrier

/-- The integer a carried representative decodes to: `fromShifted` at `n = 255` over
`ℤ`, applied to the canonical representative — the scalar the consuming ladder computes
with (the `BigInt` stage of PS `fromShifted`). -/
def Type1.toScalarZ (t : Type1 Fq) : ℤ :=
  Type1.fromShifted 255 (⟨(t.val.val : ℤ)⟩ : Type1 ℤ)

end Snarky
