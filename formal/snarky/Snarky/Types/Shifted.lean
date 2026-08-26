import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.ZMod.Basic
import Pasta.CompElliptic
import Snarky.Encoding

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
- Only the shifted carriers the `varBaseMul` laws speak about are ported: the `Type1`
  newtype and the `SplitField` pair, each with its `fromShifted` decode. PS's `Type2`
  newtype (whose decode delegates to `SplitField`'s), the `Shifted` class, the
  forbidden-values checks, and the shifted circuit ops are consumed only by the
  pickles modules and arrive with them.
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
  2 * t.val + 2 ^ n + 1

/-- A scalar carried as a half and a parity bit (PS `SplitField`), standing shifted
for `2·sDiv2 + sOdd + 2^n`. Phantom like `Type1`: `scaleFast2`'s ladder realizes the
shift. -/
structure SplitField (α : Type u) (β : Type v) where
  /-- The halved representative. -/
  sDiv2 : α
  /-- The parity bit. -/
  sOdd : β

/-- The `SplitField` decode (PS `fromShifted`; PS `Type2`'s delegates to it): the
pair stands for `2·sDiv2 + sOdd + 2^n`. `scaleFast2` computes exactly its image, and
its law states the result through it. -/
def SplitField.fromShifted {R : Type u} [Semiring R] (n : ℕ) (s : SplitField R Bool) : R :=
  2 * s.sDiv2 + (if s.sOdd then 1 else 0) + 2 ^ n

/-! ## The deployed Pasta codec

PS declares its `Shifted` codec (`toShifted`/`fromShifted`) per concrete field pair,
never over an abstract modulus pair. The pair the laws speak about is an `Fp` scalar
carried `Type1` in `Fq` (`p < q`, `n = 255`): shift by genuine field arithmetic in the
scalar field, transport across the boundary by canonical representative (PS
`toBigInt`/`fromBigInt`), and decode by the same `fromShifted` operator read over `ℤ`. -/

/-- The carrier is phantom: a `Type1` is its representative. -/
@[simps apply symm_apply] def Type1.equivCarrier {α : Type} : Type1 α ≃ α where
  toFun t := t.val
  invFun v := ⟨v⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A `Type1` encodes as its one cell (PS's generic instance). -/
instance instCircuitTypeType1 {F : Type} : CircuitType F (Type1 F) (Type1 (FVar F)) :=
  CircuitType.ofEquiv Type1.equivCarrier Type1.equivCarrier

/-- The deployed encode (PS `toShifted` at `Fp → Type1 Fq`): shift in the scalar
field — `(s − 2^255 − 1) / 2` — and carry the canonical representative across the
boundary. -/
def Type1.toShifted (s : Fp) : Type1 Fq :=
  ⟨(((s - 2 ^ 255 - 1) / 2 : Fp).val : Fq)⟩

/-- The integer a carried representative decodes to: `fromShifted` at `n = 255` over
`ℤ`, applied to the canonical representative — the scalar the consuming ladder computes
with (the `BigInt` stage of PS `fromShifted`). -/
def Type1.toScalarZ (t : Type1 Fq) : ℤ :=
  Type1.fromShifted 255 (⟨(t.val.val : ℤ)⟩ : Type1 ℤ)

/-- The deployed decode (PS `fromShifted` at `Type1 Fq → Fp`): the decode integer
reduced into the scalar field. -/
def Type1.toScalar (t : Type1 Fq) : Fp :=
  (t.toScalarZ : Fp)

/-- The round trip: the encode's decode is the encoded scalar. -/
theorem Type1.toScalar_toShifted (z : Fp) : (Type1.toShifted z).toScalar = z := by
  set t : Fp := (z - 2 ^ 255 - 1) / 2 with ht
  have htq : ((t.val : Fq)).val = t.val := by
    rw [ZMod.val_natCast,
      Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt t) (by decide))]
  have hback : ((t.val : ℕ) : Fp) = t := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  simp only [Type1.toScalar, Type1.toScalarZ, Type1.toShifted, Type1.fromShifted,
    ← ht, htq]
  push_cast
  rw [hback, ht]
  have hhalf : (2 : Fp) * ((z - 2 ^ 255 - 1) / 2) = z - 2 ^ 255 - 1 := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ (by decide)
  rw [hhalf]
  ring


end Snarky
