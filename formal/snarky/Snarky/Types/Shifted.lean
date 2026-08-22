import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Pasta.CompElliptic
import Pasta.Shifted

/-!
# Shifted scalar types

Port of `Snarky.Types.Shifted`
(packages/snarky-kimchi/src/Snarky/Types/Shifted.purs): the wrappers marking a scalar
as SHIFTED — carried in a form whose true value the consuming ladder recovers.
`Type1 t` stands for the scalar `2·t + 2^n + 1` (`n` the field size in bits), the
representation used when the scalar field is no larger than the circuit field;
`varBaseMul`'s ladder consumes it. The decode polynomial itself is
`Pasta.Shifted.unshiftType1`, the `Shifted_value` algebra the gate semantics already
read through (`scaleFast2`'s split scalar reads through `unshiftType2` the same way).

PS declares its `Shifted` codec (`toShifted`/`fromShifted`) per concrete field pair,
never over an abstract modulus pair. The pair the laws speak about is
`Shifted (F Vesta.ScalarField) (Type1 (F Vesta.BaseField))` — an `Fp` scalar carried
`Type1` in `Fq` (`p < q`, `n = 255`), shifted by genuine field arithmetic
(`scale = recip 2`) and transported across the boundary by canonical representative
(PS `toBigInt`/`fromBigInt`). `Type1.toShifted`/`Type1.fromShifted` port exactly that
instance; the round trip `fromShifted_toShifted` needs no hypotheses.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
only the shifted carrier the `varBaseMul` laws speak about is ported: the `Type1`
newtype with the deployed codec. PS's `SplitField` pair and `Type2` newtype (the
gadget takes the split scalar as two arguments), the same-field `Shifted` instances,
the class packaging, the forbidden-values checks, and the shifted circuit ops are
consumed only by the pickles modules and arrive with them.
-/

namespace Snarky

open CompElliptic.Fields.Pasta Pasta.Shifted

/-- A scalar carried shifted (PS `Type1`): the wrapped value `t` stands for
`unshiftType1 n t = 2·t + 2^n + 1`. Phantom: the ladder consuming it realizes the
shift. -/
structure Type1 (α : Type u) where
  /-- The shifted representative. -/
  val : α

/-- The deployed encode (PS `toShifted` at `Fp → Type1 Fq`): shift in the scalar
field — `(s − 2^255 − 1) / 2` — and carry the canonical representative across the
boundary. -/
def Type1.toShifted (s : Fp) : Type1 Fq :=
  ⟨(((s - 2 ^ 255 - 1) / 2 : Fp).val : Fq)⟩

/-- The integer a carried representative decodes to: the unshift of the canonical
representative — the scalar the consuming ladder computes with (the `BigInt` stage
of PS `fromShifted`). -/
def Type1.fromShiftedZ (t : Type1 Fq) : ℤ :=
  unshiftType1 255 (t.val.val : ℤ)

/-- The deployed decode (PS `fromShifted` at `Type1 Fq → Fp`): the decode integer
reduced into the scalar field. -/
def Type1.fromShifted (t : Type1 Fq) : Fp :=
  (t.fromShiftedZ : Fp)

/-- The round trip: the encode's decode is the encoded scalar. -/
theorem Type1.fromShifted_toShifted (z : Fp) : (Type1.toShifted z).fromShifted = z := by
  set t : Fp := (z - 2 ^ 255 - 1) / 2 with ht
  have htq : ((t.val : Fq)).val = t.val := by
    rw [ZMod.val_natCast,
      Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt t) (by decide))]
  have hback : ((t.val : ℕ) : Fp) = t := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  simp only [Type1.fromShifted, Type1.fromShiftedZ, Type1.toShifted, unshiftType1,
    ← ht, htq]
  push_cast
  rw [hback, ht]
  have hhalf : (2 : Fp) * ((z - 2 ^ 255 - 1) / 2) = z - 2 ^ 255 - 1 := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ (by decide)
  rw [hhalf]
  ring

end Snarky
