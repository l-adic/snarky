import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

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
  newtype with its `fromShifted` decode and `toShifted` encode (`Type1.encode`), and
  the `SplitField` pair with its decode. PS's `Type2` newtype (whose decode delegates
  to `SplitField`'s), the `Shifted` class packaging, the forbidden-values checks, and
  the shifted circuit ops are consumed only by the pickles modules and arrive with
  them.
- PS bakes the width `n` into each field's `Shifted` instance (via `FieldSizeInBits`);
  the decodes here are generic, so `n` is an explicit argument.
-/

namespace Snarky

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

/-- The integer a canonically-carried `Type1` representative decodes to:
`fromShifted` of its canonical representative — the scalar the consuming ladder
computes with. -/
def Type1.decodeZ {q : ℕ} (n : ℕ) (t : Type1 (ZMod q)) : ℤ :=
  Type1.fromShifted n ⟨(t.val.val : ℤ)⟩

/-- `decodeZ` read across a field boundary: the scalar-field value a shifted public
input stands for. -/
def Type1.decodeCanonical {q p : ℕ} (n : ℕ) (t : Type1 (ZMod q)) : ZMod p :=
  (Type1.decodeZ n t : ZMod p)

/-- The `Type1` encode (PS `toShifted`): carry `z` as the canonical representative of
`(z − 2^n − 1) / 2`, computed in the scalar field — `(p + 1) / 2` is `2`'s inverse at
odd `p` — and transported across the field boundary (`p ≤ q`). The decode inverts it
(`decodeCanonical_encode`). -/
def Type1.encode {p : ℕ} (q n : ℕ) (z : ZMod p) : Type1 (ZMod q) :=
  ⟨(((z - 2 ^ n - 1) * ((p + 1) / 2 : ℕ) : ZMod p).val : ZMod q)⟩

/-- The round trip: the encode's decode is the encoded scalar. The halving constant's
defining identity `2 · (p+1)/2 = 1` arrives as a hypothesis, dischargeable by `decide`
at any odd concrete modulus. -/
theorem Type1.decodeCanonical_encode {p q : ℕ} [NeZero p] [NeZero q] (n : ℕ)
    (hpq : p ≤ q) (h2 : (2 : ZMod p) * (((p + 1) / 2 : ℕ) : ZMod p) = 1) (z : ZMod p) :
    Type1.decodeCanonical n (Type1.encode q n z) = z := by
  set t : ZMod p := (z - 2 ^ n - 1) * ((p + 1) / 2 : ℕ) with ht
  have htq : ((t.val : ZMod q)).val = t.val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt t) hpq)]
  have hback : ((t.val : ℕ) : ZMod p) = t := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  simp only [Type1.decodeCanonical, Type1.decodeZ, Type1.encode, Type1.fromShifted,
    ← ht, htq]
  push_cast
  rw [hback, ht]
  have hhalf : (2 : ZMod p) * ((z - 2 ^ n - 1) * ((p + 1) / 2 : ℕ)) = z - 2 ^ n - 1 := by
    rw [mul_comm (z - 2 ^ n - 1), ← mul_assoc, h2, one_mul]
  rw [hhalf]
  ring

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

end Snarky
