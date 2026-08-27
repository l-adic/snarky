import Snarky.DSL.Bits

/-!
# The canonical bit decomposition

Port of OCaml `Field.Checked.unpack_full` / `lt_bitstring_value` (snark0.ml, the base-DSL
checked runtime). Plain `unpack` (DSL/Bits.lean) pins the bits' weighted sum to the
operand only modulo the field, so any representative's decomposition satisfies its rows;
locking the decomposition to the canonical representative takes a further comparison
against the modulus, run MSB-outward against a constant bit pattern.

`modBitsMsb` is that pattern.
-/

namespace Snarky

/-- MSB-first bit decomposition of `m` at width `n` (PS `modulusBitsMsb`). -/
def modBitsMsb (m n : ℕ) : List Bool :=
  ((List.range n).map m.testBit).reverse

/-- The pattern has the requested width. -/
theorem modBitsMsb_length (m n : ℕ) : (modBitsMsb m n).length = n := by
  simp [modBitsMsb]

end Snarky
