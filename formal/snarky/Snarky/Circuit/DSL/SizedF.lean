import Snarky.Circuit.DSL.Bits
import Snarky.Backend.Assignments

/-!
# Sized field elements

Port of `Snarky.Circuit.DSL.SizedF`
(packages/snarky/src/Snarky/Circuit/DSL/SizedF.purs): a value tagged with a
type-level bit width. The tag is a contract, not an invariant: the wrapped value is
promised to fit in `n` bits, and the laws consuming a `SizedF` take that promise as
their `SizedF.Fits` hypothesis.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- The newtype and its contract (`SizedF.Fits`) are ported. PS's bit combinators
  (`fromBits`, `toBits`, `coerceViaBits`, `fromField`) and the `CheckedType` instance
  (the high-bits-zero range check emitted when a `SizedF` is witnessed) arrive with
  their consumers — no ported circuit consumes them yet. Once the check instance
  lands, its soundness law concludes `Fits` from the emitted constraints, and
  composition discharges the gadget laws' `Fits` hypotheses instead of assuming them.
-/

namespace Snarky

/-- A value tagged with a type-level bit width (PS `SizedF n f`): the wrapped value
is promised to fit in `n` bits. Phantom: `n` never influences the data. -/
structure SizedF (n : ℕ) (α : Type u) where
  /-- The wrapped value. -/
  val : α

/-- The `SizedF` contract at an environment: the wrapped variable reads to a value
that fits the tagged width (the reader's faithfulness is `LawfulToNat`'s). Gadget
completeness laws take this as their scalar hypothesis; the future
`CheckedType` port's soundness law concludes it (see the module docstring). -/
def SizedF.Fits {F : Type} [Add F] [Mul F] [ToNat F] {n : ℕ}
    (s : SizedF n (FVar F)) (V : Valuation F) : Prop :=
  ToNat.toNat (s.val.val V) < 2 ^ n

end Snarky
