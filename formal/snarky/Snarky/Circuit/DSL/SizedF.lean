/-!
# Sized field elements

Port of `Snarky.Circuit.DSL.SizedF`
(packages/snarky/src/Snarky/Circuit/DSL/SizedF.purs): a value tagged with a
type-level bit width. The tag is a contract, not an invariant: the wrapped value is
promised to fit in `n` bits, and the laws consuming a `SizedF` state that promise as
an explicit hypothesis (`ToNat.toNat v < 2 ^ n`-shaped, at the consumer).

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- Only the newtype is ported. PS's bit combinators (`fromBits`, `toBits`,
  `coerceViaBits`, `fromField`) and the `CheckedType` instance (the high-bits-zero
  range check emitted when a `SizedF` is witnessed) arrive with their consumers — no
  ported circuit consumes them yet.
-/

namespace Snarky

/-- A value tagged with a type-level bit width (PS `SizedF n f`): the wrapped value
is promised to fit in `n` bits. Phantom: `n` never influences the data. -/
structure SizedF (n : ℕ) (α : Type u) where
  /-- The wrapped value. -/
  val : α

end Snarky
