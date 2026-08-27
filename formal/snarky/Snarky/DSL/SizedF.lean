import Mathlib.Data.ZMod.Basic
import Snarky.DSL.Field

/-!
# Sized field elements

A value tagged with a type-level bit width. The tag is a contract, not an invariant: the
wrapped value is promised to fit in `n` bits, and the laws consuming a `SizedF` take that
promise as their `SizedF.Fits` hypothesis. The bit combinators and the check emitted when
a `SizedF` is witnessed arrive with their consumers.
-/

namespace Snarky

universe u

/-- The canonical natural representative of a field element — `ZMod.val` at a prime
field. Its laws arrive with the bit decomposition that needs them. -/
class ToNat (F : Type u) where
  /-- The canonical representative. -/
  toNat : F → Nat

/-- The canonical representative at a `ZMod` modulus is `ZMod.val` — every deployed
field reads through this one instance. -/
instance instToNatZMod (p : Nat) : ToNat (ZMod p) := ⟨ZMod.val⟩

/-- A value tagged with a type-level bit width: the wrapped value is promised to fit in
`n` bits. Phantom — `n` never influences the data. -/
structure SizedF (n : Nat) (α : Type u) where
  /-- The wrapped value. -/
  val : α

/-- The contract at a valuation: the wrapped variable reads to a value that fits the
tagged width. -/
def SizedF.Fits {F : Type} [Add F] [Mul F] [ToNat F] {n : Nat} (s : SizedF n (FVar F))
    (V : Valuation F) : Prop :=
  ToNat.toNat (s.val.val V) < 2 ^ n

end Snarky
