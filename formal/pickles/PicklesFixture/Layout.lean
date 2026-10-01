import Snarky.DSL.SizedF
import Snarky.Kimchi.Constraint
import Kimchi.Columns
import Kimchi.Verifier.Kimchi
import Pasta.Endo
import Pickles.Statement

/-!
# The drivers' constraint types

What more than one driver shares: the kimchi constraint type at each Pasta field, and the
fields' `ToNat` instances `unpack`'s bit reads go through.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi CompElliptic.Fields.Pasta

/-- `unpack`'s bit reads go through the canonical representative. -/
instance toNatFp : ToNat Fp := ⟨ZMod.val⟩

/-- The same at the wrap field. -/
instance toNatFq : ToNat Fq := ⟨ZMod.val⟩

/-- The kimchi constraint sum at the step field. -/
abbrev C := KimchiConstraint Fp

/-- The kimchi constraint sum at the wrap field. -/
abbrev Cq := KimchiConstraint Fq

end PicklesFixture
