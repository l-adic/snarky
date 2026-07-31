import Snarky.Circuit.DSL.Assert
import Snarky.Circuit.DSL.Boolean
import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.Monad

/-!
# The user-facing barrel

Port of `Snarky.Circuit.DSL` (packages/snarky/src/Snarky/Circuit/DSL.purs), the umbrella
module circuit authors import. In PS it is a pure re-export barrel over the `Monad`/
`Field`/`Boolean`/`Assert`/`Bits`/`SizedF`/`Utils` submodules; here it grows toward that
shape as the gadget modules land (walk steps 9–13 of
`formal/docs/snarky-ps-alignment.md`) — Lean has no re-export lists, so the barrel is the
import. The transitional `assertEq` this file once carried retired at step 11: `assertEq`
is now the `AssertEqual` class method (`Circuit/DSL/Assert`), whose `FVar` instance is
`assertEqual` — the `equal`-constructor encoding with the PS constant folding.
-/
