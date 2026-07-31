import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.Monad

/-!
# The user-facing barrel

Port of `Snarky.Circuit.DSL` (packages/snarky/src/Snarky/Circuit/DSL.purs), the umbrella
module circuit authors import. In PS it is a pure re-export barrel over the `Monad`/
`Field`/`Boolean`/`Assert`/`Bits`/`SizedF`/`Utils` submodules; here it grows toward that
shape as the gadget modules land (walk steps 9–13 of
`formal/docs/snarky-ps-alignment.md`) — Lean has no re-export lists, so the barrel is the
import.

Transitional: `assertEq` lives here until `Circuit/DSL/Assert.lean` (its PS home) lands
at walk step 11, where it switches to the `BasicSystem.equal` constructor and gains the
PS constant-folding behavior.
-/

namespace Snarky

variable {F c : Type u}

/-- Assert that two field variables are equal, via `x * 1 = y` (PS `assertEqual_`;
transitional encoding — see the module docstring). -/
def assertEq [One F] [BasicSystem F c] (x y : FVar F) : CircuitM F c PUnit :=
  addConstraint (BasicSystem.r1cs x (.const 1) y)

end Snarky
