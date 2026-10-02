import Snarky
import PicklesFixture.Layout

/-!
# The make-zero application circuit

The application circuit of `two_phase_chain`'s `make_zero` branch.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi CompElliptic.Fields.Pasta

/-- `app_circuit_two_phase_chain_make_zero`: assert the input equals zero. -/
def makeZeroAppCircuit (x : FVar Fp) : CircuitM Fp C PUnit :=
  assertEqual x (.const 0)

end PicklesFixture
