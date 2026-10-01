import Snarky
import Pickles.StepMain
import PicklesFixture.Layout

/-!
# The transcribed application rules

The rules of the step main circuits the dumps compile, and the application circuit one of
them is built from, as `Pickles.stepMain` takes a rule: the slots' previous statements and the
application state.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi CompElliptic.Fields.Pasta

/-- `app_circuit_two_phase_chain_make_zero`: assert the input equals zero. -/
def makeZeroAppCircuit (x : FVar Fp) : CircuitM Fp C PUnit :=
  assertEqual x (.const 0)

/-- The rule of `simple_chain_n2`: two previous states, `self` their sum plus one unless `self`
is zero, the base case in which neither previous proof must verify. -/
def simpleChainN2Rule (appState : FVar Fp) :
    CircuitM Fp C ((Fin 2 → Pickles.PrevStatement 1) × Unit) := do
  let prev1 ← witness (val := Fp) (AsProver.throw "advice")
  let prev2 ← witness (val := Fp) (AsProver.throw "advice")
  let isBaseCase ← equals (.const 0) appState
  let mustVerify := Snarky.not isBaseCase
  let selfCorrect ← equals (CVar.add_ (CVar.add_ (.const 1) prev1) prev2) appState
  assertAny [selfCorrect, isBaseCase]
  pure (#v[⟨#v[prev1], mustVerify⟩, ⟨#v[prev2], mustVerify⟩].get, ())

/-- The rule of `two_phase_chain`'s `make_zero` branch: `self = 0`, with no slot. -/
def makeZeroRule (x : FVar Fp) :
    CircuitM Fp C ((Fin 0 → Pickles.PrevStatement 1) × Unit) := do
  makeZeroAppCircuit x
  pure (Fin.elim0, ())

/-- The rule of `two_phase_chain`'s `increment` branch: `self = prev + 1`, its one slot this
system's previous proof, which must verify. -/
def incrementRule (x : FVar Fp) :
    CircuitM Fp C ((Fin 1 → Pickles.PrevStatement 1) × Unit) := do
  let prev ← witness (val := Fp) (AsProver.throw "advice")
  assertEqual x (CVar.add_ (.const 1) prev)
  pure (#v[⟨#v[prev], true_⟩].get, ())

/-- The rule of `tree_proof_return`: slot 0 a No_recursion_return proof, which always verifies,
slot 1 this system's previous proof, which verifies unless it is the base case; `self` is `0`
in the base case, `1 + prev` otherwise. -/
def treeProofReturnRule :
    CircuitM Fp C ((Fin 2 → Pickles.PrevStatement 1) × FVar Fp) := do
  let noRecursiveInput ← witness (val := Fp) (AsProver.throw "advice")
  let prev ← witness (val := Fp) (AsProver.throw "advice")
  let isBaseCase ← witness (val := Bool) (AsProver.throw "advice")
  let mustVerify := Snarky.not isBaseCase
  let self ← selectField isBaseCase (.const 0) (CVar.add_ (.const 1) prev)
  pure (#v[⟨#v[noRecursiveInput], true_⟩, ⟨#v[prev], mustVerify⟩].get, self)

/-- The rule of `import_two_phase_chain`: slot 0 a `two_phase_chain` proof, which always
verifies, slot 1 this system's previous proof, which verifies unless it is the base case;
`self` is slot 0's value `tx` in the base case, `prev + tx` otherwise. -/
def importTwoPhaseChainRule :
    CircuitM Fp C ((Fin 2 → Pickles.PrevStatement 1) × FVar Fp) := do
  let tx ← witness (val := Fp) (AsProver.throw "advice")
  let prev ← witness (val := Fp) (AsProver.throw "advice")
  let isBaseCase ← witness (val := Bool) (AsProver.throw "advice")
  let mustVerify := Snarky.not isBaseCase
  let self ← selectField isBaseCase tx (CVar.add_ prev tx)
  pure (#v[⟨#v[tx], true_⟩, ⟨#v[prev], mustVerify⟩].get, self)

end PicklesFixture
