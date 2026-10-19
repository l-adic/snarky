import Snarky.DSL.Field

/-!
# The registration wrapper's expiry signal

`Prover.Reg` (`Snarky/Prover/WP.lean`) exists because `mvcgen` unifies a registered spec's
postcondition with the goal's before discharging its precondition, so an unwrapped law's entry
ghost is captured whenever the two have the same shape. This script registers `mul`'s law
unwrapped, under a name of its own, and runs a composite whose last action has the composite's
postcondition: the proof must fail, and the message guard expects exactly that failure. When a
toolchain makes it pass, the wrapper is dead: delete `Prover.Reg`, `Prover.register`, the
registered definitions, `Prover.Reg.iff` from the grind calls, and this script.
-/

namespace Snarky

open Std.Do

set_option mvcgen.warning false

variable {F c : Type}

/-- `mul` under a name of its own, so that its law can be registered unwrapped without touching
the library's registration. -/
def mulU [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (x y : FVar F) :
    CircuitM F c (FVar F) :=
  mul x y

/-- `mul`'s law at `mulU`, registered unwrapped. -/
theorem Prover.mulU_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀⌝⦄
    mulU (c := Prover c) x y
    ⦃⇓ r st' => ⌜r.Scoped st' ∧ st'.read r = st₀.read x * st₀.read y ∧ st₀ ≤ st'⌝⦄ :=
  Prover.mul_spec x y st₀

attribute [spec] Prover.mulU_spec

/-- Two multiplications, the last with the composite's postcondition. -/
def twoMulLastU [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (x y : FVar F) :
    CircuitM F c (FVar F) := do
  let _ ← mulU x y
  mulU y y

/-- error: the entry ghost was captured: Prover.Reg is still needed -/
#guard_msgs in
theorem Prover.twoMulLastU_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀⌝⦄
    twoMulLastU (c := Prover c) x y
    ⦃⇓ r s' => ⌜r.Scoped s' ∧ s'.read r = st₀.read y * st₀.read y ∧ st₀ ≤ s'⌝⦄ := by
  simp only [twoMulLastU]
  mvcgen
  all_goals first
    | grind [ProverState.read_of_le, CVar.Scoped.of_le]
    | run_tac (Lean.throwError "the entry ghost was captured: Prover.Reg is still needed" :
        Lean.Elab.Tactic.TacticM Unit)

end Snarky
