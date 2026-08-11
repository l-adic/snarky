import Mathlib.Algebra.Field.ZMod
import Snarky.DSL
import Snarky.Constraint.Basic

-- `mvcgen` is experimental; this option is its acknowledged-use switch (see the
-- `Backend/WP` module docstring for the adoption rationale).
set_option mvcgen.warning false

/-!
# The framework showcase: a walked circuit

The classic tutorial statement — `y = x³ + x + 5` — composed purely from gadgets, its
laws proved by walking: unfold, `mvcgen` (the registry supplies each callee's spec),
close the arithmetic. No constraint row is mentioned anywhere; the leaf analyses were
paid once, in the gadget laws, and no caller pays them again. The soundness proof is
the shape every gadget-only circuit proof takes; the completeness proof shows the one
honest extra cost of the prover reading — threading `Assignments.Le` as the table
grows. The `decide` examples at the bottom tie the walked laws to the executable
regression net.

The per-gadget D9 regression checks live in `Example/Gadgets.lean`.
-/

namespace Snarky.Example

/-- The showcase field: the integers mod 17 — small enough for `decide`, and a `Field`
(17 is prime), which the gadget laws need. -/
abbrev F17 := ZMod 17

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

open Std.Do

/-- Constrain `y = x³ + x + 5` (the circuit every SNARK tutorial builds): three gadget
calls, generic over the backend. -/
def cubic {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) :
    CircuitM F c PUnit := do
  let x2 ← square x
  let x3 ← mul x2 x
  assertEqual (sum [x3, x, .const 5]) y

/-- **`cubic` soundness**: any satisfying assignment forces `y = x³ + x + 5`. Three
`mvcgen` steps hand over the three gadgets' facts; one `ring` closes. -/
theorem cubic_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x y : FVar F) (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => x.val V ^ 3 + x.val V + 5 = y.val V) Q⦄
    cubic (c := c) x y
    ⦃Q⦄ := by
  simp only [cubic]
  mvcgen
  rename_i s hpre
  intro x2 _ hx2
  mvcgen
  intro x3 _ hx3
  mvcgen
  intro u _ heq
  refine hpre u _ ?_
  simp only [sum, List.foldl, circuitVal] at heq
  rw [← heq, hx3, hx2]
  ring

/-- **`cubic` completeness**: on operands satisfying the equation the honest run cannot
fail. The same walk; the extra lines thread evaluation facts along `Assignments.Le` as
the table grows — the one cost the prover reading genuinely adds. -/
theorem cubic_complete_spec {F : Type} [Field F] [DecidableEq F]
    (x y : FVar F)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (x.eval env).isOk ∧ (y.eval env).isOk ∧
        ∀ xv yv, x.eval env = .ok xv → y.eval env = .ok yv → xv ^ 3 + xv + 5 = yv)
      (fun _ _ _ => True) Q⦄
    cubic (c := ProverC F) x y
    ⦃Q⦄ := by
  simp only [cubic]
  mvcgen
  rename_i st hpre
  obtain ⟨⟨hokx, hoky, heq⟩, hk⟩ := hpre
  obtain ⟨xv, hx⟩ := CVar.evalOk hokx
  obtain ⟨yv, hy⟩ := CVar.evalOk hoky
  refine ⟨hokx, fun x2 st₁ hx2 hle₁ => ?_⟩
  mvcgen
  have hx₁ : x.eval st₁.env = .ok xv := CVar.eval_le hle₁ hx
  have hx2' : x2.eval st₁.env = .ok (xv * xv) := hx2 xv hx
  refine ⟨⟨by rw [hx2']; rfl, by rw [hx₁]; rfl⟩, fun x3 st₂ hx3 hle₂ => ?_⟩
  mvcgen
  have hx₂ : x.eval st₂.env = .ok xv := CVar.eval_le hle₂ hx₁
  have hy₂ : y.eval st₂.env = .ok yv := CVar.eval_le (hle₁.trans hle₂) hy
  have hx3' : x3.eval st₂.env = .ok (xv * xv * xv) := hx3 (xv * xv) xv hx2' hx₁
  have hsum : (sum [x3, x, .const 5]).eval st₂.env
      = .ok ([xv * xv * xv, xv, 5].sum) := by
    refine sum_eval ?_
    simp [hx3', hx₂, CVar.eval]
  refine ⟨⟨by rw [hsum]; rfl, by rw [hy₂]; rfl, fun av bv hav hbv => ?_⟩,
    fun u st₃ hle₃ => hk u st₃ ((hle₁.trans hle₂).trans hle₃)⟩
  rw [hsum] at hav
  rw [hy₂] at hbv
  injection hav with hav
  injection hbv with hbv
  rw [← hav, ← hbv, ← heq xv yv hx hy]
  simp [List.sum]
  ring

/-- The laws, exercised in the kernel: the honest run accepts `x = 3, y = 35`
(`27 + 3 + 5`)… -/
example : (prove Basic.holds
    ((do let x ← witness (val := F17) (pure 3)
         cubic x (.const 35)) : CircuitM F17 (Basic F17) PUnit)
    0 Assignments.empty).isOk = true := by decide

/-- …and rejects `y = 36`. -/
example : (prove Basic.holds
    ((do let x ← witness (val := F17) (pure 3)
         cubic x (.const 36)) : CircuitM F17 (Basic F17) PUnit)
    0 Assignments.empty).isOk = false := by decide

end Snarky.Example
