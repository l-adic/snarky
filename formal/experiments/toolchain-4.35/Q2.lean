import Snarky.DSL.Field
import Std.WP
import Std.Tactic.Do

/-!
# The prover's reading in `Std.WP` (experiment sidecar)

The `Std.WP` interpretation of `CircuitM F (Prover c)`, defined from the library's `proverWP`:
the same transformer at Prop-valued state predicates. `vcgen` recognizes only `Std.WP.wp`, so
this is what lets it run on circuits.
-/

namespace Snarky

open Lean.Order Std.WP

variable {F c : Type}

/-- The transformer is monotone in both conditions. -/
theorem proverWP_mono₂ [Zero F] [ConstraintHolds F c] {α : Type} {x : CircuitM F c α}
    {Q₁ Q₂ : α → ProverState F → ULift Prop} {E₁ E₂ : EvalError → ProverState F → ULift Prop}
    (hQ : ∀ a s, (Q₁ a s).down → (Q₂ a s).down) (hE : ∀ e s, (E₁ e s).down → (E₂ e s).down)
    {st : ProverState F} (hx : (proverWP x Q₁ E₁ st).down) : (proverWP x Q₂ E₂ st).down := by
  induction x generalizing st with
  | pure a => exact hQ a st hx
  | addConstraintOp con k ih =>
    simp only [proverWP] at hx ⊢
    exact ⟨hx.1, hx.2.1, ih hx.2.2⟩
  | existsOp n wit k ih =>
    simp only [proverWP] at hx ⊢
    rcases hr : wit.run st.env with e | xs <;> rw [hr] at hx
    · exact hE e st hx
    · exact ih _ hx

/-- The prover's reading as a `Std.WP` interpretation. -/
instance Prover.instStdWP [Zero F] [ConstraintHolds F c] {α : Type} :
    Std.WP.WP (CircuitM F (Prover c) α) α (ProverState F → Prop)
      (EvalError → ProverState F → Prop) where
  wpTrans x := ⟨fun post epost st =>
    (proverWP.{0} (c := Prover c) x (fun a s => ULift.up.{0} (post a s))
      (fun e s => ULift.up.{0} (epost e s)) st).down⟩
  wp_trans_monotone _ := fun _ _ _ _ hE hQ _ h =>
    proverWP_mono₂ (fun a s => hQ a s) (fun e s => hE e s) h

/-- The reading is a monad morphism. -/
instance Prover.instStdWPMonad [Zero F] [ConstraintHolds F c] :
    Std.WP.WPMonad (CircuitM F (Prover c)) (ProverState F → Prop)
      (EvalError → ProverState F → Prop) where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := fun _ h => h
  bind_le_wp_bind x f post epost := fun st h => by
    show (proverWP.{0} (c := Prover c) (x >>= f) _ _ st).down
    rw [proverWP_bind]
    exact h

/-- The bridge: a law at the prover's reading, as the transformer it unfolds to, is a `Std.WP`
triple. -/
theorem Prover.std_of_wp [Zero F] [ConstraintHolds F c] {α : Type} {x : CircuitM F (Prover c) α}
    {P : ProverState F → Prop} {Q : α → ProverState F → Prop}
    (h : ∀ st, P st → (proverWP.{0} (c := Prover c) x (fun r s => ULift.up.{0} (Q r s))
      (fun _ _ => ULift.up.{0} False) st).down) :
    ⦃P⦄ x ⦃Q⦄ :=
  ⟨fun st hp => proverWP_mono₂ (fun _ _ h => h) (fun _ _ (h : False) => h.elim) (h st hp)⟩

/-! ## Question 2: the negative control under `vcgen`, `mul`'s law registered bare -/

set_option experimental.vcgen true

/-- `mul` under a name of its own, as in the in-tree control. -/
def mulU [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (x y : FVar F) :
    CircuitM F c (FVar F) :=
  mul x y

/-- `mul`'s law at `mulU`, in the library's shape (entry ghost `st₀`, `st₀ ≤ s'`), registered
bare: no `Prover.Reg`. -/
@[spec] theorem Prover.mulU_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F) :
    ⦃fun st => st = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀⦄
    mulU (c := Prover c) x y
    ⦃fun r st' => r.Scoped st' ∧ st'.read r = st₀.read x * st₀.read y ∧ st₀ ≤ st'⦄ :=
  Prover.std_of_wp fun st h => Prover.mul_spec x y st₀ st h

/-- Two multiplications, the last with the composite's postcondition. -/
def twoMulLastU [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (x y : FVar F) :
    CircuitM F c (FVar F) := do
  let _ ← mulU x y
  mulU y y

set_option trace.Elab.Tactic.Do.vcgen true in
theorem Prover.twoMulLastU_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F) :
    ⦃fun s => s = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀⦄
    twoMulLastU (c := Prover c) x y
    ⦃fun r s' => r.Scoped s' ∧ s'.read r = st₀.read y * st₀.read y ∧ st₀ ≤ s'⦄ := by
  unfold twoMulLastU
  vcgen
  all_goals first
    | grind [ProverState.read_of_le, CVar.Scoped.of_le]
    | run_tac (Lean.throwError "the entry ghost was captured" : Lean.Elab.Tactic.TacticM Unit)

end Snarky

#print axioms Snarky.Prover.twoMulLastU_spec
#print axioms Snarky.Prover.mulU_spec
