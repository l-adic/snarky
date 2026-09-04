import Std.Tactic.Do
import Snarky.Builder
import Snarky.BasicSystem

/-!
# The weakest-precondition interpretation of `build`

The soundness reading of a circuit, packaged for `Std.Do`: a circuit is a program whose
only effect is to assume facts about an ambient valuation — each emitted constraint is
an assumption on it. `Builder V c` tags the constraint type with the valuation, so
`wp⟦x⟧ Q` at `nv` is "if every constraint `build x nv` emits holds under `V`, then `Q`
holds of the built result at the advanced counter". The counter is the program's only
state. `WPMonad` is the composition seam: `wp_bind` is `build_bind` plus currying the
split satisfaction hypothesis; through it the framework's triples and `mvcgen` apply to
`CircuitM`.
-/

namespace Snarky

open Std.Do

variable {F c : Type}

/-- A total table of values: the verifier's reading. -/
abbrev Valuation (F : Type) := Variable → F

/-- The backend's semantic reading of one constraint value under a total valuation. -/
class ConstraintHolds (F c : Type) where
  /-- The constraint value is satisfied under the valuation. -/
  Holds : Valuation F → c → Prop

/-- The soundness tag: the constraint type indexed by the valuation. A program enters
the soundness reading by naming the tag — `g (c := Builder V c)` — and every sub-call of
its body elaborates at the same `V`. `Builder V c` is `c` under a name instance search
will not unfold, so the reading has its own `WP` shape while the body keeps the generic
`Monad` instance; the resulting term is definitionally a `CircuitM F c` program. -/
def Builder (_ : Valuation F) (c : Type) := c

instance [inst : ConstraintHolds F c] : ConstraintHolds F (Builder V c) := inst

/-- The soundness reading of `build` at `V`: emitted constraints become assumptions on
the valuation; the state is the allocation counter. -/
instance Builder.instWP {V : Valuation F} [ConstraintHolds F c] :
    WP (CircuitM F (Builder V c)) (.arg Nat .pure) where
  wp x := {
    trans := fun Q nv =>
      .up ((∀ con ∈ (build x nv).constraints, ConstraintHolds.Holds V con) →
        (Q.1 (build x nv).result (build x nv).nextVar).down)
    conjunctiveRaw := by
      intro Q₁ Q₂
      apply SPred.bientails.of_eq
      ext s
      simp [SPred.and, imp_and]
  }

/-- `wp` is a monad morphism: `pure` emits nothing, and a sequence's constraints
concatenate (`build_bind`), the satisfaction hypothesis currying across the split. -/
instance Builder.instWPMonad {V : Valuation F} [ConstraintHolds F c] :
    WPMonad (CircuitM F (Builder V c)) (.arg Nat .pure) where
  wp_pure a := by
    ext Q s
    simp [wp, PredTrans.apply, build]
    rfl
  wp_bind x f := by
    ext Q s
    simp only [PredTrans.apply_Bind_bind]
    simp [wp, PredTrans.apply, build_bind]
    constructor
    · intro h hA hB
      exact h fun con hc => hc.elim (hA con) (hB con)
    · intro h hAB
      exact h (fun con hc => hAB con (Or.inl hc)) fun con hc => hAB con (Or.inr hc)

/-- The soundness triple at the tag is the plain interpreter law: every satisfying
valuation pins the built result. -/
theorem builder_spec_iff {V : Valuation F} [ConstraintHolds F c] {α : Type}
    (g : CircuitM F (Builder V c) α) (post : α → Prop) :
    (⦃⌜True⌝⦄ g ⦃⇓ r _ => ⌜post r⌝⦄) ↔
      ∀ nv : Nat, (∀ con ∈ (build g nv).constraints, ConstraintHolds.Holds V con) →
        post (build g nv).result := by
  constructor
  · intro h nv hsat
    exact h nv trivial hsat
  · intro h nv _ hsat
    exact h nv hsat

/-- A specification whose hypotheses concern values fixed before the run may carry them
into the postcondition: `wp` is deterministic, so a family of triples indexed by such
hypotheses is one triple with the family's conclusion universally quantified. -/
theorem builder_spec_forall {V : Valuation F} [ConstraintHolds F c] {α ι : Type}
    (g : CircuitM F (Builder V c) α) (P : ι → Prop) (post : ι → α → Prop)
    (h : ∀ x, P x → ⦃⌜True⌝⦄ g ⦃⇓ r _ => ⌜post x r⌝⦄) :
    ⦃⌜True⌝⦄ g ⦃⇓ r _ => ⌜∀ x, P x → post x r⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat x hx
  exact (builder_spec_iff g (post x)).mp (h x hx) nv hsat

/-- Weakening a specification's conclusion. -/
theorem builder_spec_imp {V : Valuation F} [ConstraintHolds F c] {α : Type}
    (g : CircuitM F (Builder V c) α) (P Q : α → Prop) (h : ⦃⌜True⌝⦄ g ⦃⇓ r _ => ⌜P r⌝⦄)
    (hpq : ∀ r, P r → Q r) : ⦃⌜True⌝⦄ g ⦃⇓ r _ => ⌜Q r⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat
  exact hpq _ ((builder_spec_iff g P).mp h nv hsat)

/-! ## The lawful-backend interface -/

/-- A backend whose reading of the `BasicSystem` primitives means what `Basic` means:
each row holds exactly when its identity does — soundness reads rows off, completeness
puts them in. -/
class LawfulBasicSystem (F c : Type) [Add F] [Mul F] [Zero F] [One F]
    [BasicSystem F c] [ConstraintHolds F c] : Prop where
  /-- `equal` holds exactly when the sides read equal. -/
  holds_equal : ∀ (V : Valuation F) (a b : CVar F),
    ConstraintHolds.Holds V (BasicSystem.equal (c := c) a b) ↔ a.val V = b.val V
  /-- `r1cs` holds exactly when the product identity reads. -/
  holds_r1cs : ∀ (V : Valuation F) (l r o : CVar F),
    ConstraintHolds.Holds V (BasicSystem.r1cs (c := c) l r o) ↔
      l.val V * r.val V = o.val V
  /-- `square` holds exactly when the square identity reads. -/
  holds_square : ∀ (V : Valuation F) (a sq : CVar F),
    ConstraintHolds.Holds V (BasicSystem.square (c := c) a sq) ↔
      a.val V * a.val V = sq.val V
  /-- `boolean` holds exactly when the reading is `0` or `1`. -/
  holds_boolean : ∀ (V : Valuation F) (x : CVar F),
    ConstraintHolds.Holds V (BasicSystem.boolean (c := c) x) ↔
      x.val V = 0 ∨ x.val V = 1

instance [inst : BasicSystem F c] : BasicSystem F (Builder V c) := inst

instance [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] [ConstraintHolds F c]
    [inst : LawfulBasicSystem F c] : LawfulBasicSystem F (Builder V c) := inst

/-! ## Primitive specs -/

/-- Emitting a constraint assumes it. -/
@[spec] theorem addConstraint_spec {V : Valuation F} [ConstraintHolds F c]
    (con : Builder V c) :
    ⦃⌜True⌝⦄
    addConstraint (F := F) (c := Builder V c) con
    ⦃⇓ _ _ => ⌜ConstraintHolds.Holds V con⌝⦄ := by
  intro nv _ hsat
  exact hsat con (List.mem_cons_self ..)

end Snarky
