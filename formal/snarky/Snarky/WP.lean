import Std.Tactic.Do
import Mathlib.Data.List.Forall2
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

/-- Every program satisfies the trivial specification: the reading of a sub-circuit whose
outputs a statement does not mention. -/
theorem builder_spec_true {V : Valuation F} [ConstraintHolds F c] {α : Type}
    (g : CircuitM F (Builder V c) α) : ⦃⌜True⌝⦄ g ⦃⇓ _ _ => ⌜True⌝⦄ := by
  rw [builder_spec_iff]
  intro _ _
  trivial

/-- What a program's prefix establishes may be assumed of the whole. A sequence's rows are
its prefix's followed by the rest's (`build_bind`), so a valuation satisfying the whole
satisfies the prefix, and the prefix's conclusion holds of it: a gadget that opens by
constraining its inputs proves the rest of its specification under those constraints' reading,
and a consumer need not supply it. -/
theorem builder_spec_bind_assume {V : Valuation F} [ConstraintHolds F c] {α β : Type}
    (x : CircuitM F (Builder V c) α) (f : α → CircuitM F (Builder V c) β) (Q : Prop)
    (post : β → Prop) (hx : ⦃⌜True⌝⦄ x ⦃⇓ _ _ => ⌜Q⌝⦄)
    (h : Q → ⦃⌜True⌝⦄ (x >>= f) ⦃⇓ r _ => ⌜post r⌝⦄) :
    ⦃⌜True⌝⦄ (x >>= f) ⦃⇓ r _ => ⌜post r⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat
  have hQ : Q := (builder_spec_iff x fun _ => Q).mp hx nv fun con hc =>
    hsat con (by rw [build_bind]; exact List.mem_append_left _ hc)
  exact (builder_spec_iff _ post).mp (h hQ) nv hsat

/-- A prefix that establishes a fact, then a tail whose specification may use it: the
composition's specification is the tail's. What an assertion run before a gadget buys — the
gadget's read, with the assertion's conclusion as a premise in hand. -/
theorem builder_spec_bind_of {V : Valuation F} [ConstraintHolds F c] {α β : Type}
    (x : CircuitM F (Builder V c) α) (f : α → CircuitM F (Builder V c) β) (Q : Prop)
    (post : β → Prop) (hx : ⦃⌜True⌝⦄ x ⦃⇓ _ _ => ⌜Q⌝⦄)
    (hf : Q → ∀ a, ⦃⌜True⌝⦄ f a ⦃⇓ r _ => ⌜post r⌝⦄) :
    ⦃⌜True⌝⦄ (x >>= f) ⦃⇓ r _ => ⌜post r⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat
  have hQ : Q := (builder_spec_iff x fun _ => Q).mp hx nv fun con hc =>
    hsat con (by rw [build_bind]; exact List.mem_append_left _ hc)
  have := (builder_spec_iff _ post).mp (hf hQ (build x nv).result) (build x nv).nextVar
    fun con hc => hsat con (by rw [build_bind]; exact List.mem_append_right _ hc)
  rw [build_bind]
  exact this

/-- Two specifications of one program conjoin: `wp` is deterministic, so both conclusions hold
of the one result. -/
theorem builder_spec_and {V : Valuation F} [ConstraintHolds F c] {α : Type}
    (g : CircuitM F (Builder V c) α) (P Q : α → Prop) (hp : ⦃⌜True⌝⦄ g ⦃⇓ r _ => ⌜P r⌝⦄)
    (hq : ⦃⌜True⌝⦄ g ⦃⇓ r _ => ⌜Q r⌝⦄) : ⦃⌜True⌝⦄ g ⦃⇓ r _ => ⌜P r ∧ Q r⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat
  exact ⟨(builder_spec_iff g P).mp hp nv hsat, (builder_spec_iff g Q).mp hq nv hsat⟩

/-- Weakening a specification's conclusion. -/
theorem builder_spec_imp {V : Valuation F} [ConstraintHolds F c] {α : Type}
    (g : CircuitM F (Builder V c) α) (P Q : α → Prop) (h : ⦃⌜True⌝⦄ g ⦃⇓ r _ => ⌜P r⌝⦄)
    (hpq : ∀ r, P r → Q r) : ⦃⌜True⌝⦄ g ⦃⇓ r _ => ⌜Q r⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat
  exact hpq _ ((builder_spec_iff g P).mp h nv hsat)

/-- A `mapM` of specifications: each element's result reads against its own target, so the
list of results reads against the list of targets. The `List.mapM` combinator `mvcgen` lacks
(it has `forIn`). -/
theorem builder_spec_mapM {V : Valuation F} [ConstraintHolds F c] {α β γ : Type}
    (f : α → CircuitM F (Builder V c) β) (R : β → γ → Prop) (Q : α → γ)
    (hf : ∀ a, ⦃⌜True⌝⦄ f a ⦃⇓ r _ => ⌜R r (Q a)⌝⦄) :
    ∀ l : List α, ⦃⌜True⌝⦄ l.mapM f ⦃⇓ rs _ => ⌜List.Forall₂ R rs (l.map Q)⌝⦄
  | [] => by
    rw [List.mapM_nil, List.map_nil]
    mvcgen
    exact .nil
  | a :: l => by
    rw [List.mapM_cons, List.map_cons]
    have ih := builder_spec_mapM f R Q hf l
    mvcgen [hf, ih]
    rename_i r _ hr rs _ hrs
    exact .cons hr hrs

/-- A specification of `f <$> m` is one of `m` read through `f`. -/
theorem builder_spec_of_map {V : Valuation F} [ConstraintHolds F c] {α β : Type}
    (m : CircuitM F (Builder V c) α) (f : α → β) (post : β → Prop)
    (h : ⦃⌜True⌝⦄ (f <$> m) ⦃⇓ r _ => ⌜post r⌝⦄) : ⦃⌜True⌝⦄ m ⦃⇓ r _ => ⌜post (f r)⌝⦄ := by
  rw [builder_spec_iff] at h ⊢
  intro nv hsat
  have hb := h nv (by
    rw [CircuitM.map_eq, build_bind]
    simpa [build] using hsat)
  rw [CircuitM.map_eq, build_bind] at hb
  simpa [build] using hb

/-- A vector `mapM` of specifications: each entry's result satisfies its own entry's
specification. -/
theorem builder_spec_vector_mapM_get {V : Valuation F} [ConstraintHolds F c] {α β : Type}
    {m : ℕ} (f : α → CircuitM F (Builder V c) β) (Q : α → β → Prop)
    (hf : ∀ a, ⦃⌜True⌝⦄ f a ⦃⇓ r _ => ⌜Q a r⌝⦄) (v : Vector α m) :
    ⦃⌜True⌝⦄ v.mapM f ⦃⇓ rs _ => ⌜∀ i : Fin m, Q v[i] rs[i]⌝⦄ := by
  have hl := builder_spec_mapM f (fun r a => Q a r) id hf v.toList
  have heq : (fun rs : Vector β m => rs.toList) <$> v.mapM f = v.toList.mapM f := by
    rw [← Vector.toList_toArray, ← Array.toList_mapM, ← Vector.toArray_mapM, ← comp_map]
    rfl
  rw [← heq] at hl
  refine builder_spec_imp _ _ _ (builder_spec_of_map _ _ _ hl) fun rs h i => ?_
  have hg := (List.forall₂_iff_get.mp h).2 i (by simp) (by simp)
  simpa using hg

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
