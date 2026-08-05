import Std.Do
import Snarky.Backend.Builder
import Snarky.Backend.Prover

/-!
# The weakest-precondition interpretation of `build`

The soundness reading of a circuit, packaged for Lean core's `Std.Do` program-logic
framework: a circuit is a program whose only effect is to ASSUME facts about an ambient
adversarial witness — each emitted constraint is an assumption on the valuation — so
`wp⟦x⟧ Q` at `(V, nv)` is "if every constraint `build x nv` emits holds under `V`, then
`Q` holds of the built result at the advanced counter". The counter is the program's
state; the valuation is read-only state, passed through unchanged.

The interpretation is generic over the backend through `ConstraintHolds`, the semantic
reading of one constraint VALUE under a total valuation — the reference `Basic` backend
reads through its checker at the everywhere-defined table (`Valuation.toAssignments`,
under which evaluation never fails); richer backends supply their own reading.

`WPMonad` — `wp` is a monad morphism — is the composition seam: `wp_bind` is
`build_bind` (constraints of a sequence concatenate) plus currying the split
satisfaction hypothesis. Everything downstream follows from these two laws: the
framework's Hoare triples `⦃P⦄ x ⦃Q⦄`, their sequencing rules, and the `mvcgen`
verification-condition generator all apply to `CircuitM` through these instances, so a
gadget's soundness law is stated as a triple and proved by walking the gadget's own
do-block, with only the leaf semantic obligations left to hand proofs.

`Std.Do` is experimental (its tactic warns on use; the assertion encoding is documented
as in flux upstream): the bet is confined by the pinned toolchain, and the kernel checks
whatever the framework produces — the axiom gates audit these laws like any other.

The PROVER interpretation of the same monad — `prove`-semantics, where the assignment
table is genuinely mutable state and `EvalError` the exception layer — needs a distinct
carrier type when it lands (one monad admits one `WP` shape); the bare `CircuitM` is
deliberately reserved for the soundness reading stated here.
-/

namespace Snarky

open Std.Do

variable {F c : Type}

/-- The backend's semantic reading of one constraint value under a total valuation —
the parameter the soundness interpretation is generic over. Instances live with their
backends (`Basic` below; the kimchi bridge supplies its own). -/
class ConstraintHolds (F c : Type) where
  /-- The constraint value is satisfied under the valuation. -/
  Holds : Valuation F → c → Prop

/-- The soundness reading of `build`: emitted constraints become assumptions on the
valuation. -/
instance CircuitM.instWP [ConstraintHolds F c] :
    WP (CircuitM F c) (.arg (Valuation F) (.arg Nat .pure)) where
  wp x := {
    trans := fun Q V nv =>
      .up ((∀ con ∈ (build x nv).constraints, ConstraintHolds.Holds V con) →
        (Q.1 (build x nv).result V (build x nv).nextVar).down)
    conjunctiveRaw := by
      intro Q₁ Q₂
      apply SPred.bientails.of_eq
      ext V nv
      simp [SPred.and, imp_and]
  }

/-- `wp` is a monad morphism: `pure` emits nothing, and a sequence's constraints
concatenate (`build_bind`), the satisfaction hypothesis currying across the split. -/
instance CircuitM.instWPMonad [ConstraintHolds F c] :
    WPMonad (CircuitM F c) (.arg (Valuation F) (.arg Nat .pure)) where
  wp_pure a := by
    ext Q V nv
    simp [wp, PredTrans.apply, build]
    rfl
  wp_bind x f := by
    ext Q V nv
    simp only [PredTrans.apply_Bind_bind]
    simp [wp, PredTrans.apply, build_bind]
    constructor
    · intro h hA hB
      exact h fun con hc => hc.elim (hA con) (hB con)
    · intro h hAB
      exact h (fun con hc => hAB con (Or.inl hc)) fun con hc => hAB con (Or.inr hc)

/-! ## The reference reading

`Basic` reads a constraint through its checker at the everywhere-defined table (the
instance lives here, not in `Constraint/Basic.lean`, because the import direction runs
`Basic → Monad → Builder → WP`). -/

/-- `Basic`'s semantic reading: the checker at the total table. -/
instance Basic.instConstraintHolds [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    ConstraintHolds F (Basic F) where
  Holds V con := con.holds V.toAssignments = true

/-! ## The lawful-backend interface -/

/-- A backend whose reading of the `BasicSystem` primitives means what `Basic` means:
one extraction law per primitive. This is the COMPLETE interface between the
backend-generic gadget laws and any backend — a gadget can only emit what
`BasicSystem` offers — so every gadget triple proved over it transfers to a new
backend by exhibiting one instance. `Basic` is the reference inhabitant below. -/
class LawfulBasicSystem (F c : Type) [Add F] [Mul F] [Zero F] [One F]
    [BasicSystem F c] [ConstraintHolds F c] : Prop where
  /-- A satisfied `equal` reads its sides equal. -/
  holds_equal : ∀ (V : Valuation F) (a b : CVar F),
    ConstraintHolds.Holds V (BasicSystem.equal (c := c) a b) → a.val V = b.val V
  /-- A satisfied `r1cs` reads as the product identity. -/
  holds_r1cs : ∀ (V : Valuation F) (l r o : CVar F),
    ConstraintHolds.Holds V (BasicSystem.r1cs (c := c) l r o) →
      l.val V * r.val V = o.val V
  /-- A satisfied `square` reads as the square identity. -/
  holds_square : ∀ (V : Valuation F) (a sq : CVar F),
    ConstraintHolds.Holds V (BasicSystem.square (c := c) a sq) →
      a.val V * a.val V = sq.val V
  /-- A satisfied `boolean` reads as `0` or `1`. -/
  holds_boolean : ∀ (V : Valuation F) (x : CVar F),
    ConstraintHolds.Holds V (BasicSystem.boolean (c := c) x) →
      x.val V = 0 ∨ x.val V = 1

/-- `Basic` is lawful: each law is its inversion lemma read through the bridge. -/
instance Basic.instLawfulBasicSystem [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    LawfulBasicSystem F (Basic F) where
  holds_equal V a b h := by
    obtain ⟨x, y, hx, hy, hxy⟩ := Basic.equal_inv h
    rw [CVar.eval_toAssignments] at hx hy
    injection hx with hx
    injection hy with hy
    rw [hx, hy, hxy]
  holds_r1cs V l r o h := by
    obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := Basic.r1cs_inv h
    rw [CVar.eval_toAssignments] at hx hy hz
    injection hx with hx
    injection hy with hy
    injection hz with hz
    rw [hx, hy, hz, hxyz]
  holds_square V a sq h := by
    obtain ⟨x, z, hx, hz, hxz⟩ := Basic.square_inv h
    rw [CVar.eval_toAssignments] at hx hz
    injection hx with hx
    injection hz with hz
    rw [hx, hz, hxz]
  holds_boolean V x h := by
    obtain ⟨v, hv, hb⟩ := Basic.boolean_inv h
    rw [CVar.eval_toAssignments] at hv
    injection hv with hv
    rw [hv]
    exact hb

/-! ## Spec shapes

The framework's recommended spec form is schematic — the postcondition is a
parameter, so `mvcgen` instantiates it exactly at each call site — but written raw it
buries a gadget's contract in encoding. The DSL's gadgets have a small number of
shapes, named here once, so each spec reads as its contract alone. -/

/-- The spec shape of an ASSERTION gadget — returns nothing and grants the caller a
fact: `⦃Asserts fact Q⦄ g ⦃Q⦄` reads "`g` asserts `fact`". Counter-agnostic, so it
covers assertions that allocate auxiliary witnesses (`assertNonZero`'s inverse) as
well as pure rows. -/
abbrev Asserts (fact : Valuation F → Prop)
    (Q : PostCond PUnit (.arg (Valuation F) (.arg Nat .pure))) :
    Assertion (.arg (Valuation F) (.arg Nat .pure)) :=
  fun V _nv => .up (fact V → ∀ nv', (Q.1 PUnit.unit V nv').down)

/-- The spec shape of a COMPUTE gadget — returns a variable whose reading the emitted
constraints characterize: `⦃Computes fact Q⦄ g ⦃Q⦄` reads "`g` computes a result
satisfying `fact`". The result variable and final counter are opaque to the caller;
the fact about the result's reading is the whole interface. -/
abbrev Computes [Add F] [Mul F] (fact : Valuation F → F → Prop)
    (Q : PostCond (FVar F) (.arg (Valuation F) (.arg Nat .pure))) :
    Assertion (.arg (Valuation F) (.arg Nat .pure)) :=
  fun V _nv => .up (∀ (r : FVar F) (nv' : Nat), fact V (r.val V) → (Q.1 r V nv').down)

/-! ## The prover reading and its carrier

One monad admits one `WP` shape, and the bare `CircuitM` carries the soundness
reading — so the `prove`-interpretation takes a synonym carrier (the `ZipList`
pattern: same programs, a type-level tag selecting the second structure). The
completeness laws are stated against the reference backend, whose prover checks
each constraint as it is added. -/

/-- `CircuitM` at the reference backend, tagged for the `prove`-interpretation.
Programs enter by type ascription — `(assertEqual x y : ProverM F PUnit)` — which
keeps their head symbols visible to `mvcgen`'s spec lookup (a wrapper function
would hide them). -/
def ProverM (F : Type) (α : Type) := CircuitM F (Basic F) α

instance : Monad (ProverM F) := inferInstanceAs (Monad (CircuitM F (Basic F)))
instance : LawfulMonad (ProverM F) := inferInstanceAs (LawfulMonad (CircuitM F (Basic F)))

/-- The prover reading: the assignment table is mutable state, `EvalError` the
exception layer — a total-correctness postcondition (`⇓`) asserts the run cannot
fail. -/
instance ProverM.instWP [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    WP (ProverM F) (.arg Nat (.arg (Assignments F) (.except EvalError .pure))) where
  wp x := {
    trans := fun Q nv env =>
      match prove Basic.holds x nv env with
      | .ok out => Q.1 out.result out.nextVar out.assignments
      | .error e => Q.2.1 e
    conjunctiveRaw := by
      intro Q₁ Q₂
      apply SPred.bientails.of_eq
      ext nv env
      rcases h : prove Basic.holds x nv env with e | out <;>
        simp [SPred.and, ExceptConds.and, h]
  }

/-- The prover `wp` is a monad morphism: `prove_bind` is the composition law. -/
instance ProverM.instWPMonad [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    WPMonad (ProverM F) (.arg Nat (.arg (Assignments F) (.except EvalError .pure))) where
  wp_pure a := by
    ext Q nv env
    simp [wp, PredTrans.apply]
    rfl
  wp_bind x f := by
    ext Q nv env
    simp only [PredTrans.apply_Bind_bind]
    simp only [wp, PredTrans.apply]
    rw [show (do let a ← x; f a : ProverM F _)
        = (x >>= f : CircuitM F (Basic F) _) from rfl, prove_bind]
    rcases h : prove Basic.holds x nv env with e | out
    · simp [Except.bind]
    · simp [Except.bind]

/-- The prover-reading spec shape of an assertion gadget: given `facts` about the
incoming table (and counter-freshness, the invariant every prover run threads), the
run cannot fail, and the caller continues at a table that EXTENDS the incoming one
with freshness re-established — old facts transport along `Assignments.Le` via
`CVar.eval_le`. Reads "`g` succeeds given `facts`". -/
abbrev ProverAsserts (facts : Assignments F → Prop)
    (Q : PostCond PUnit (.arg Nat (.arg (Assignments F) (.except EvalError .pure)))) :
    Assertion (.arg Nat (.arg (Assignments F) (.except EvalError .pure))) :=
  fun nv env => .up (env.FreshFrom nv ∧ facts env ∧
    ∀ (nv' : Nat) (env' : Assignments F),
      env'.FreshFrom nv' → env.Le env' → (Q.1 PUnit.unit nv' env').down)

/-- The prover-reading spec shape of a compute gadget: given `facts`, the run succeeds
and the result reads as `value` in the final (extended, fresh) table. Reads "`g`
computes `value` given `facts`". -/
abbrev ProverComputes [Add F] [Mul F] (facts : Assignments F → Prop)
    (value : Assignments F → F)
    (Q : PostCond (FVar F) (.arg Nat (.arg (Assignments F) (.except EvalError .pure)))) :
    Assertion (.arg Nat (.arg (Assignments F) (.except EvalError .pure))) :=
  fun nv env => .up (env.FreshFrom nv ∧ facts env ∧
    ∀ (r : FVar F) (nv' : Nat) (env' : Assignments F),
      r.eval env' = .ok (value env) → env'.FreshFrom nv' → env.Le env' →
        (Q.1 r nv' env').down)

end Snarky
