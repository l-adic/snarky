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

/-- The builder state a soundness triple runs over: the adversary's valuation and the
allocation counter, as ONE object — the prover reading's `ProverState` without an
invariant to carry, since a valuation is total and allocation position never affects
soundness. Bundling keeps the two readings the same shape and leaves room for the
builder's state to grow (labels, public-input slots) without changing every
statement. -/
structure BuilderState (F : Type) where
  /-- The adversary's witness — total, fixed for the whole run. -/
  V : Valuation F
  /-- The next-variable counter the run allocates from. -/
  nv : Nat

/-- The soundness reading of `build`: emitted constraints become assumptions on the
valuation. -/
instance CircuitM.instWP [ConstraintHolds F c] :
    WP (CircuitM F c) (.arg (BuilderState F) .pure) where
  wp x := {
    trans := fun Q s =>
      .up ((∀ con ∈ (build x s.nv).constraints, ConstraintHolds.Holds s.V con) →
        (Q.1 (build x s.nv).result ⟨s.V, (build x s.nv).nextVar⟩).down)
    conjunctiveRaw := by
      intro Q₁ Q₂
      apply SPred.bientails.of_eq
      ext s
      simp [SPred.and, imp_and]
  }

/-- `wp` is a monad morphism: `pure` emits nothing, and a sequence's constraints
concatenate (`build_bind`), the satisfaction hypothesis currying across the split. -/
instance CircuitM.instWPMonad [ConstraintHolds F c] :
    WPMonad (CircuitM F c) (.arg (BuilderState F) .pure) where
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

/-- **The soundness spec shape**, polymorphic in what the gadget returns: under
`Q`-whatever-comes-next, a gadget granting `post` about its result satisfies the
caller's obligation. `⦃Sound post Q⦄ g ⦃Q⦄` reads "`g` guarantees `post` of its
result".

Only the counter is quantified in the conclusion: the valuation is read-only, so the
successor state is `⟨s.V, nv'⟩` — quantifying the whole state would lose that and
break composition. `post` speaks about the RESULT ITSELF, not a reading of it — each gadget's spec
applies whichever reading its result type has (`r.val V` for an `FVar`,
`(↑r : CVar F).val V` for a `BoolVar`, componentwise for a bundle), which is what
keeps one shape serving every return type. The final counter is quantified: a
caller never learns how many variables a gadget allocated. -/
abbrev Sound {α : Type} (post : Valuation F → α → Prop)
    (Q : PostCond α (.arg (BuilderState F) .pure)) :
    Assertion (.arg (BuilderState F) .pure) :=
  fun s => .up (∀ (r : α) (nv' : Nat), post s.V r → (Q.1 r ⟨s.V, nv'⟩).down)

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

/-- The prover reading: the state is the invariant-carrying `ProverState` (counter,
table, and the freshness relating them — PS's single mutable store, rendered as one
object rather than two arguments), `EvalError` the exception layer. A
total-correctness postcondition (`⇓`) asserts the run cannot fail.

The successor state's invariant is quantified rather than constructed: `∀ hf, Q …
⟨…, hf⟩` avoids a dependent match, and proof irrelevance plus
`ProverState.freshOut` — which inhabits it — make the quantifier free. -/
instance ProverM.instWP [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    WP (ProverM F) (.arg (ProverState F) (.except EvalError .pure)) where
  wp x := {
    trans := fun Q st =>
      match prove Basic.holds x st.nv st.env with
      | .ok out => .up (∀ hf : out.assignments.FreshFrom out.nextVar,
          (Q.1 out.result ⟨out.nextVar, out.assignments, hf⟩).down)
      | .error e => Q.2.1 e
    conjunctiveRaw := by
      intro Q₁ Q₂
      apply SPred.bientails.of_eq
      ext st
      rcases h : prove Basic.holds x st.nv st.env with e | out <;>
        simp [SPred.and, ExceptConds.and, h, forall_and]
  }

/-- The prover `wp` is a monad morphism: `prove_bind` is the composition law, and the
intermediate state's invariant — the quantifier the successor carries — is discharged
by `ProverState.freshOut`. -/
instance ProverM.instWPMonad [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    WPMonad (ProverM F) (.arg (ProverState F) (.except EvalError .pure)) where
  wp_pure a := by
    ext Q st
    simp only [wp, PredTrans.apply]
    exact ⟨fun h => h st.fresh, fun h _ => h⟩
  wp_bind x f := by
    ext Q st
    simp only [PredTrans.apply_Bind_bind]
    simp only [wp, PredTrans.apply]
    rw [show (do let a ← x; f a : ProverM F _)
        = (x >>= f : CircuitM F (Basic F) _) from rfl, prove_bind]
    rcases h : prove Basic.holds x st.nv st.env with e | out
    · simp [Except.bind]
    · simp only [Except.bind]
      constructor
      · intro hL _
        exact hL
      · intro hR
        exact hR (ProverState.freshOut (st := st) h)

/-- **The prover-reading spec shape**, polymorphic in what the gadget returns: given
`pre` about the incoming table, the run cannot fail, and the caller continues at a
state whose table extends the incoming one — old facts transport along
`Assignments.Le` via `CVar.eval_le`. Reads "`g` succeeds given `pre`, guaranteeing
`post`".

Freshness appears nowhere: `ProverState` carries it. As on the soundness side, `post`
speaks about the result itself and each spec supplies its own reading. `pre` should
say `(x.eval env).isOk` rather than `∃ xv, x.eval env = .ok xv` — an existential
leaks an uninstantiable metavariable at call sites; `CVar.evalOk` recovers the value
inside the proof. -/
abbrev ProverSpec {α : Type} (pre : Assignments F → Prop)
    (post : Assignments F → α → Assignments F → Prop)
    (Q : PostCond α (.arg (ProverState F) (.except EvalError .pure))) :
    Assertion (.arg (ProverState F) (.except EvalError .pure)) :=
  fun st => .up (pre st.env ∧
    ∀ (r : α) (st' : ProverState F),
      post st.env r st'.env → st.env.Le st'.env → (Q.1 r st').down)

/-- Extract the value behind a successful-evaluation fact — the bridge from the
metavariable-free `isOk` form the specs' `facts` use to the equation their proofs
consume. -/
theorem CVar.evalOk [Add F] [Mul F] {x : CVar F} {env : Assignments F}
    (h : (x.eval env).isOk = true) : ∃ xv, x.eval env = .ok xv := by
  cases hx : x.eval env with
  | error e => rw [hx] at h; cases h
  | ok v => exact ⟨v, rfl⟩

/-! ## Reading a program at the prover carrier

A gadget's body elaborates its binds at `CircuitM` (its definition site), so the
prover reading's `wp_bind` — whose binds are the carrier's — never matches, and the
verification-condition generator resolves `WPMonad` from the bind's instance, finds
the SOUNDNESS interpretation, and abandons the goal. The retag is definitional (the
instances differ only by name) and rewrites a program into the carrier's binds. -/

/-- Retag a bind at the prover carrier. -/
@[simp] theorem ProverM.retag_bind [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {α β : Type} (x : CircuitM F (Basic F) α) (f : α → CircuitM F (Basic F) β) :
    (x >>= f : CircuitM F (Basic F) β) = ((x : ProverM F α) >>= f : ProverM F β) := rfl

end Snarky
