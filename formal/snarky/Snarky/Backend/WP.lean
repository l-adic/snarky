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
program's law is stated as a triple and proved by walking its do-block, with only the
leaf semantic obligations left to hand proofs.

`Std.Do` is experimental (its tactic warns on use; the assertion encoding is documented
as in flux upstream): the bet is confined by the pinned toolchain, and the kernel checks
whatever the framework produces — the axiom gates audit these laws like any other.

The PROVER interpretation of the same monad — `prove`-semantics, where the assignment
table is genuinely mutable state and `EvalError` the exception layer — needs a distinct
type (one monad admits one `WP` shape); the tag is `ProverC`, a name for the reference
backend that selects the prover instances without changing the monad. See the prover
section below.
-/

namespace Snarky

open Std.Do

variable {F c : Type}

/-- The backend's semantic reading of one constraint value under a total valuation —
the parameter the soundness interpretation is generic over. Instances live with their
backends (`Basic` below). -/
class ConstraintHolds (F c : Type) where
  /-- The constraint value is satisfied under the valuation. -/
  Holds : Valuation F → c → Prop

/-- The builder state a soundness triple runs over: the adversary's valuation and the
allocation counter, as ONE object — the prover reading's `ProverState` without an
invariant to carry, since a valuation is total and allocation position never affects
soundness. Bundling keeps the two readings the same shape and leaves room for the
builder's state to grow (labels, public-input slots) without changing every
statement. -/
structure BuilderState (F : Type u) where
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
one extraction law per primitive. A program can only emit what `BasicSystem` offers,
so a law proved over this interface transfers to a new backend by exhibiting one
instance. `Basic` is the reference inhabitant below. -/
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

The framework's recommended spec form is schematic — the postcondition is a parameter,
so `mvcgen` instantiates it exactly at each call site — but written raw it buries a
program's contract in encoding. The shapes are named here once, so each spec reads as
its contract alone.

A proof over these shapes runs: `simp only` with the program's definition to unfold
the body, then `mvcgen` to apply one registered spec, then `simp [circuitVal]` (the
simp set registered in `Circuit/CVar`) to reduce what is left to a field identity,
closed by `grind`/`ring`. Two rewrites must be avoided: `mvcgen [f]` unfolds `f`
instead of consulting the `@[spec]` registry, and plain `simp` rewrites `>>=` past
`wp_bind`. -/

/-- The soundness spec shape, polymorphic in the result: under any consumer `Q`, a
program granting `post` about its result satisfies the caller's obligation —
`⦃Sound post Q⦄ g ⦃Q⦄` reads "`g` guarantees `post` of its result".

Only the counter is quantified in the conclusion: the valuation is read-only, and the
pinned `⟨s.V, nv'⟩` is what lets the caller apply the granted fact at its own
valuation. `post` speaks about the result itself, not a reading of it — each spec
supplies the reading its result type has (`r.val V` for an `FVar`,
`(↑r : CVar F).val V` for a `BoolVar`, componentwise for a bundle), which keeps one
shape serving every return type. A caller never learns how many variables were
allocated. -/
abbrev Sound {α : Type} (post : Valuation F → α → Prop)
    (Q : PostCond α (.arg (BuilderState F) .pure)) :
    Assertion (.arg (BuilderState F) .pure) :=
  fun s => .up (∀ (r : α) (nv' : Nat), post s.V r → (Q.1 r ⟨s.V, nv'⟩).down)

/-! ## The prover reading and its carrier

One monad admits one `WP` shape (`ps` is an `outParam`, so resolution keys on the monad
alone) — the two readings of `CircuitM` must differ somewhere in the type. The tag sits
on the CONSTRAINT parameter, the type argument that already varies: `ProverC F` is
`Basic F` under a name instance search will not unfold. `CircuitM F (ProverC F)` then
keeps the generic `Monad` instance — program bodies elaborate at it, so `mvcgen`
resolves specs and the bind laws with no retagging — while selecting the
`prove`-interpretation's `WP` instance below. The soundness instance stays out of the
way because its `ConstraintHolds` guard has no instance at the tag. The completeness
laws are stated against the reference backend, whose prover checks each constraint as
it is added. -/

/-- The reference backend tagged for the `prove`-interpretation. A program enters the
prover reading by naming the tag — `g (c := ProverC F)` — exactly as a soundness
statement names its backend; the resulting term is definitionally a
`CircuitM F (Basic F)` program, so the interpreter lemmas apply through a `rfl`
retag. -/
def ProverC (F : Type) := Basic F

instance : BasicSystem F (ProverC F) := inferInstanceAs (BasicSystem F (Basic F))

/-- The prover reading: the state is the invariant-carrying `ProverState` (counter,
table, and the freshness relating them — PS's single mutable store, rendered as one
object rather than two arguments), `EvalError` the exception layer. A
total-correctness postcondition (`⇓`) asserts the run cannot fail.

The successor state's invariant is quantified rather than constructed: `∀ hf, Q …
⟨…, hf⟩` avoids a dependent match, and proof irrelevance plus
`ProverState.freshOut` — which inhabits it — make the quantifier free. -/
instance ProverC.instWP [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    WP (CircuitM F (ProverC F)) (.arg (ProverState F) (.except EvalError .pure)) where
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
instance ProverC.instWPMonad [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    WPMonad (CircuitM F (ProverC F)) (.arg (ProverState F) (.except EvalError .pure)) where
  wp_pure a := by
    ext Q st
    simp only [wp, PredTrans.apply]
    exact ⟨fun h => h st.fresh, fun h _ => h⟩
  wp_bind x f := by
    ext Q st
    simp only [PredTrans.apply_Bind_bind]
    simp only [wp, PredTrans.apply]
    rw [show (do let a ← x; f a : CircuitM F (ProverC F) _)
        = (x >>= f : CircuitM F (Basic F) _) from rfl, prove_bind]
    rcases h : prove Basic.holds x st.nv st.env with e | out
    · simp [Except.bind]
    · simp only [Except.bind]
      constructor
      · intro hL _
        exact hL
      · intro hR
        exact hR (ProverState.freshOut (st := st) h)

/-- The completeness spec shape, polymorphic in what the gadget returns: given
`pre` about the incoming table, the run cannot fail, and the caller continues at a
state whose table extends the incoming one — old facts transport along
`Assignments.Le` via `CVar.eval_le`. Reads "`g` succeeds given `pre`, guaranteeing
`post`".

Freshness appears nowhere: `ProverState` carries it. As on the soundness side, `post`
speaks about the result itself and each spec supplies its own reading. No spec
parameter may appear only inside this assertion — such a parameter cannot be
instantiated by unification at a call site, so `mvcgen` leaves it as a bare
metavariable goal. In particular `pre` says `(x.eval env).isOk` rather than
`∃ xv, x.eval env = .ok xv`, and operand facts are quantified in `post`;
`CVar.evalOk` recovers values inside a proof. -/
abbrev Complete {α : Type} (pre : Assignments F → Prop)
    (post : Assignments F → α → Assignments F → Prop)
    (Q : PostCond α (.arg (ProverState F) (.except EvalError .pure))) :
    Assertion (.arg (ProverState F) (.except EvalError .pure)) :=
  fun st => .up (pre st.env ∧
    ∀ (r : α) (st' : ProverState F),
      post st.env r st'.env → st.env.Le st'.env → (Q.1 r st').down)

/-- Extract the value behind a successful-evaluation fact. -/
theorem CVar.evalOk [Add F] [Mul F] {x : CVar F} {env : Assignments F}
    (h : (x.eval env).isOk = true) : ∃ xv, x.eval env = .ok xv := by
  cases hx : x.eval env with
  | error e => rw [hx] at h; cases h
  | ok v => exact ⟨v, rfl⟩

/-- The prover-side reading of "this operand is a bit": it evaluates, and its value
is `0` or `1`. The value is universally quantified rather than existential, for the
reason `Complete` records. -/
def ReadsBit [Add F] [Mul F] [Zero F] [One F] (x : CVar F) (env : Assignments F) : Prop :=
  (x.eval env).isOk ∧ ∀ v, x.eval env = .ok v → v = 0 ∨ v = 1

/-- Name the bit an operand reads as — the form a proof consumes, recovered inside the
proof rather than quantified in the statement. -/
theorem ReadsBit.exists_bit [Add F] [Mul F] [Zero F] [One F] {x : CVar F}
    {env : Assignments F} (h : ReadsBit x env) : ∃ b : Bool, x.eval env = .ok (bit b) := by
  obtain ⟨hok, hbit⟩ := h
  obtain ⟨v, hv⟩ := CVar.evalOk hok
  rcases hbit v hv with h0 | h1
  · exact ⟨false, by rw [hv, h0]; rfl⟩
  · exact ⟨true, by rw [hv, h1]; rfl⟩

/-! ## Running a schematic spec

The spec shapes are continuation-passing: `Q` is a bound consumer, so application at a
call site is unification. Instantiating `Q` at the spec's own post — the identity
continuation — recovers the plain interpreter-level statement, and the converse holds
because each shape's conclusion pins what its reading keeps fixed. The two
equivalences below state this per shape. -/

open Std.Do in
/-- The schematic soundness triple, quantified over `Q`, is the plain interpreter
law: every satisfying assignment pins the built result. -/
theorem sound_spec_iff [ConstraintHolds F c] {α : Type}
    (g : CircuitM F c α) (post : Valuation F → α → Prop) :
    (∀ Q : PostCond α (.arg (BuilderState F) .pure), ⦃Sound post Q⦄ g ⦃Q⦄)
      ↔ ∀ (V : Valuation F) (nv : Nat),
          (∀ con ∈ (build g nv).constraints, ConstraintHolds.Holds V con) →
          post V (build g nv).result := by
  constructor
  · intro h V nv hsat
    exact h (PostCond.noThrow fun r s => ⌜post s.V r⌝) ⟨V, nv⟩ (fun r _ hp => hp) hsat
  · intro h Q s hpre hsat
    exact hpre (build g s.nv).result (build g s.nv).nextVar (h s.V s.nv hsat)

open Std.Do in
/-- The schematic completeness triple, quantified over `Q`, is the honest-run
existential: from any invariant-carrying state satisfying `pre`, the run succeeds,
grants `post`, and only extends the table. The forward direction runs at the
total-correctness continuation (`False` on the exception channel forces success). -/
theorem complete_spec_iff {F : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {α : Type} (g : CircuitM F (ProverC F) α)
    (pre : Assignments F → Prop) (post : Assignments F → α → Assignments F → Prop) :
    (∀ Q : PostCond α (.arg (ProverState F) (.except EvalError .pure)),
        ⦃Complete pre post Q⦄ g ⦃Q⦄)
      ↔ ∀ st : ProverState F, pre st.env →
          ∃ out : Proved F α, prove Basic.holds g st.nv st.env = .ok out
            ∧ post st.env out.result out.assignments ∧ st.env.Le out.assignments := by
  constructor
  · intro h st hpre
    have hw := h (PostCond.noThrow fun r st' => ⌜post st.env r st'.env ∧ st.env.Le st'.env⌝)
      st ⟨hpre, fun r st' hp hle => ⟨hp, hle⟩⟩
    rcases hrun : prove Basic.holds g st.nv st.env with e | out
    · simp only [wp, PredTrans.apply, hrun] at hw
      cases hw
    · simp only [wp, PredTrans.apply, hrun] at hw
      obtain ⟨hp, hle⟩ := hw (ProverState.freshOut (st := st) hrun)
      exact ⟨out, rfl, hp, hle⟩
  · intro h Q st hpre
    obtain ⟨hp, hk⟩ := hpre
    obtain ⟨out, hrun, hpost, hle⟩ := h st hp
    simp only [wp, PredTrans.apply, hrun]
    intro hf
    exact hk out.result ⟨out.nextVar, out.assignments, hf⟩ hpost hle

/-! ## Primitive specs

Triple laws for the monad's own operations: emitting a row, and witnessing a checked
boolean. `witness` at other value types carries no triple of its own — each gadget's law
covers its witness through its private run lemma. -/

open Std.Do in
/-- Emitting a row assumes it. -/
@[spec] theorem addConstraint_spec [ConstraintHolds F c]
    (con : c) (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => ConstraintHolds.Holds V con) Q⦄
    addConstraint (F := F) (c := c) con
    ⦃Q⦄ := by
  intro s hpre hsat
  exact hpre PUnit.unit _ (hsat con (List.mem_cons_self ..))

open Std.Do in
/-- The row's own check is the precondition; the state is unchanged. -/
@[spec] theorem addConstraint_complete_spec {F : Type} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] (con : Basic F)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => Basic.holds con env = true) (fun _ _ _ => True) Q⦄
    addConstraint (F := F) (c := ProverC F) con
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨hch, hk⟩ := hpre
  simp only [wp, PredTrans.apply, addConstraint, prove, hch, if_true]
  exact fun _ => hk PUnit.unit st trivial (Assignments.Le.refl st.env)

open Std.Do in
/-- A witness promises nothing on the soundness side — uniformly sound for every
`CheckedType`, since a caller who learns nothing learns nothing falsely. The leaf that
lets a walk glide over any `witness` whose content arrives through a later
constraint. -/
@[spec] theorem witness_spec {val var : Type} [CircuitType F val var]
    [BasicSystem F c] [ConstraintHolds F c] [CheckedType F c var] (w : AsProver F val)
    (Q : PostCond var (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun _ (_ : var) => True) Q⦄
    (witness (val := val) w : CircuitM F c var)
    ⦃Q⦄ := by
  intro s hpre hsat
  exact hpre _ _ trivial

open Std.Do in
/-- The checked witness's `boolean` row makes the result a bit. -/
@[spec] theorem witnessBool_spec [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (w : AsProver F Bool) (Q : PostCond (BoolVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : BoolVar F) => (↑r : CVar F).val V = 0 ∨ (↑r : CVar F).val V = 1) Q⦄
    (witness (val := Bool) w : CircuitM F c (BoolVar F))
    ⦃Q⦄ := by
  intro s hpre hsat
  exact hpre (.unchecked (.var s.nv)) _
    (LawfulBasicSystem.holds_boolean s.V _ (hsat _ (List.mem_cons_self ..)))

/-- The honest run of one checked-`Bool` witness: the `boolean` row always accepts a
bit. The run equation behind `witnessBool_complete_spec`. -/
private theorem prove_witnessBool {F : Type} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] {w : AsProver F Bool} {nv : Nat} {env : Assignments F} {b : Bool}
    (hw : w env = .ok b) (hfresh : env.FreshFrom nv) :
    prove Basic.holds (witness (val := Bool) w : CircuitM F (Basic F) (BoolVar F)) nv env
      = .ok ⟨.unchecked (.var nv), nv + 1, env.extend nv (bit b)⟩ := by
  have hnv : env nv = none := hfresh nv (Nat.le_refl nv)
  have hwit : (w env).map (CircuitType.valueToFields (F := F) (val := Bool))
      = .ok ⟨#[bit b], rfl⟩ := by rw [hw]; rfl
  have hext : env.extendPairs
      ((allocRange nv 1).toList.zip (⟨#[bit b], rfl⟩ : Vector F 1).toList)
      = .ok (env.extend nv (bit b)) := by
    show env.extendPairs [(nv, bit b)] = .ok _
    simp [Assignments.extendPairs, hnv]
  have hch : Basic.holds (.boolean (.var nv)) (env.extend nv (bit b)) = true := by
    cases b <;> simp [Basic.holds, CVar.eval, Assignments.extend, bit]
  show prove Basic.holds (.existsOp 1 (fun e => (w e).map _) _) nv env = _
  simp only [prove, hwit, hext]
  show prove Basic.holds
    (.addConstraintOp (.boolean (.var nv)) (.pure (BoolVar.unchecked (.var nv)))) (nv + 1)
    (env.extend nv (bit b)) = _
  simp only [prove, hch, if_true]

open Std.Do in
/-- A witness computation that succeeds makes the run succeed, and the result reads
as the computed bit's encoding. -/
@[spec] theorem witnessBool_complete_spec {F : Type} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] (w : AsProver F Bool)
    (Q : PostCond (BoolVar F) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (w env).isOk)
        (fun env (r : BoolVar F) env' => ∀ b, w env = .ok b →
          (↑r : CVar F).eval env' = .ok (bit b)) Q⦄
    (witness (val := Bool) w : CircuitM F (ProverC F) (BoolVar F))
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨hok, hk⟩ := hpre
  obtain ⟨b, hw⟩ : ∃ b, w st.env = .ok b := by
    cases hwe : w st.env with
    | error e => rw [hwe] at hok; cases hok
    | ok b => exact ⟨b, rfl⟩
  rw [show (witness (val := Bool) w : CircuitM F (ProverC F) (BoolVar F))
      = (witness (val := Bool) w : CircuitM F (Basic F) (BoolVar F)) from rfl]
  simp only [wp, PredTrans.apply, prove_witnessBool hw st.fresh]
  intro hf
  refine hk (.unchecked (.var st.nv)) ⟨st.nv + 1, st.env.extend st.nv (bit b), hf⟩
    (fun b' hb' => ?_) (Assignments.le_extend_self st.fresh _)
  rw [hw] at hb'
  injection hb' with hb'
  subst hb'
  simp [circuitVal]

/-! ## The vector loop rule

The `Sound` and `Complete` laws of `generateVec`, given a spec for each component —
the analogue of the framework's `Spec.forIn_list`. They cannot be `@[spec]`: the
componentwise hypothesis is the caller's to supply. -/

open Std.Do in
/-- Componentwise guarantees aggregate componentwise. No invariant beyond the
components' own facts: the valuation is read-only, so nothing threads. -/
theorem generateVec_spec {α : Type} [ConstraintHolds F c] :
    ∀ (n : Nat) (f : Fin n → CircuitM F c α) (post : Fin n → Valuation F → α → Prop),
      (∀ (i : Fin n) (Q : PostCond α (.arg (BuilderState F) .pure)),
        ⦃Sound (post i) Q⦄ f i ⦃Q⦄) →
      ∀ (Q : PostCond (Vector α n) (.arg (BuilderState F) .pure)),
        ⦃Sound (fun V (rs : Vector α n) => ∀ i : Fin n, post i V rs[i]) Q⦄
        generateVec n f
        ⦃Q⦄ := by
  intro n
  induction n with
  | zero =>
    intro f post hf Q s hpre _
    exact hpre #v[] s.nv (fun i => i.elim0)
  | succ n ih =>
    intro f post hf Q s hpre
    show (wp⟦(generateVec n fun i => f i.castSucc) >>= fun init =>
        f (Fin.last n) >>= fun last => pure (init.push last)⟧ Q s).down
    simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
    refine ih _ _ (fun i Q => hf i.castSucc Q) _ s (fun init nv₁ hinit => ?_)
    refine hf (Fin.last n) _ ⟨s.V, nv₁⟩ (fun last nv₂ hlast => ?_)
    intro _
    refine hpre (init.push last) nv₂ (fun i => ?_)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hlast
    · simpa using hinit j

open Std.Do in
/-- Componentwise runs chain, given that each component's `pre` and `post` transport
along table extension — the two hypotheses that replace a loop invariant, since the
prover's table grows. -/
theorem generateVec_complete_spec {F : Type} {α : Type} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] :
    ∀ (n : Nat) (f : Fin n → CircuitM F (ProverC F) α)
      (pre : Fin n → Assignments F → Prop)
      (post : Fin n → Assignments F → α → Assignments F → Prop),
      (∀ (i : Fin n) (Q : PostCond α (.arg (ProverState F) (.except EvalError .pure))),
        ⦃Complete (pre i) (post i) Q⦄ f i ⦃Q⦄) →
      (∀ (i : Fin n) (env env' : Assignments F), env.Le env' → pre i env → pre i env') →
      (∀ (i : Fin n) (env₀ env₁ : Assignments F) (r : α) (env₂ env₃ : Assignments F),
        env₀.Le env₁ → env₂.Le env₃ → post i env₁ r env₂ → post i env₀ r env₃) →
      ∀ (Q : PostCond (Vector α n) (.arg (ProverState F) (.except EvalError .pure))),
        ⦃Complete (fun env => ∀ i : Fin n, pre i env)
            (fun env rs env' => ∀ i : Fin n, post i env rs[i] env') Q⦄
        generateVec n f
        ⦃Q⦄ := by
  intro n
  induction n with
  | zero =>
    intro f pre post hf hpremono hpostmono Q st hpre
    obtain ⟨hpres, hk⟩ := hpre
    exact fun _ => hk #v[] st (fun i => i.elim0) (Assignments.Le.refl st.env)
  | succ n ih =>
    intro f pre post hf hpremono hpostmono Q st hpre
    obtain ⟨hpres, hk⟩ := hpre
    show (wp⟦(generateVec n fun i => f i.castSucc) >>= fun init =>
        f (Fin.last n) >>= fun last => pure (init.push last)⟧ Q st).down
    simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
    refine ih _ _ _ (fun i Q => hf i.castSucc Q) (fun i => hpremono i.castSucc)
      (fun i => hpostmono i.castSucc) _ st
      ⟨fun i => hpres i.castSucc, fun init st₁ hinit hle₁ => ?_⟩
    refine hf (Fin.last n) _ st₁
      ⟨hpremono _ _ _ hle₁ (hpres (Fin.last n)), fun last st₂ hlast hle₂ => ?_⟩
    intro _
    refine hk (init.push last) st₂ (fun i => ?_) (hle₁.trans hle₂)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hpostmono _ st.env st₁.env last st₂.env st₂.env hle₁
        (Assignments.Le.refl st₂.env) hlast
    · simpa using hpostmono _ st.env st.env init[j] st₁.env st₂.env
        (Assignments.Le.refl st.env) hle₂ (hinit j)

/-! ## The alignment bridge

Soundness states what the constraints force; completeness states what the prover
computes. `post_of_prove` connects them: an honest run's result satisfies any
soundness relation the program carries, read at the completion of the final table
(`Assignments.toValuation`). -/

open Std.Do in
/-- Apply a program's `Sound` triple at the completed final table: the satisfaction
hypothesis is what `prove_complete` establishes, and `prove_build_agrees` identifies
the two interpreters' results. -/
theorem post_of_prove {F : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {α : Type} {post : Valuation F → α → Prop} {g : CircuitM F (Basic F) α}
    (hspec : ∀ Q, ⦃Sound post Q⦄ g ⦃Q⦄)
    {nv : Nat} {env env' : Assignments F} {nv' : Nat} {x : α}
    (hrun : prove Basic.holds g nv env = .ok ⟨x, nv', env'⟩) :
    post env'.toValuation x := by
  have hsat : ∀ con ∈ (build g nv).constraints,
      ConstraintHolds.Holds env'.toValuation con := by
    intro con hcon
    have h1 : Basic.holds con env' = true :=
      prove_complete (holds := Basic.holds)
        (fun _con _ _ hle hh => Basic.holds_mono hle hh) hrun con hcon
    exact Basic.holds_mono (Assignments.le_toValuation env') h1
  have h2 := hspec (PostCond.noThrow fun r s => ⌜post s.V r⌝)
    ⟨env'.toValuation, nv⟩ (fun r _ h => h) hsat
  have h3 := prove_build_agrees hrun
  rw [h3.1] at h2
  exact h2

end Snarky
