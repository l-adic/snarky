import Std.Do
import Snarky.Backend.Builder
import Snarky.Backend.Prover

/-!
# The weakest-precondition interpretation of `build`

The soundness reading of a circuit, packaged for Lean core's `Std.Do` program-logic
framework: a circuit is a program whose only effect is to ASSUME facts about an ambient
adversarial witness — each emitted constraint is an assumption on the valuation. The
valuation indexes the reading: `Builder V c` tags the constraint type with it, so
`wp⟦x⟧ Q` at `nv` is "if every constraint `build x nv` emits holds under `V`, then `Q`
holds of the built result at the advanced counter". The counter is the program's only
state.

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

/-- The soundness tag: the constraint type indexed by the adversary's valuation. A
program enters the soundness reading by naming the tag — `g (c := Builder V c)` — and
every sub-call of its body elaborates at the same `V`, so no valuation is threaded
through any statement: a spec quantifies `V` once, and a call site fixes it by unifying
the program's type. `Builder V c` is `c` under a name instance search will not unfold,
so the reading has its own `WP` shape while the body keeps the generic `Monad`
instance; the resulting term is definitionally a `CircuitM F c` program, so the
interpreter lemmas apply through a `rfl` retag. Classes with generic instances
(`CheckedType`) are bound at the tag, never forwarded: a forwarder would give a second
derivation the non-reducible tag keeps from unifying with the generic one. The
valuation is a phantom index (Mathlib's `WithLp` shape), hence the linter exemption. -/
@[nolint unusedArguments] def Builder (_ : Valuation F) (c : Type) := c

instance [inst : BasicSystem F c] : BasicSystem F (Builder V c) := inst
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

instance [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] [ConstraintHolds F c]
    [inst : LawfulBasicSystem F c] : LawfulBasicSystem F (Builder V c) := inst

/-- A pure assertion's content, for the `circuitVal` closers: what a leaf proof is left
with after the satisfaction hypothesis is introduced. -/
@[circuitVal, simp] theorem idiom_down_nil (P : Prop) : (⌜P⌝ : SPred []).down = P := rfl

/-- The same, one state layer down. -/
@[circuitVal, simp] theorem idiom_down_cons (P : Prop) (n : Nat) :
    ((⌜P⌝ : SPred [Nat]) n).down = P := rfl

/-! ## Spec shapes

A soundness spec is the framework's native triple at the tag,
`⦃⌜pre⌝⦄ g (c := Builder V c) ⦃⇓ r _ => ⌜post r⌝⦄`: `pre` the operand facts the
caller holds at the call (`⌜True⌝` when there are none — building never fails), `post`
the fact the constraints force about the result at `V`. `post` speaks about the
result itself, not a reading of it — each spec supplies the reading its result type
has (`r.val V` for an `FVar`, `(↑r : CVar F).val V` for a `BoolVar`, componentwise for
a bundle), which keeps one shape serving every return type. A caller never learns how
many variables were allocated. Facts established only later in a run (a regime of a
decoded scalar, a computed coordinate's nonvanishing) stay implications inside `post`.

A proof over this shape runs: `simp only` with the program's definition to unfold
the body, then ONE `mvcgen`, which applies the registered spec of every step and
leaves each granted fact as a hypothesis, then `simp [circuitVal]` (the simp set
registered in `Circuit/CVar`) to reduce what is left to a field identity, closed by
`grind`/`ring`. Two rewrites must be avoided: `mvcgen [f]` unfolds `f` instead of
consulting the `@[spec]` registry, and plain `simp` rewrites `>>=` past `wp_bind`. -/

/-! ## The prover reading and its carrier

One monad admits one `WP` shape (`ps` is an `outParam`, so resolution keys on the monad
alone) — the two readings of `CircuitM` must differ somewhere in the type. The tag sits
on the CONSTRAINT parameter, the type argument that already varies: `Prover c` is `c`
under a name instance search will not unfold. `CircuitM F (Prover c)` then
keeps the generic `Monad` instance — program bodies elaborate at it, so `mvcgen`
resolves specs and the bind laws with no retagging — while selecting the
`prove`-interpretation's `WP` instance below. The soundness instance stays out of the
way because its `ConstraintHolds` guard has no instance at the tag. The completeness
laws are stated against any backend whose prover-side check accepts honest values
(`LawfulChecker` below); `ProverC` names the reference instantiation. -/

/-- The backend's decidable per-constraint check — the prover-side dual of
`ConstraintHolds`. Instances live with their backends (`Basic` below). -/
class Checker (F c : Type) where
  /-- The constraint value passes the backend's check on the current table. -/
  holds : c → Assignments F → Bool

/-- A checkable backend tagged for the `prove`-interpretation. A program enters the
prover reading by naming the tag — `g (c := Prover c)` — exactly as a soundness
statement names its backend; the resulting term is definitionally a `CircuitM F c`
program, so the interpreter lemmas apply through a `rfl` retag. -/
def Prover (c : Type) := c

instance [inst : BasicSystem F c] : BasicSystem F (Prover c) := inst

/-- The prover reading: the state is the invariant-carrying `ProverState` (counter,
table, and the freshness relating them — PS's single mutable store, rendered as one
object rather than two arguments), `EvalError` the exception layer. A
total-correctness postcondition (`⇓`) asserts the run cannot fail.

The successor state's invariant is quantified rather than constructed: `∀ hf, Q …
⟨…, hf⟩` avoids a dependent match, and proof irrelevance plus
`ProverState.freshOut` — which inhabits it — make the quantifier free. -/
instance Prover.instWP [Checker F c] :
    WP (CircuitM F (Prover c)) (.arg (ProverState F) (.except EvalError .pure)) where
  wp x := {
    trans := fun Q st =>
      match prove (Checker.holds (F := F) (c := c)) x st.nv st.env with
      | .ok out => .up (∀ hf : out.assignments.FreshFrom out.nextVar,
          (Q.1 out.result ⟨out.nextVar, out.assignments, hf⟩).down)
      | .error e => Q.2.1 e
    conjunctiveRaw := by
      intro Q₁ Q₂
      apply SPred.bientails.of_eq
      ext st
      rcases h : prove (Checker.holds (F := F) (c := c)) x st.nv st.env with e | out <;>
        simp [SPred.and, ExceptConds.and, h, forall_and]
  }

/-- The prover `wp` is a monad morphism: `prove_bind` is the composition law, and the
intermediate state's invariant — the quantifier the successor carries — is discharged
by `ProverState.freshOut`. -/
instance Prover.instWPMonad [Checker F c] :
    WPMonad (CircuitM F (Prover c)) (.arg (ProverState F) (.except EvalError .pure)) where
  wp_pure a := by
    ext Q st
    simp only [wp, PredTrans.apply]
    exact ⟨fun h => h st.fresh, fun h _ => h⟩
  wp_bind x f := by
    ext Q st
    simp only [PredTrans.apply_Bind_bind]
    simp only [wp, PredTrans.apply]
    rw [show (do let a ← x; f a : CircuitM F (Prover c) _)
        = (x >>= f : CircuitM F c _) from rfl, prove_bind]
    rcases h : prove (Checker.holds (F := F) (c := c)) x st.nv st.env with e | out
    · simp [Except.bind]
    · simp only [Except.bind]
      constructor
      · intro hL _
        exact hL
      · intro hR
        exact hR (ProverState.freshOut (st := st) h)

/-- `Basic`'s check is its checker (the reference instance). -/
instance Basic.instChecker [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    Checker F (Basic F) :=
  ⟨Basic.holds⟩

/-- The reference prover carrier: the checking reading at the `Basic` backend, where
the demos and examples run. -/
abbrev ProverC (F : Type) := Prover (Basic F)

/-- The honest values pass the check: the completeness-side dual of
`LawfulBasicSystem`, one implication per `BasicSystem` primitive — all a completeness
proof consumes (rejection is the exhibits' territory). `Basic`'s instance is the
reference inhabitant below. -/
class LawfulChecker (F c : Type) [Add F] [Mul F] [Zero F] [One F]
    [BasicSystem F c] [Checker F c] : Prop where
  /-- Equal evaluations pass the `equal` check. -/
  check_equal : ∀ (env : Assignments F) (a b : CVar F) (v : F),
    a.eval env = .ok v → b.eval env = .ok v →
    Checker.holds (BasicSystem.equal (c := c) a b) env = true
  /-- A product identity passes the `r1cs` check. -/
  check_r1cs : ∀ (env : Assignments F) (l r o : CVar F) (x y z : F),
    l.eval env = .ok x → r.eval env = .ok y → o.eval env = .ok z →
    x * y = z → Checker.holds (BasicSystem.r1cs (c := c) l r o) env = true
  /-- A square identity passes the `square` check. -/
  check_square : ∀ (env : Assignments F) (a sq : CVar F) (x z : F),
    a.eval env = .ok x → sq.eval env = .ok z →
    x * x = z → Checker.holds (BasicSystem.square (c := c) a sq) env = true
  /-- A bit passes the `boolean` check. -/
  check_boolean : ∀ (env : Assignments F) (a : CVar F) (v : F),
    a.eval env = .ok v → v = 0 ∨ v = 1 →
    Checker.holds (BasicSystem.boolean (c := c) a) env = true

/-- `Basic` is a lawful checker: each field is its checker computation. -/
instance Basic.instLawfulChecker [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    LawfulChecker F (Basic F) where
  check_equal env a b v ha hb := by
    show Basic.holds (.equal a b) env = true
    simp [Basic.holds, ha, hb]
  check_r1cs env l r o x y z hl hr ho hxyz := by
    show Basic.holds (.r1cs l r o) env = true
    simp [Basic.holds, hl, hr, ho, hxyz]
  check_square env a sq x z ha hsq hxz := by
    show Basic.holds (.square a sq) env = true
    simp [Basic.holds, ha, hsq, hxz]
  check_boolean env a v ha hb := by
    show Basic.holds (.boolean a) env = true
    simp only [Basic.holds, ha]
    rcases hb with h | h <;> simp [h]

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

/-- A pinned evaluation is a successful one — the converse direction of
`CVar.evalOk`, for building `Complete` preconditions from granted equations. -/
theorem isOk_of_eq {ε α : Type} {x : Except ε α} {v : α} (h : x = .ok v) :
    x.isOk := by
  rw [h]; rfl

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

/-- The canonical producer fact introduces the reading: an operand that reads as
`bit b` `ReadsBit` — how one gadget's grant becomes the next gadget's precondition. -/
theorem ReadsBit.of_bit [Add F] [Mul F] [Zero F] [One F] {x : CVar F}
    {env : Assignments F} {b : Bool} (h : x.eval env = .ok (bit b)) :
    ReadsBit x env := by
  refine ⟨by rw [h]; rfl, fun w hw => ?_⟩
  rw [h] at hw
  injection hw with hw
  subst hw
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Name the bit an operand reads as — the form a proof consumes, recovered inside the
proof rather than quantified in the statement. -/
theorem ReadsBit.exists_bit [Add F] [Mul F] [Zero F] [One F] {x : CVar F}
    {env : Assignments F} (h : ReadsBit x env) : ∃ b : Bool, x.eval env = .ok (bit b) := by
  obtain ⟨hok, hbit⟩ := h
  obtain ⟨v, hv⟩ := CVar.evalOk hok
  rcases hbit v hv with h0 | h1
  · exact ⟨false, by rw [hv, h0]; rfl⟩
  · exact ⟨true, by rw [hv, h1]; rfl⟩

/-- The reading survives table extension. -/
theorem ReadsBit.mono [Add F] [Mul F] [Zero F] [One F] {x : CVar F}
    {env env' : Assignments F} (hle : env.Le env') (h : ReadsBit x env) :
    ReadsBit x env' := by
  obtain ⟨b, hb⟩ := h.exists_bit
  exact .of_bit (CVar.eval_le hle hb)

/-! ## Running a schematic spec

The spec shapes are continuation-passing: `Q` is a bound consumer, so application at a
call site is unification. Instantiating `Q` at the spec's own post — the identity
continuation — recovers the plain interpreter-level statement, and the converse holds
because each shape's conclusion pins what its reading keeps fixed. The two
equivalences below state this per shape. -/

open Std.Do in
/-- The soundness triple at the tag is the plain interpreter law: every satisfying
assignment pins the built result. -/
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

open Std.Do in
/-- The schematic completeness triple, quantified over `Q`, is the honest-run
existential: from any invariant-carrying state satisfying `pre`, the run succeeds,
grants `post`, and only extends the table. The forward direction runs at the
total-correctness continuation (`False` on the exception channel forces success). -/
theorem complete_spec_iff {F c : Type} [Checker F c]
    {α : Type} (g : CircuitM F (Prover c) α)
    (pre : Assignments F → Prop) (post : Assignments F → α → Assignments F → Prop) :
    (∀ Q : PostCond α (.arg (ProverState F) (.except EvalError .pure)),
        ⦃Complete pre post Q⦄ g ⦃Q⦄)
      ↔ ∀ st : ProverState F, pre st.env →
          ∃ out : Proved F α,
            prove (Checker.holds (F := F) (c := c)) g st.nv st.env = .ok out
            ∧ post st.env out.result out.assignments ∧ st.env.Le out.assignments := by
  constructor
  · intro h st hpre
    have hw := h (PostCond.noThrow fun r st' => ⌜post st.env r st'.env ∧ st.env.Le st'.env⌝)
      st ⟨hpre, fun r st' hp hle => ⟨hp, hle⟩⟩
    rcases hrun : prove (Checker.holds (F := F) (c := c)) g st.nv st.env with e | out
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
@[spec] theorem addConstraint_spec {V : Valuation F} [ConstraintHolds F c]
    (con : Builder V c) :
    ⦃⌜True⌝⦄
    addConstraint (F := F) (c := Builder V c) con
    ⦃⇓ _ _ => ⌜ConstraintHolds.Holds V con⌝⦄ := by
  intro nv _ hsat
  exact hsat con (List.mem_cons_self ..)

open Std.Do in
/-- The row's own check is the precondition; the state is unchanged. -/
@[spec] theorem addConstraint_complete_spec {F c : Type} [Checker F c] (con : c)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => Checker.holds (F := F) (c := c) con env = true)
        (fun _ _ _ => True) Q⦄
    addConstraint (F := F) (c := Prover c) con
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨hch, hk⟩ := hpre
  simp only [wp, PredTrans.apply, addConstraint, prove, hch, if_true]
  exact fun _ => hk PUnit.unit st trivial (Assignments.Le.refl st.env)

/-! ## The checked-witness contract

What `witness` grants on the soundness side is whatever its bundle's `check` rows
force — nothing for a field element, a bit for a boolean, the curve equation for a
curve point, componentwise for a bundle. `SoundCheckedType` names that fact per type
and carries the one law, so `witness_spec` is a single leaf over every checked type;
it is the soundness-side companion of `LawfulCheckedType`. Bound at the tag like the
check instance it reads: `CheckedType` has generic instances, so a forwarder would give
a second derivation the tag keeps from unifying. -/

/-- The soundness contract of a `CheckedType` at the tag: `post` is what a bundle's
`check` rows force about it under the valuation, and `check_sound` that they do. -/
class SoundCheckedType (F c : Type) (V : Valuation F) (var : Type) [ConstraintHolds F c]
    [CheckedType F (Builder V c) var] where
  /-- What the check's rows force about the bundle. -/
  post : var → Prop
  /-- The rows force it. -/
  check_sound : ∀ bundle : var,
    ⦃⌜True⌝⦄ (CheckedType.check (F := F) (c := Builder V c) bundle) ⦃⇓ _ _ => ⌜post bundle⌝⦄

attribute [spec] SoundCheckedType.check_sound

section SoundCheckedTypeInstances

variable {V : Valuation F} [ConstraintHolds F c]

/-- A field element's check is empty. -/
instance instSoundCheckedTypeF : SoundCheckedType F c V (FVar F) where
  post _ := True
  check_sound _ := by
    intro nv _ _
    trivial

/-- An `UnChecked` bundle's check is empty. -/
instance instSoundCheckedTypeUnChecked {var : Type} :
    SoundCheckedType F c V (UnChecked var) where
  post _ := True
  check_sound _ := by
    intro nv _ _
    trivial

/-- The `boolean` row makes a witnessed boolean a bit. -/
instance instSoundCheckedTypeBool [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [LawfulBasicSystem F c] : SoundCheckedType F c V (BoolVar F) where
  post r := (↑r : CVar F).val V = 0 ∨ (↑r : CVar F).val V = 1
  check_sound b := by
    intro nv _ hsat
    exact LawfulBasicSystem.holds_boolean V _ (hsat _ (List.mem_cons_self ..))

/-- A pair's rows force both components' facts. -/
instance instSoundCheckedTypeProd {avar bvar : Type} [CheckedType F (Builder V c) avar]
    [CheckedType F (Builder V c) bvar] [SA : SoundCheckedType F c V avar]
    [SB : SoundCheckedType F c V bvar] : SoundCheckedType F c V (avar × bvar) where
  post p := SA.post p.1 ∧ SB.post p.2
  check_sound p := by
    show ⦃⌜True⌝⦄ (do CheckedType.check (F := F) (c := Builder V c) p.1
                      CheckedType.check (F := F) (c := Builder V c) p.2) ⦃_⦄
    mvcgen
    rename_i h1 _ _
    intro h2
    exact ⟨h1, h2⟩

/-- A list of checks forces every element's fact — the vector instance's spine. -/
private theorem forM_check_sound {var : Type} [CheckedType F (Builder V c) var]
    [S : SoundCheckedType F c V var] :
    ∀ l : List var,
      ⦃⌜True⌝⦄ (l.forM (CheckedType.check (F := F) (c := Builder V c)))
      ⦃⇓ _ _ => ⌜∀ x ∈ l, S.post x⌝⦄
  | [] => by
    show ⦃⌜True⌝⦄ (pure PUnit.unit : CircuitM F (Builder V c) PUnit) ⦃_⦄
    mvcgen
    simp
  | x :: l => by
    show ⦃⌜True⌝⦄ (do CheckedType.check (F := F) (c := Builder V c) x
                      l.forM (CheckedType.check (F := F) (c := Builder V c))) ⦃_⦄
    have ih := forM_check_sound l
    mvcgen [ih]
    rename_i hx _ _
    intro hl y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact hl y hy

/-- A vector's rows force every component's fact. -/
instance instSoundCheckedTypeVector {var : Type} [CheckedType F (Builder V c) var]
    [S : SoundCheckedType F c V var] {n : Nat} : SoundCheckedType F c V (Vector var n) where
  post v := ∀ x ∈ v.toList, S.post x
  check_sound v := forM_check_sound v.toList

end SoundCheckedTypeInstances

/-- The contract of `var`, read on an isomorphic `var'` — the companion of
`CheckedType.ofEquiv`. -/
@[reducible] def SoundCheckedType.ofEquiv {V : Valuation F} [ConstraintHolds F c] {var var' : Type}
    [CheckedType F (Builder V c) var] [S : SoundCheckedType F c V var] (er : var' ≃ var) :
    @SoundCheckedType F c V var' _ (CheckedType.ofEquiv (F := F) (c := Builder V c) er) :=
  @SoundCheckedType.mk F c V var' _ (CheckedType.ofEquiv (F := F) (c := Builder V c) er)
    (fun r => S.post (er r)) (fun r => S.check_sound (er r))

open Std.Do in
/-- A witness grants its type's contract: the leaf every `witness` step walks through,
whatever the bundle. -/
@[spec] theorem witness_spec {V : Valuation F} {val var : Type} [CircuitType F val var]
    [BasicSystem F c] [ConstraintHolds F c] [CheckedType F (Builder V c) var]
    [S : SoundCheckedType F c V var] (w : AsProver F val) :
    ⦃⌜True⌝⦄
    (witness (val := val) w : CircuitM F (Builder V c) var)
    ⦃⇓ r _ => ⌜S.post r⌝⦄ := by
  intro nv _ hsat
  simp only [witness, build, build_bind, List.append_nil] at hsat ⊢
  exact (builder_spec_iff _ _).mp (S.check_sound _) _ hsat

/-- The contracts, for the `circuitVal` closers and `mvcgen`'s own simplifier. -/
@[circuitVal, simp] theorem SoundCheckedType.post_fvar {V : Valuation F} [ConstraintHolds F c]
    (r : FVar F) : SoundCheckedType.post (F := F) (c := c) (V := V) r = True := rfl

@[circuitVal, simp] theorem SoundCheckedType.post_unChecked {V : Valuation F}
    [ConstraintHolds F c] {var : Type} (r : UnChecked var) :
    SoundCheckedType.post (F := F) (c := c) (V := V) r = True := rfl

@[circuitVal, simp] theorem SoundCheckedType.post_bool {V : Valuation F} [Add F] [Mul F]
    [Zero F] [One F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (r : BoolVar F) :
    SoundCheckedType.post (F := F) (c := c) (V := V) r
      = ((↑r : CVar F).val V = 0 ∨ (↑r : CVar F).val V = 1) := rfl

@[circuitVal, simp] theorem SoundCheckedType.post_prod {V : Valuation F} [ConstraintHolds F c]
    {avar bvar : Type} [CheckedType F (Builder V c) avar] [CheckedType F (Builder V c) bvar]
    [SA : SoundCheckedType F c V avar] [SB : SoundCheckedType F c V bvar] (p : avar × bvar) :
    SoundCheckedType.post (F := F) (c := c) (V := V) p = (SA.post p.1 ∧ SB.post p.2) := rfl

@[circuitVal, simp] theorem SoundCheckedType.post_ofEquiv {V : Valuation F} [ConstraintHolds F c]
    {var var' : Type} [CheckedType F (Builder V c) var] [S : SoundCheckedType F c V var]
    (er : var' ≃ var) (r : var') :
    @SoundCheckedType.post F c V var' _ (CheckedType.ofEquiv (F := F) (c := Builder V c) er)
      (SoundCheckedType.ofEquiv er) r = S.post (er r) := rfl

@[circuitVal, simp] theorem SoundCheckedType.post_vector {V : Valuation F} [ConstraintHolds F c]
    {var : Type} [CheckedType F (Builder V c) var] [S : SoundCheckedType F c V var] {n : Nat}
    (v : Vector var n) :
    SoundCheckedType.post (F := F) (c := c) (V := V) v = ∀ x ∈ v.toList, S.post x := rfl

/-! ## The witness leaf

One completeness spec serves every witnessed type: the honest encoding is written to
fresh slots and passes its own checks (`LawfulCheckedType`), and the promise arrives
as the bundle's `WitnessReads.Reads` — already in the type's own vocabulary, so call
sites consume it directly. -/

/-- The completeness contract of a `CheckedType`: an honest encoding passes its own
checks. PS discharges this dynamically — the prover runs `check` on the freshly
written fields; here it is the class's law, stated as the completeness triple the
witness leaf composes. The check instance is bound at the prover tag so the class has
exactly one derivation path there — a base-`c` binder plus a forwarding instance
would give two derivations the non-reducible tag keeps from unifying. -/
class LawfulCheckedType (F c val var : Type) [Add F] [Mul F]
    [CircuitType F val var] [CheckedType F (Prover c) var] [Checker F c] : Prop where
  /-- On a table where the bundle's fields read as a value's encoding, the check's
  honest run accepts. -/
  check_complete : ∀ (bundle : var) (v : val)
      (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))),
    ⦃Complete
        (fun env =>
          (CircuitType.varToFields (F := F) (val := val) bundle).toList.mapM
              (CVar.eval · env)
            = .ok (CircuitType.valueToFields (F := F) (var := var) v).toList)
        (fun _ _ _ => True) Q⦄
    (CheckedType.check bundle : CircuitM F (Prover c) PUnit)
    ⦃Q⦄

open Std.Do in
/-- The triple of a check-free `check`: a `pure` accepts anything — the
`LawfulCheckedType` witness of every constraint-free leaf encoder. -/
theorem check_pure_complete {F c : Type} [Checker F c]
    {pre : Assignments F → Prop}
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete pre (fun _ _ _ => True) Q⦄
    (.pure PUnit.unit : CircuitM F (Prover c) PUnit)
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨-, hk⟩ := hpre
  simp only [wp, PredTrans.apply, prove]
  intro hf
  exact hk PUnit.unit ⟨st.nv, st.env, hf⟩ trivial (Assignments.Le.refl st.env)

/-- Extract the evaluation behind a singleton fields read. -/
private theorem mapM_eval_singleton {F : Type} [Add F] [Mul F]
    {x : CVar F} {env : Assignments F} {v : F}
    (h : [x].mapM (CVar.eval · env) = .ok [v]) : x.eval env = .ok v := by
  cases he : x.eval env with
  | error e => simp [List.mapM_cons, he, Bind.bind, Except.bind] at h
  | ok y =>
    simp [List.mapM_cons, List.mapM_nil, he, Bind.bind, Except.bind, Pure.pure,
      Except.pure] at h
    rw [h]

instance instLawfulCheckedTypeF {F c : Type} [Add F] [Mul F] [Checker F c] :
    LawfulCheckedType F c F (FVar F) :=
  ⟨fun _ _ Q => check_pure_complete (c := c) Q⟩

instance instLawfulCheckedTypeUnChecked {F c : Type} [Add F] [Mul F]
    {val var : Type} [CircuitType F val var] [Checker F c] :
    LawfulCheckedType F c (UnChecked val) (UnChecked var) :=
  ⟨fun _ _ Q => check_pure_complete (c := c) Q⟩

open Std.Do in
instance instLawfulCheckedTypeBool {F c : Type} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] [BasicSystem F c] [Checker F c] [LawfulChecker F c] :
    LawfulCheckedType F c Bool (BoolVar F) where
  check_complete bundle b Q := by
    intro st hpre
    obtain ⟨hread, hk⟩ := hpre
    have hb : (bundle.toCVar).eval st.env = .ok (bit b) := mapM_eval_singleton hread
    refine addConstraint_complete_spec (c := c) _ Q st
      ⟨?_, fun u st' _ hle => hk u st' trivial hle⟩
    exact LawfulChecker.check_boolean _ _ _ hb (by cases b <;> simp [bit])

/-- The check-completeness contract transports across the equivalences: the
transported grant is the base grant at the mapped bundle and value, definitionally.
Built with `letI` (see `LawfulCircuitType.ofEquiv`). -/
theorem LawfulCheckedType.ofEquiv {F c : Type} [Add F] [Mul F] [Checker F c]
    {val var val' var' : Type} [A : CircuitType F val var]
    [CheckedType F (Prover c) var] [LawfulCheckedType F c val var]
    (ev : val' ≃ val) (er : var' ≃ var) :
    @LawfulCheckedType F c val' var' _ _ (A.ofEquiv ev er)
      (CheckedType.ofEquiv (c := Prover c) er) _ :=
  letI : CircuitType F val' var' := A.ofEquiv ev er
  letI : CheckedType F (Prover c) var' := CheckedType.ofEquiv (c := Prover c) er
  { check_complete := fun bundle v Q =>
      LawfulCheckedType.check_complete (c := c) (val := val) (er bundle) (ev v) Q }

/-- `allocRange`'s underlying list is the consecutive range. -/
private theorem allocRange_toList : ∀ (n nv : Nat),
    (allocRange nv n).toList = List.range' nv n
  | 0, _ => rfl
  | n + 1, nv => by
    have ih := allocRange_toList n (nv + 1)
    simp only [allocRange, Vector.toList_ofFn] at ih ⊢
    rw [List.ofFn_succ, show List.range' nv (n + 1) = nv :: List.range' (nv + 1) n
      from rfl, ← ih]
    congr 1
    refine congrArg List.ofFn (funext fun i => ?_)
    simp only [Fin.val_succ]
    omega

/-- Fresh consecutive slots batch-extend successfully; the table only grows, stays
fresh past the batch, and each slot holds its value. -/
private theorem extendPairs_consecutive {F : Type} :
    ∀ (xs : List F) (nv : Nat) (a : Assignments F), a.FreshFrom nv →
      ∃ a', a.extendPairs ((List.range' nv xs.length).zip xs) = .ok a' ∧
        a.Le a' ∧ a'.FreshFrom (nv + xs.length) ∧
        ∀ i x, xs[i]? = some x → a' (nv + i) = some x
  | [], nv, a, hfresh =>
    ⟨a, rfl, Assignments.Le.refl a, by simpa using hfresh,
      fun i x h => by simp at h⟩
  | x :: rest, nv, a, hfresh => by
    have hnv : a nv = none := hfresh nv (Nat.le_refl nv)
    have hfresh' : (a.extend nv x).FreshFrom (nv + 1) := by
      intro u hu
      have hne : ¬ u = nv := by omega
      simp only [Assignments.extend, if_neg hne]
      exact hfresh u (by omega)
    obtain ⟨a', hrun, hle, hfr, hread⟩ :=
      extendPairs_consecutive rest (nv + 1) (a.extend nv x) hfresh'
    refine ⟨a', ?_, (Assignments.le_extend_self hfresh x).trans hle, ?_, ?_⟩
    · show a.extendPairs
        ((nv :: List.range' (nv + 1) rest.length).zip (x :: rest)) = .ok a'
      simp only [List.zip_cons_cons, Assignments.extendPairs, hnv]
      exact hrun
    · intro u hu
      simp only [List.length_cons] at hu
      exact hfr u (by omega)
    · intro i y hy
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
        exact hy ▸ hle nv x (by simp [Assignments.extend])
      | succ i =>
        have := hread i y (by simpa using hy)
        rw [show nv + (i + 1) = (nv + 1) + i by omega]
        exact this

/-- Consecutive variables read their recorded values on any extension of the table. -/
private theorem mapM_eval_range' {F : Type} [Add F] [Mul F]
    {env env' : Assignments F} (hle : env.Le env') :
    ∀ (xs : List F) (nv : Nat), (∀ i x, xs[i]? = some x → env (nv + i) = some x) →
      ((List.range' nv xs.length).map CVar.var).mapM (CVar.eval · env') = .ok xs
  | [], _, _ => rfl
  | x :: rest, nv, hread => by
    have h0 : env' nv = some x := hle nv x (by simpa using hread 0 x (by simp))
    have hx : (CVar.var nv).eval env' = .ok x := by simp [CVar.eval, h0]
    have ih := mapM_eval_range' hle rest (nv + 1) fun i y hy => by
      have := hread (i + 1) y (by simpa using hy)
      rw [show (nv + 1) + i = nv + (i + 1) by omega]
      exact this
    show ((nv :: List.range' (nv + 1) rest.length).map CVar.var).mapM
      (CVar.eval · env') = _
    simp [List.mapM_cons, hx, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The decoded reading of a witnessed bundle — what the flat fields grant of the
witness leaf means, in the type's own vocabulary. Instances mirror the `CircuitType`
grammar, so a composite bundle's reading computes to its components' readings and no
per-composite extraction lemmas exist: one instance per leaf encoder is the whole
per-type surface. -/
class WitnessReads (F val var : Type) [Add F] [Mul F] [CircuitType F val var] where
  /-- The bundle's decoded reading on a table: `r` witnesses the value `v`. -/
  Reads : var → Assignments F → val → Prop
  /-- The flat fields grant implies the reading. -/
  reads_of_grant : ∀ {r : var} {env : Assignments F} {v : val},
    (CircuitType.varToFields (F := F) (val := val) r).toList.mapM (CVar.eval · env)
      = .ok (CircuitType.valueToFields (F := F) (var := var) v).toList →
    Reads r env v
  /-- The reading survives table extension. -/
  reads_le : ∀ {env env' : Assignments F} {r : var} {v : val},
    env.Le env' → Reads r env v → Reads r env' v

/-- The decoded reading transports across the equivalences: read the mapped bundle
as the mapped value. Built with `letI` (see `LawfulCircuitType.ofEquiv`). -/
@[reducible] def WitnessReads.ofEquiv {F : Type} [Add F] [Mul F]
    {val var val' var' : Type} [A : CircuitType F val var] [WitnessReads F val var]
    (ev : val' ≃ val) (er : var' ≃ var) :
    @WitnessReads F val' var' _ _ (A.ofEquiv ev er) :=
  letI : CircuitType F val' var' := A.ofEquiv ev er
  { Reads := fun r env v => WitnessReads.Reads (F := F) (er r) env (ev v)
    reads_of_grant := fun h => WitnessReads.reads_of_grant h
    reads_le := fun hle h => WitnessReads.reads_le hle h }

open Std.Do in
/-- A witness computation that succeeds makes the run succeed — the honest encoding
passes its own checks — and the bundle reads as the computed value on the final table
(`WitnessReads.Reads`, which at each concrete type computes to its instance's
shape). -/
@[spec] theorem witness_complete_spec {F c val var : Type} [Add F] [Mul F]
    [DecidableEq F] [CircuitType F val var] [LawfulCircuitType F val var]
    [CheckedType F (Prover c) var] [Checker F c] [LawfulCheckedType F c val var]
    [WitnessReads F val var] (w : AsProver F val)
    (Q : PostCond var (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (w env).isOk)
        (fun env (r : var) env' => ∀ v, w env = .ok v →
          WitnessReads.Reads (F := F) r env' v) Q⦄
    (witness (val := val) w : CircuitM F (Prover c) var)
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨hok, hk⟩ := hpre
  obtain ⟨v, hw⟩ : ∃ v, w st.env = .ok v := by
    cases hwe : w st.env with
    | error e => rw [hwe] at hok; cases hok
    | ok v => exact ⟨v, rfl⟩
  have hwit : (w st.env).map (CircuitType.valueToFields (F := F) (val := val))
      = .ok (CircuitType.valueToFields (F := F) (var := var) v) := by rw [hw]; rfl
  obtain ⟨env₁, hext, hle₁, hfr₁, hread⟩ :=
    extendPairs_consecutive
      (CircuitType.valueToFields (F := F) (var := var) v).toList st.nv st.env st.fresh
  have hext' : st.env.extendPairs
      ((allocRange st.nv (CircuitType.size F val)).toList.zip
        (CircuitType.valueToFields (F := F) (var := var) v).toList) = .ok env₁ := by
    rw [allocRange_toList]
    simpa using hext
  have hfr₁' : env₁.FreshFrom (st.nv + CircuitType.size F val) := by
    simpa using hfr₁
  have hvars : ∀ (env'' : Assignments F), env₁.Le env'' →
      (CircuitType.varToFields (F := F) (val := val)
          (CircuitType.fieldsToVar (F := F) (val := val)
            (mapVec CVar.var (allocRange st.nv (CircuitType.size F val))))).toList.mapM
          (CVar.eval · env'')
        = .ok (CircuitType.valueToFields (F := F) (var := var) v).toList := by
    intro env'' hle''
    rw [LawfulCircuitType.vars_roundTrip (F := F) (val := val)]
    show ((allocRange st.nv (CircuitType.size F val)).toList.map CVar.var).mapM
      (CVar.eval · env'') = _
    rw [allocRange_toList]
    have hlen : CircuitType.size F val
        = (CircuitType.valueToFields (F := F) (var := var) v).toList.length := by simp
    conv_lhs => rw [hlen]
    exact mapM_eval_range' hle'' _ st.nv hread
  rw [show (witness (val := val) w : CircuitM F (Prover c) var)
      = ((CircuitM.existsOp (CircuitType.size F val)
            (fun e => (w e).map (CircuitType.valueToFields (F := F) (val := val)))
            (fun vs => CircuitM.pure vs) : CircuitM F (Prover c) _) >>=
          fun vs =>
            (CheckedType.check (c := Prover c)
                (CircuitType.fieldsToVar (F := F) (val := val)
                  (mapVec CVar.var vs)) >>=
              fun _ => pure (CircuitType.fieldsToVar (F := F) (val := val)
                (mapVec CVar.var vs)))) from rfl]
  simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  simp only [wp, PredTrans.apply, prove, hwit, hext']
  intro hf
  refine LawfulCheckedType.check_complete (c := c) (val := val) _ v
    (⟨fun _ st' => .up (∀ hf' : st'.env.FreshFrom st'.nv,
        (Q.1 (CircuitType.fieldsToVar (F := F) (val := val)
            (mapVec CVar.var (allocRange st.nv (CircuitType.size F val))))
          ⟨st'.nv, st'.env, hf'⟩).down), Q.2⟩)
    ⟨st.nv + CircuitType.size F val, env₁, hf⟩
    ⟨hvars env₁ (Assignments.Le.refl env₁), fun u st' _ hle' => ?_⟩
  intro hf'
  refine hk _ ⟨st'.nv, st'.env, hf'⟩ (fun v' hv' => ?_) (hle₁.trans hle')
  rw [hw] at hv'
  injection hv' with hv'
  subst hv'
  exact WitnessReads.reads_of_grant (hvars st'.env hle')

/-- Split a successful read at the append boundary. -/
private theorem mapM_eval_append_ok {F : Type} [Add F] [Mul F] {env : Assignments F} :
    ∀ {l₁ : List (CVar F)} {e₁ : List F} {l₂ : List (CVar F)} {e₂ : List F},
      e₁.length = l₁.length →
      (l₁ ++ l₂).mapM (CVar.eval · env) = .ok (e₁ ++ e₂) →
      l₁.mapM (CVar.eval · env) = .ok e₁ ∧ l₂.mapM (CVar.eval · env) = .ok e₂
  | [], e₁, _, _, hlen, h => by
    have : e₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst this
    exact ⟨rfl, by simpa using h⟩
  | x :: xs, y :: e₁, l₂, e₂, hlen, h => by
    cases he : x.eval env with
    | error e => simp [List.mapM_cons, he, Bind.bind, Except.bind] at h
    | ok z =>
      cases hr : (xs ++ l₂).mapM (CVar.eval · env) with
      | error e => simp [List.mapM_cons, he, hr, Bind.bind, Except.bind] at h
      | ok zs =>
        simp only [List.cons_append, List.mapM_cons, he, hr, Bind.bind, Except.bind,
          Pure.pure, Except.pure, Except.ok.injEq, List.cons.injEq] at h
        obtain ⟨hz, hzs⟩ := h
        obtain ⟨h1, h2⟩ :=
          mapM_eval_append_ok (by simpa using hlen) (hr.trans (by rw [hzs]))
        exact ⟨by simp [List.mapM_cons, he, h1, hz, Bind.bind, Except.bind,
          Pure.pure, Except.pure], h2⟩
  | x :: xs, [], l₂, e₂, hlen, h => by simp at hlen

/-- Split a successful flattened read into its per-piece reads. -/
private theorem mapM_eval_flatten_ok {F : Type} [Add F] [Mul F] {env : Assignments F} :
    ∀ {bs : List (List (CVar F))} {es : List (List F)}, bs.length = es.length →
      (∀ p ∈ bs.zip es, p.2.length = p.1.length) →
      bs.flatten.mapM (CVar.eval · env) = .ok es.flatten →
      ∀ p ∈ bs.zip es, p.1.mapM (CVar.eval · env) = .ok p.2
  | [], [], _, _, _, _, hp => by simp at hp
  | [], _ :: _, hlen, _, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _, _ => by simp at hlen
  | b :: bs, e :: es, hlen, hplen, h, p, hp => by
    simp only [List.flatten_cons] at h
    obtain ⟨h1, h2⟩ := mapM_eval_append_ok (hplen (b, e) (by simp)) h
    rcases List.mem_cons.mp (by simpa using hp) with hhead | htail
    · rw [hhead]
      exact h1
    · exact mapM_eval_flatten_ok (by simpa using hlen)
        (fun q hq => hplen q (List.mem_cons_of_mem _ hq)) h2 p htail

open Std.Do in
instance instLawfulCheckedTypeProd {F c : Type} [Add F] [Mul F] {a b av bv : Type}
    [A : CircuitType F a av] [B : CircuitType F b bv] [CheckedType F (Prover c) av]
    [CheckedType F (Prover c) bv] [Checker F c] [LawfulCheckedType F c a av]
    [LawfulCheckedType F c b bv] :
    LawfulCheckedType F c (a × b) (av × bv) where
  check_complete bundle v Q := by
    intro st hpre
    obtain ⟨hread, hk⟩ := hpre
    have hread' : (A.varToFields bundle.1 ++ B.varToFields bundle.2).toList.mapM
          (CVar.eval · st.env)
        = .ok (A.valueToFields v.1 ++ B.valueToFields v.2).toList := hread
    simp only [Vector.toList_append] at hread'
    obtain ⟨hr1, hr2⟩ := mapM_eval_append_ok (by simp) hread'
    rw [show (CheckedType.check (c := Prover c) bundle : CircuitM F (Prover c) PUnit)
        = (CheckedType.check (c := Prover c) bundle.1 >>= fun _ =>
            CheckedType.check (c := Prover c) bundle.2) from rfl]
    simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
    refine LawfulCheckedType.check_complete (c := c) (val := a) bundle.1 v.1
      ⟨fun _ st' => (Std.Do.wp (CheckedType.check (c := Prover c) bundle.2 :
          CircuitM F (Prover c) PUnit)).apply Q st', Q.2⟩ st
      ⟨hr1, fun u st' _ hle' => ?_⟩
    exact LawfulCheckedType.check_complete (c := c) (val := b) bundle.2 v.2 Q st'
      ⟨mapM_eval_le hle' hr2,
        fun w st'' _ hle'' => hk w st'' trivial (hle'.trans hle'')⟩

open Std.Do in
/-- The element checks of a list, run in order: each element's read survives to its
own check through the table growth of the checks before it. -/
private theorem forM_check_complete {F c val var : Type} [Add F] [Mul F]
    [CircuitType F val var] [CheckedType F (Prover c) var] [Checker F c]
    [LawfulCheckedType F c val var] :
    ∀ (bs : List var) (vs : List val), bs.length = vs.length →
      ∀ (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))),
      ⦃Complete
          (fun env => ∀ p ∈ bs.zip vs,
            (CircuitType.varToFields (F := F) (val := val) p.1).toList.mapM
                (CVar.eval · env)
              = .ok (CircuitType.valueToFields (F := F) (var := var) p.2).toList)
          (fun _ _ _ => True) Q⦄
      (bs.forM (CheckedType.check (c := Prover c)) : CircuitM F (Prover c) PUnit)
      ⦃Q⦄
  | [], _, _, Q => fun st hpre => check_pure_complete (c := c) Q st hpre
  | b :: bs, [], hlen, Q => by simp at hlen
  | b :: bs, v :: vs, hlen, Q => by
    intro st hpre
    obtain ⟨hreads, hk⟩ := hpre
    rw [show ((b :: bs).forM (CheckedType.check (c := Prover c))
          : CircuitM F (Prover c) PUnit)
        = (CheckedType.check (c := Prover c) b >>= fun _ =>
            bs.forM (CheckedType.check (c := Prover c))) from rfl]
    simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
    refine LawfulCheckedType.check_complete (c := c) (val := val) b v
      ⟨fun _ st' => (Std.Do.wp (bs.forM (CheckedType.check (c := Prover c))
          : CircuitM F (Prover c) PUnit)).apply Q st', Q.2⟩ st
      ⟨hreads (b, v) (by simp), fun u st' _ hle' => ?_⟩
    refine forM_check_complete bs vs (by simpa using hlen) Q st'
      ⟨fun p hp => mapM_eval_le hle' (hreads p ?_),
        fun w st'' _ hle'' => hk w st'' trivial (hle'.trans hle'')⟩
    rw [List.zip_cons_cons]
    exact List.mem_cons_of_mem _ hp

open Std.Do in
instance instLawfulCheckedTypeVector {F c : Type} [Add F] [Mul F] {val var : Type}
    [A : CircuitType F val var] [CheckedType F (Prover c) var] [Checker F c]
    [LawfulCheckedType F c val var] {n : Nat} :
    LawfulCheckedType F c (Vector val n) (Vector var n) where
  check_complete bundle v Q := by
    intro st hpre
    obtain ⟨hread, hk⟩ := hpre
    refine forM_check_complete bundle.toList v.toList (by simp) Q st
      ⟨?_, fun u st' _ hle' => hk u st' trivial hle'⟩
    intro p hp
    have hsplit := mapM_eval_flatten_ok (env := st.env)
      (bs := bundle.toList.map fun x =>
        (CircuitType.varToFields (F := F) (val := val) x).toList)
      (es := v.toList.map fun x =>
        (CircuitType.valueToFields (F := F) (var := var) x).toList)
      (by simp) (fun q hq => by
        rw [List.zip_map] at hq
        obtain ⟨q₀, -, rfl⟩ := List.mem_map.mp hq
        simp)
      (by
        have hread' : ((bundle.map (CircuitType.varToFields (F := F)
                (val := val))).flatten).toList.mapM (CVar.eval · st.env)
            = .ok ((v.map (CircuitType.valueToFields (F := F)
                (var := var))).flatten).toList := hread
        simpa [toList_flatten, Vector.toList_map, List.map_map] using hread')
    have hmem : ((CircuitType.varToFields (F := F) (val := val) p.1).toList,
        (CircuitType.valueToFields (F := F) (var := var) p.2).toList)
        ∈ (bundle.toList.map fun x =>
            (CircuitType.varToFields (F := F) (val := val) x).toList).zip
          (v.toList.map fun x =>
            (CircuitType.valueToFields (F := F) (var := var) x).toList) := by
      rw [List.zip_map]
      exact List.mem_map_of_mem hp
    exact hsplit _ hmem

instance instWitnessReadsF {F : Type} [Add F] [Mul F] :
    WitnessReads F F (FVar F) where
  Reads r env x := r.eval env = .ok x
  reads_of_grant h := mapM_eval_singleton h
  reads_le hle h := CVar.eval_le hle h

instance instWitnessReadsBool {F : Type} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] : WitnessReads F Bool (BoolVar F) where
  Reads r env b := (↑r : CVar F).eval env = .ok (bit b)
  reads_of_grant h := mapM_eval_singleton h
  reads_le hle h := CVar.eval_le hle h

instance instWitnessReadsUnChecked {F val var : Type} [Add F] [Mul F]
    [CircuitType F val var] [WitnessReads F val var] :
    WitnessReads F (UnChecked val) (UnChecked var) where
  Reads r env v := WitnessReads.Reads (F := F) r.val env v.val
  reads_of_grant h := WitnessReads.reads_of_grant h
  reads_le hle h := WitnessReads.reads_le hle h

instance instWitnessReadsProd {F a b av bv : Type} [Add F] [Mul F]
    [A : CircuitType F a av] [B : CircuitType F b bv] [WitnessReads F a av]
    [WitnessReads F b bv] : WitnessReads F (a × b) (av × bv) where
  Reads r env v := WitnessReads.Reads (F := F) r.1 env v.1 ∧
    WitnessReads.Reads (F := F) r.2 env v.2
  reads_of_grant {r} {env} {v} h := by
    have h' : (A.varToFields r.1 ++ B.varToFields r.2).toList.mapM (CVar.eval · env)
        = .ok (A.valueToFields v.1 ++ B.valueToFields v.2).toList := h
    simp only [Vector.toList_append] at h'
    obtain ⟨h1, h2⟩ := mapM_eval_append_ok (by simp) h'
    exact ⟨WitnessReads.reads_of_grant h1, WitnessReads.reads_of_grant h2⟩
  reads_le hle h := ⟨WitnessReads.reads_le hle h.1, WitnessReads.reads_le hle h.2⟩

instance instWitnessReadsVector {F val var : Type} [Add F] [Mul F]
    [CircuitType F val var] [WitnessReads F val var] {n : Nat} :
    WitnessReads F (Vector val n) (Vector var n) where
  Reads r env v := ∀ (i : ℕ) (hi : i < n), WitnessReads.Reads (F := F) r[i] env v[i]
  reads_of_grant {r} {env} {v} h := by
    intro i hi
    refine WitnessReads.reads_of_grant ?_
    have hsplit := mapM_eval_flatten_ok (env := env)
      (bs := r.toList.map fun x =>
        (CircuitType.varToFields (F := F) (val := val) x).toList)
      (es := v.toList.map fun x =>
        (CircuitType.valueToFields (F := F) (var := var) x).toList)
      (by simp) (fun q hq => by
        rw [List.zip_map] at hq
        obtain ⟨q₀, -, rfl⟩ := List.mem_map.mp hq
        simp)
      (by
        have h' : ((r.map (CircuitType.varToFields (F := F)
                (val := val))).flatten).toList.mapM (CVar.eval · env)
            = .ok ((v.map (CircuitType.valueToFields (F := F)
                (var := var))).flatten).toList := h
        simpa [toList_flatten, Vector.toList_map, List.map_map] using h')
    have hmem : ((CircuitType.varToFields (F := F) (val := val) r[i]).toList,
        (CircuitType.valueToFields (F := F) (var := var) v[i]).toList)
        ∈ (r.toList.map fun x =>
            (CircuitType.varToFields (F := F) (val := val) x).toList).zip
          (v.toList.map fun x =>
            (CircuitType.valueToFields (F := F) (var := var) x).toList) := by
      rw [List.zip_map]
      refine List.mem_map_of_mem (a := (r[i], v[i])) ?_
      refine List.mem_iff_getElem.mpr ⟨i, by simp; omega, ?_⟩
      simp [List.getElem_zip]
    exact hsplit _ hmem
  reads_le hle h := fun i hi => WitnessReads.reads_le hle (h i hi)

/-! ## The vector loop rule

The soundness and `Complete` laws of `generateVec`, given a spec for each component —
the analogue of the framework's `Spec.forIn_list`. They cannot be `@[spec]`: the
componentwise hypothesis is the caller's to supply. -/

open Std.Do in
/-- Componentwise guarantees aggregate componentwise. No invariant beyond the
components' own facts: nothing threads. -/
theorem generateVec_spec {V : Valuation F} {α : Type} [ConstraintHolds F c] :
    ∀ (n : Nat) (f : Fin n → CircuitM F (Builder V c) α) (post : Fin n → α → Prop),
      (∀ i : Fin n, ⦃⌜True⌝⦄ f i ⦃⇓ r _ => ⌜post i r⌝⦄) →
      ⦃⌜True⌝⦄ generateVec n f ⦃⇓ rs _ => ⌜∀ i : Fin n, post i rs[i]⌝⦄ := by
  intro n
  induction n with
  | zero =>
    intro f post hf nv _ _
    exact fun i => i.elim0
  | succ n ih =>
    intro f post hf
    show ⦃⌜True⌝⦄ ((generateVec n fun i => f i.castSucc) >>= fun init =>
        f (Fin.last n) >>= fun last => pure (init.push last)) ⦃_⦄
    have hinit := ih (fun i => f i.castSucc) (fun i => post i.castSucc) (fun i => hf i.castSucc)
    have hlast := hf (Fin.last n)
    mvcgen [hinit, hlast]
    rename_i init _ hinit' last _ hlast'
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hlast'
    · simpa using hinit' j

open Std.Do in
/-- Componentwise runs chain, given that each component's `pre` and `post` transport
along table extension — the two hypotheses that replace a loop invariant, since the
prover's table grows. -/
theorem generateVec_complete_spec {F c : Type} {α : Type} [Checker F c] :
    ∀ (n : Nat) (f : Fin n → CircuitM F (Prover c) α)
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
/-- Apply a program's soundness triple at the completed final table: the satisfaction
hypothesis is what `prove_complete` establishes, and `prove_build_agrees` identifies
the two interpreters' results. -/
theorem post_of_prove {F : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {α : Type} {post : Valuation F → α → Prop} {g : CircuitM F (Basic F) α}
    (hspec : ∀ V : Valuation F,
      ⦃⌜True⌝⦄ (show CircuitM F (Builder V (Basic F)) α from g) ⦃⇓ r _ => ⌜post V r⌝⦄)
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
  have h2 : post env'.toValuation (build g nv).result :=
    hspec env'.toValuation nv trivial hsat
  have h3 := prove_build_agrees hrun
  rw [h3.1] at h2
  exact h2

end Snarky
