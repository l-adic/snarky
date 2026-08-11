import Snarky.Circuit.DSL.Boolean
import Snarky.Backend.WP

-- `mvcgen` is experimental; this option is its acknowledged-use switch (see the
-- `Backend/WP` module docstring for the adoption rationale).
set_option mvcgen.warning false

/-!
# Assertion gadgets

Port of `Snarky.Circuit.DSL.Assert` (packages/snarky/src/Snarky/Circuit/DSL/Assert.purs):
constraints enforced without returning values — equality, non-zeroness (an inverse
witness, which is what fails on zero), squares, boolean assertions — plus the generic
`AssertEqual` class and `allBools`.

Name map (D7; underscores drop): `assertEqual_` → `assertEqual`, `assertNonZero_` →
`assertNonZero`, `assertNotEqual_` → `assertNotEqual`, `assertSquare_` → `assertSquare`,
`assert_` → `assert`, `assertAny_`/`assertAll_`/`assertExactlyOne_` drop likewise,
`allBools` keeps its PS name; the class method `assertEq` keeps its PS name — the barrel's
transitional `assertEq` is subsumed by the class (`FVar` call sites are unchanged).

Deviations from the PS original (per `formal/docs/snarky-ps-alignment.md`):
- PS CRASHES at circuit construction on impossible constant assertions (`unsafeThrow` on
  unequal constants in `assertEqual_`; on the constant zero through `inv_` in
  `assertNonZero_`). The total rendering emits the impossible constraint instead —
  `assertEqual` emits the unsatisfiable `equal` row verbatim, `assertNonZero` the
  canonical falsum `0 = 1` — so the prover rejects, and soundness treats the branch by
  contradiction.
- The `AssertEqual` class: fundeps unmodelled (house precedent); base instances only
  (`FVar`, `BoolVar`, `PUnit`, the pair — components FIRST THEN SECOND, PS order, unlike
  `IfThenElse`); the `Vector`/`Record` instances and the `GAssertEqual`/`RAssertEqual`
  deriving machinery land with their first consumers (D8; monadic vector traversal needs
  a kernel-reducible helper in `Snarky/Vec.lean` first).
- `allBools` keeps the OCaml/PS constant-FIRST argument order in its three-plus case
  (`equals (const n) (sum bs)`) — the order matters for the constraint's coefficient
  signs downstream.

D9 survey (the `snarky-test-utils` Assert spec), in the D12 form, laws beside their
gadgets: the `assertNonZero`/`assertEqual`/`assertNotEqual`/`assertSquare` rows land as
the `_sound`/`_complete` pairs below (`assert` gets its pair too — it is the workhorse
that pins a verifier's output bit). The sum-based `assertAny`/`assertAll`/
`assertExactlyOne` and `allBools`'s three-plus case share `any`/`all`'s standing
characteristic obligation (a sum of `n` bits detects `n` only below the characteristic)
and defer with it. Assertions allocate nothing (except `assertNonZero`'s inverse
witness), so their completeness laws are exact run equations, not existentials.

Public results: the triple laws, all `@[spec]` — `assertEqual`, `assertNonZero`,
`assertNotEqual`, `assertSquare`, and `assert`, each as `*_spec` (soundness, generic
over any lawful backend) and `*_complete_spec` (prover reading) — all `roots.txt`
entries.
-/

namespace Snarky

variable {F c : Type u}

/-! ## The gadgets -/

/-- Assert equality (PS `assertEqual_`): equal constants fold to nothing; unequal
constants emit the unsatisfiable `equal` row (PS crashes at construction instead);
otherwise one `equal` constraint. -/
def assertEqual [DecidableEq F] [BasicSystem F c] (x y : FVar F) : CircuitM F c PUnit :=
  match x, y with
  | .const f, .const g =>
    if f = g then pure PUnit.unit else addConstraint (BasicSystem.equal x y)
  | _, _ => addConstraint (BasicSystem.equal x y)

/-- Assert non-zeroness by witnessing the inverse (PS `assertNonZero_ = void ∘ inv_`):
a nonzero constant folds to nothing; the constant zero emits the canonical falsum
`0 = 1` (PS crashes at construction instead). -/
def assertNonZero [Field F] [DecidableEq F] [BasicSystem F c] (v : FVar F) :
    CircuitM F c PUnit :=
  match v with
  | .const f =>
    if f = 0 then addConstraint (BasicSystem.equal (.const 0 : CVar F) (.const 1))
    else pure PUnit.unit
  | _ => do
    let _ ← inv v
    pure PUnit.unit

/-- Assert inequality: the difference is nonzero (PS `assertNotEqual_`). -/
def assertNotEqual [Field F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) :
    CircuitM F c PUnit :=
  assertNonZero (CVar.sub_ x y)

/-- Assert a square identity `x · x = y` with one dedicated constraint
(PS `assertSquare_`). -/
def assertSquare [BasicSystem F c] (x y : FVar F) : CircuitM F c PUnit :=
  addConstraint (BasicSystem.square x y)

/-- Assert a boolean holds: its bit equals `1` (PS `assert_`). -/
def assert [One F] [DecidableEq F] [BasicSystem F c] (v : BoolVar F) :
    CircuitM F c PUnit :=
  assertEqual ↑v (.const 1)

/-- Assert at least one bit is set: the bit-sum is nonzero (PS `assertAny_`, OCaml
`Boolean.Assert.any` — no two-element special case). -/
def assertAny [Field F] [DecidableEq F] [BasicSystem F c] (bs : List (BoolVar F)) :
    CircuitM F c PUnit :=
  assertNonZero (sum (bs.map BoolVar.toCVar))

/-- Assert exactly one bit is set: the bit-sum equals `1` (PS `assertExactlyOne_`,
OCaml `Boolean.Assert.exactly_one` — the one-hot validator). -/
def assertExactlyOne [Field F] [DecidableEq F] [BasicSystem F c]
    (bs : List (BoolVar F)) : CircuitM F c PUnit :=
  assertEqual (sum (bs.map BoolVar.toCVar)) (.const 1)

/-- Assert every bit is set: the bit-sum equals the length (PS `assertAll_`, OCaml
`Boolean.Assert.all`). -/
def assertAll [Field F] [DecidableEq F] [BasicSystem F c] (bs : List (BoolVar F)) :
    CircuitM F c PUnit :=
  assertEqual (sum (bs.map BoolVar.toCVar)) (.const (bs.length : F))

/-- AND a list of bits, `sum`-based beyond two elements (PS `allBools`, OCaml
`Boolean.all`): empty is true, a singleton is itself, a pair is `and`, and three or
more test the bit-sum against the length — constant FIRST, whose coefficient signs the
OCaml constraint depends on. -/
def allBools {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]
    (bs : List (BoolVar F)) : CircuitM F c (BoolVar F) :=
  match bs with
  | [] => pure true_
  | [b] => pure b
  | [b₁, b₂] => Snarky.and b₁ b₂
  | _ => equals (.const (bs.length : F)) (sum (bs.map BoolVar.toCVar))

/-! ## The `AssertEqual` class -/

/-- Generic equality assertion and test over variable bundles (PS `AssertEqual`;
fundeps unmodelled, the house precedent). -/
class AssertEqual (F c : Type) (var : Type) where
  /-- Assert componentwise equality (PS `assertEq`). -/
  assertEq : var → var → CircuitM F c PUnit
  /-- Test componentwise equality (PS `isEqual`). -/
  isEqual : var → var → CircuitM F c (BoolVar F)

export AssertEqual (assertEq isEqual)

/-- Field variables assert with `assertEqual` and test with `equals`. -/
instance {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] :
    AssertEqual F c (FVar F) where
  assertEq := assertEqual
  isEqual := equals

/-- Boolean variables assert and test through their field expressions (PS coerces). -/
instance {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] :
    AssertEqual F c (BoolVar F) where
  assertEq x y := assertEqual ↑x ↑y
  isEqual x y := equals ↑x ↑y

/-- Nothing to compare (PS `Unit` instance). -/
instance {F c : Type} [One F] : AssertEqual F c PUnit where
  assertEq _ _ := pure PUnit.unit
  isEqual _ _ := pure true_

/-- Pairs compare componentwise, first component THEN second — PS order (unlike
`IfThenElse`, which reverses). -/
instance {F c : Type} {a b : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [BasicSystem F c] [AssertEqual F c a] [AssertEqual F c b] :
    AssertEqual F c (a × b) where
  assertEq p q := do
    assertEq p.1 q.1
    assertEq p.2 q.2
  isEqual p q := do
    let r₁ ← isEqual p.1 q.1
    let r₂ ← isEqual p.2 q.2
    Snarky.and r₁ r₂

/-! ## The `assertEqual` laws (D12)

The soundness law is a Hoare triple in the `Backend/WP` interpretation, generic over
any lawful backend — the `Basic` form is its instance, and richer backends inherit it
by exhibiting `LawfulBasicSystem`. The completeness side keeps its exact `prove`
equation below, with a triple corollary in the prover reading; both specs are
`@[spec]`, so `mvcgen` consumes them at call sites (the two `example`s). -/

open Std.Do in
/-- **`assertEqual` soundness** (D12): `assertEqual x y` asserts that any satisfying
valuation reads the operands equal — through the fold, the unsatisfiable-constants
row, and the general row. Generic over any lawful backend. -/
@[spec] theorem assertEqual_spec {F c : Type} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x y : FVar F) (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => x.val V = y.val V) Q⦄
    assertEqual (c := c) x y
    ⦃Q⦄ := by
  intro s hpre
  obtain ⟨V, nv⟩ := s
  cases x <;> cases y <;> simp only [assertEqual] <;>
    first
    | (rename_i f g
       split_ifs with hfg
       · intro _
         exact hpre PUnit.unit _ hfg
       · intro hsat
         exact hpre PUnit.unit _
           (LawfulBasicSystem.holds_equal V _ _ (hsat _ (List.mem_cons_self ..))))
    | (intro hsat
       exact hpre PUnit.unit _
         (LawfulBasicSystem.holds_equal V _ _ (hsat _ (List.mem_cons_self ..))))

open Std.Do in
/-- **`assertEqual` completeness, prover reading**: on equal values the run cannot
fail — it changes nothing, so the postcondition is claimed at the incoming state.
Schematic like the soundness spec; the exact equation above supplies the reduction. -/
@[spec] theorem assertEqual_complete_spec {F : Type} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] (x y : FVar F)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (x.eval env).isOk ∧ (y.eval env).isOk ∧
          ∀ xv yv, x.eval env = .ok xv → y.eval env = .ok yv → xv = yv) (fun _ _ _ => True) Q⦄
    assertEqual (c := ProverC F) x y
    ⦃Q⦄ := by
  intro st hpre
  rw [show (assertEqual (c := ProverC F) x y : CircuitM F (ProverC F) _)
      = (assertEqual (c := Basic F) x y : CircuitM F (Basic F) _) from rfl]
  obtain ⟨⟨hokx, hoky, heq⟩, hk⟩ := hpre
  obtain ⟨xv, hx⟩ := CVar.evalOk hokx
  obtain ⟨yv, hy⟩ := CVar.evalOk hoky
  have hxy := heq xv yv hx hy
  have hQ := hk PUnit.unit st trivial (Assignments.Le.refl st.env)
  have hch : (BasicSystem.equal (c := Basic F) x y).holds st.env = true := by
    show (Basic.equal x y).holds st.env = true
    simp [Basic.holds, hx, hy, hxy]
  cases x <;> cases y <;> simp only [assertEqual] <;>
    first
    | (rename_i f g
       split_ifs with hfg
       · exact fun _ => hQ
       · simp only [addConstraint, wp, PredTrans.apply, prove, hch, if_true]
         exact fun _ => hQ)
    | (simp only [addConstraint, wp, PredTrans.apply, prove, hch, if_true]
       exact fun _ => hQ)

section MvcgenDemos

open Std.Do

variable {F c : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]

/-- `mvcgen` walks a two-step chain, consuming `assertEqual_spec` at both call
sites: equality is transitive through composition, at any lawful backend. -/
example [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x y z : FVar F) :
    ⦃⌜True⌝⦄
    (do assertEqual (c := c) x y
        assertEqual (c := c) y z : CircuitM F c PUnit)
    ⦃⇓ _ s => ⌜x.val s.V = z.val s.V⌝⦄ := by
  mvcgen
  intro _ _nv' hxy
  exact assertEqual_spec (c := c) y z _ _ fun _ _ hyz => hxy.trans hyz

/-- The SAME chain in the prover reading: on agreeing values the honest run cannot
fail — the two `@[spec]` lemmas for one head symbol coexist across the two
readings, and `mvcgen` selects by the ambient monad. -/
example (x y z : FVar F) (xv yv zv : F) :
    ⦃fun st => ⌜x.eval st.env = Except.ok xv ∧ y.eval st.env = Except.ok yv ∧
        z.eval st.env = Except.ok zv ∧ xv = yv ∧ yv = zv⌝⦄
    (do assertEqual (c := ProverC F) x y
        assertEqual (c := ProverC F) y z)
    ⦃PostCond.noThrow fun _ _st => ⌜True⌝⦄ := by
  mvcgen
  rename_i h
  obtain ⟨hx, hy, hz, hxy, hyz⟩ := h
  subst hxy
  subst hyz
  refine ⟨⟨by rw [hx]; rfl, by rw [hy]; rfl, fun a b ha hb => ?_⟩,
    fun _ st' hle => ?_⟩
  · rw [hx] at ha; rw [hy] at hb
    injection ha with ha; injection hb with hb
    rw [← ha, ← hb]
  · refine assertEqual_complete_spec y z _ st'
      ⟨⟨by rw [CVar.eval_le hle hy]; rfl, by rw [CVar.eval_le hle hz]; rfl,
        fun a b ha hb => ?_⟩, fun _ _ _ _ => trivial⟩
    rw [CVar.eval_le hle hy] at ha; rw [CVar.eval_le hle hz] at hb
    injection ha with ha; injection hb with hb
    rw [← ha, ← hb]

end MvcgenDemos

section MvcgenDemosField

open Std.Do

variable {F c : Type} [Field F] [DecidableEq F]

/-- A compute–assert chain with a mathematical postcondition: pinning `w` to the
witnessed inverse forces `w` to read as `v`'s field inverse — one `mvcgen` walk
consumes a compute spec (`inv_spec`) and an assert spec (`assertEqual_spec`). -/
example [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (v w : FVar F) :
    ⦃⌜True⌝⦄
    (do let r ← inv (c := c) v
        assertEqual (c := c) r w : CircuitM F c PUnit)
    ⦃⇓ _ s => ⌜w.val s.V = (v.val s.V)⁻¹⌝⦄ := by
  mvcgen
  intro r _nv' hr
  refine assertEqual_spec (c := c) r w _ _ fun _ _ heq => ?_
  show w.val _ = _
  exact heq ▸ hr

end MvcgenDemosField

/-! ## The `assertNonZero`, `assertNotEqual`, and `assertSquare` laws (D12) -/

open Std.Do in
/-- **`assertNonZero` soundness** (D12): asserts the operand reads nonzero — the
zero-constant branch carries an unsatisfiable row, the witnessing branch the
inverse's product row. Generic over any lawful backend. -/
@[spec] theorem assertNonZero_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (v : FVar F) (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => v.val V ≠ 0) Q⦄
    assertNonZero (c := c) v
    ⦃Q⦄ := by
  intro s hpre
  obtain ⟨V, nv⟩ := s
  cases v <;> simp only [assertNonZero]
  case const f =>
    split_ifs with h0
    · intro hsat
      exact absurd
        (LawfulBasicSystem.holds_equal V _ _ (hsat _ (List.mem_cons_self ..)))
        zero_ne_one
    · intro _
      exact hpre PUnit.unit _ h0
  all_goals
    (intro hsat
     rw [build_bind] at hsat
     have h := LawfulBasicSystem.holds_r1cs V _ _ _
       (hsat _ (List.mem_append_left _ (List.mem_cons_self ..)))
     exact hpre PUnit.unit _ (left_ne_zero_of_mul_eq_one (by simpa using h)))

open Std.Do in
/-- **`assertNonZero` completeness** (D12, prover reading): the run succeeds on a
nonzero value, extending the table with the witnessed inverse. -/
@[spec] theorem assertNonZero_complete_spec {F : Type} [Field F] [DecidableEq F]
    (v : FVar F)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (v.eval env).isOk ∧
        ∀ vv, v.eval env = .ok vv → vv ≠ 0)
        (fun _ _ _ => True) Q⦄
    assertNonZero (c := ProverC F) v
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨⟨hokv, hne⟩, hk⟩ := hpre
  obtain ⟨vv, hv⟩ := CVar.evalOk hokv
  have hvv := hne vv hv
  cases v <;> simp only [assertNonZero]
  case const f =>
    have hf : f = vv := by simpa [CVar.eval] using hv
    rw [if_neg (by rw [hf]; exact hvv)]
    exact fun _ => hk PUnit.unit st trivial (Assignments.Le.refl st.env)
  all_goals
    (simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
     refine inv_complete_spec _ _ st ⟨⟨by rw [hv]; rfl, fun _ h => ?_⟩,
       fun _ st' _ hle => ?_⟩
     · rw [hv] at h
       injection h with h
       exact h ▸ hvv
     · simp only [wp, PredTrans.apply, prove]
       intro hf
       exact hk PUnit.unit ⟨st'.nv, st'.env, hf⟩ trivial hle)

open Std.Do in
/-- **`assertNotEqual` soundness** (D12), delegated to `assertNonZero` through the
difference. -/
@[spec] theorem assertNotEqual_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x y : FVar F) (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => x.val V ≠ y.val V) Q⦄
    assertNotEqual (c := c) x y
    ⦃Q⦄ := by
  intro s hpre
  obtain ⟨V, nv⟩ := s
  refine assertNonZero_spec (c := c) _ Q ⟨V, nv⟩ ?_
  intro _ _ hne
  exact hpre PUnit.unit _ (by rwa [CVar.val_sub_, sub_ne_zero] at hne)

open Std.Do in
/-- **`assertNotEqual` completeness** (D12, prover reading), delegated to
`assertNonZero` through the difference. -/
@[spec] theorem assertNotEqual_complete_spec {F : Type} [Field F] [DecidableEq F]
    (x y : FVar F)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (x.eval env).isOk ∧ (y.eval env).isOk ∧
        ∀ xv yv, x.eval env = .ok xv → y.eval env = .ok yv → xv ≠ yv)
        (fun _ _ _ => True) Q⦄
    assertNotEqual (c := ProverC F) x y
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨⟨hokx, hoky, hne⟩, hk⟩ := hpre
  obtain ⟨xv, hx⟩ := CVar.evalOk hokx
  obtain ⟨yv, hy⟩ := CVar.evalOk hoky
  refine assertNonZero_complete_spec (CVar.sub_ x y) Q st
    ⟨⟨by rw [CVar.eval_sub_ hx hy]; rfl, fun d hd => ?_⟩, hk⟩
  rw [CVar.eval_sub_ hx hy] at hd
  injection hd with hd
  exact hd ▸ sub_ne_zero.mpr (hne xv yv hx hy)

open Std.Do in
/-- **`assertSquare` soundness** (D12): asserts the square identity on the operands'
readings. Generic over any lawful backend. -/
@[spec] theorem assertSquare_spec {F c : Type} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x y : FVar F) (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => x.val V * x.val V = y.val V) Q⦄
    assertSquare (c := c) x y
    ⦃Q⦄ := by
  intro s hpre hsat
  obtain ⟨V, nv⟩ := s
  exact hpre PUnit.unit _
    (LawfulBasicSystem.holds_square V _ _ (hsat _ (List.mem_cons_self ..)))

open Std.Do in
/-- **`assertSquare` completeness** (D12, prover reading): the run succeeds on a true
square, changing nothing. -/
@[spec] theorem assertSquare_complete_spec {F : Type} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] (x y : FVar F)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (x.eval env).isOk ∧ (y.eval env).isOk ∧
        ∀ xv yv, x.eval env = .ok xv → y.eval env = .ok yv → xv * xv = yv)
        (fun _ _ _ => True) Q⦄
    assertSquare (c := ProverC F) x y
    ⦃Q⦄ := by
  intro st hpre
  rw [show (assertSquare (c := ProverC F) x y : CircuitM F (ProverC F) _)
      = (assertSquare (c := Basic F) x y : CircuitM F (Basic F) _) from rfl]
  obtain ⟨⟨hokx, hoky, hsq'⟩, hk⟩ := hpre
  obtain ⟨xv, hx⟩ := CVar.evalOk hokx
  obtain ⟨yv, hy⟩ := CVar.evalOk hoky
  have hsq := hsq' xv yv hx hy
  have hch : (BasicSystem.square (c := Basic F) x y).holds st.env = true := by
    show (Basic.square x y).holds st.env = true
    simp [Basic.holds, hx, hy, hsq]
  simp [assertSquare, addConstraint, wp, PredTrans.apply, prove, hch]
  exact fun _ => hk PUnit.unit st trivial (Assignments.Le.refl st.env)

open Std.Do in
/-- **`assert` soundness** (D12): `assert v` asserts the bit reads `1`. -/
@[spec] theorem assert_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (v : BoolVar F) (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => (↑v : CVar F).val V = 1) Q⦄
    assert (c := c) v
    ⦃Q⦄ := by
  simp only [assert]
  exact assertEqual_spec (c := c) ↑v (.const 1) Q

open Std.Do in
/-- **`assert` completeness** (D12, prover reading): the run succeeds on a bit that
reads `1`. -/
@[spec] theorem assert_complete_spec {F : Type} [Field F] [DecidableEq F]
    (v : BoolVar F)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => ((↑v : CVar F).eval env).isOk ∧
        ∀ bv, (↑v : CVar F).eval env = .ok bv → bv = 1)
        (fun _ _ _ => True) Q⦄
    assert (c := ProverC F) v
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨⟨hokv, hone⟩, hk⟩ := hpre
  obtain ⟨bv, hv⟩ := CVar.evalOk hokv
  refine assertEqual_complete_spec ↑v (.const 1) Q st
    ⟨⟨by rw [hv]; rfl, by rfl, fun a b ha hb => ?_⟩, hk⟩
  rw [hv] at ha
  injection ha with ha
  injection hb with hb
  rw [← ha, ← hb]
  exact hone bv hv

end Snarky
