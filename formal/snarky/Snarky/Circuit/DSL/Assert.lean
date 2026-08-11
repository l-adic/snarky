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
`AssertEqual` class and `allBools`. Every gadget carries its two laws beside it.

Name map (underscores drop): `assertEqual_`, `assertNonZero_`, `assertNotEqual_`,
`assertSquare_`, `assert_`, `assertAny_`, `assertAll_`, `assertExactlyOne_`;
`allBools` and the class methods `assertEq`/`isEqual` keep their PS names.

Deviations from the PS original (ledger: `formal/docs/snarky-ps-alignment.md`):
- PS CRASHES at circuit construction on impossible constant assertions. The total
  rendering emits the impossible constraint instead — `assertEqual` the unsatisfiable
  `equal` row, `assertNonZero` the falsum `0 = 1` — so the prover rejects, and
  soundness treats the branch by contradiction.
- The `AssertEqual` class: fundeps unmodelled; base instances only (`FVar`, `BoolVar`,
  `PUnit`, the pair — components FIRST THEN SECOND, PS order, unlike `IfThenElse`).
- `allBools` keeps the OCaml/PS constant-FIRST argument order in its three-plus case
  (`equals (const n) (sum bs)`).

The sum-based laws carry the cast-injectivity hypothesis of `DSL/Boolean`'s sum-based
section wherever a count must be detected below the characteristic; the direction that
only needs a count to cast is hypothesis-free.
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

/-! ## The `assertEqual` laws -/

open Std.Do in
/-- `assertEqual x y` asserts that any satisfying
valuation reads the operands equal — through the fold, the unsatisfiable-constants
row, and the general row. -/
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
/-- Prover reading: on equal values the run cannot
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

/-- A two-step chain: equality is transitive through composition. -/
example [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x y z : FVar F) :
    ⦃⌜True⌝⦄
    (do assertEqual (c := c) x y
        assertEqual (c := c) y z : CircuitM F c PUnit)
    ⦃⇓ _ s => ⌜x.val s.V = z.val s.V⌝⦄ := by
  mvcgen
  intro _ _nv' hxy
  exact assertEqual_spec (c := c) y z _ _ fun _ _ hyz => hxy.trans hyz

/-- The same chain in the prover reading: on agreeing values the honest run cannot
fail. The two `@[spec]` lemmas for one head symbol coexist across the two readings;
`mvcgen` selects by the ambient monad. -/
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
witnessed inverse forces `w` to read as `v`'s field inverse. -/
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

/-! ## The `assertNonZero`, `assertNotEqual`, and `assertSquare` laws -/

open Std.Do in
/-- Asserts the operand reads nonzero — the
zero-constant branch carries an unsatisfiable row, the witnessing branch the
inverse's product row. -/
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
    (simp only [inv]
     mvcgen
     intro r _nv' hr _
     exact hpre PUnit.unit _ (left_ne_zero_of_mul_eq_one hr))

open Std.Do in
/-- The run succeeds on a
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
    (mvcgen
     refine ⟨⟨by rw [hv]; rfl, fun _ h => ?_⟩, fun _ st' _ hle => ?_⟩
     · rw [hv] at h
       injection h with h
       exact h ▸ hvv
     · exact fun _ => hk PUnit.unit st' hle)

open Std.Do in
/-- Delegated to `assertNonZero` through the
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
/-- Delegated to
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
/-- Asserts the square identity on the operands'
readings. -/
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
/-- The run succeeds on a true
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
/-- `assert v` asserts the bit reads `1`. -/
@[spec] theorem assert_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (v : BoolVar F) (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => (↑v : CVar F).val V = 1) Q⦄
    assert (c := c) v
    ⦃Q⦄ := by
  simp only [assert]
  exact assertEqual_spec (c := c) ↑v (.const 1) Q

open Std.Do in
/-- The run succeeds on a bit that
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

/-! ## The sum-based combinators (`allBools`, `assertAny`, `assertAll`,
`assertExactlyOne`)

The three-plus cases test a bit-sum, so the laws carry the cast-injectivity hypothesis
of `DSL/Boolean`'s sum-based section (`assertAny`'s soundness needs none: a zero count
casts to zero in any semiring). -/

open Std.Do in
/-- On bit operands the result is the list's
conjunction, under cast-injectivity up to the length. -/
@[spec] theorem allBools_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length + 1 → k ≤ bs.length + 1 → (j : F) = k → j = k)
    (Q : PostCond (BoolVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : BoolVar F) => ∀ bl : List Bool, ReadBits V bs bl →
        (↑r : CVar F).val V = bit (bl.all id)) Q⦄
    allBools (c := c) bs
    ⦃Q⦄ := by
  match bs, hchar with
  | [], _ =>
    simp only [allBools]
    intro s hpre _
    refine hpre true_ s.nv (fun bl hbl => ?_)
    cases hbl
    rfl
  | [a], _ =>
    simp only [allBools]
    intro s hpre _
    refine hpre a s.nv (fun bl hbl => ?_)
    obtain - | ⟨hb, hnil⟩ := hbl
    cases hnil
    simpa using hb
  | [a, b], _ =>
    simp only [allBools]
    refine fun s hpre => and_spec a b Q s (fun r nv' hr => ?_)
    refine hpre r nv' (fun bl hbl => ?_)
    obtain - | ⟨ha', htl⟩ := hbl
    obtain - | ⟨hb', hnil⟩ := htl
    cases hnil
    simpa using hr _ _ ha' hb'
  | x₁ :: x₂ :: x₃ :: t, hchar =>
    simp only [allBools]
    set bs := x₁ :: x₂ :: x₃ :: t with hbs
    refine fun s hpre => equals_spec _ _ Q s (fun r nv' hr => ?_)
    refine hpre r nv' (fun bl hbl => ?_)
    have hsum := sum_bits_val (V := s.V) hbl
    have hlen := forall₂_length hbl
    have hcount : bl.count true ≤ bs.length + 1 := by
      have := List.count_le_length (a := true) (l := bl)
      omega
    rw [hr, hsum]
    simp only [equalsPure]
    show (if (CVar.const (bs.length : F)).val s.V = (bl.count true : F) then 1 else 0) = _
    by_cases hall : bl.all id = true
    · rw [hall]
      have hc : bl.count true = bl.length := count_true_eq_length.mpr hall
      simp only [CVar.val]
      rw [if_pos (by rw [hc, hlen]), bit_true]
    · have hall' : bl.all id = false := by revert hall; cases bl.all id <;> simp
      rw [hall']
      have hc : bl.count true ≠ bl.length := fun hcc =>
        absurd (count_true_eq_length.mp hcc) (by rw [hall']; simp)
      have hne : ¬((bs.length : F) = (bl.count true : F)) := by
        intro hcast
        have := hchar _ _ (by omega) hcount hcast
        omega
      simp only [CVar.val]
      rw [if_neg hne, bit_false]

open Std.Do in
/-- The run succeeds on any
evaluable operands, and where they read as bits the result is the conjunction. -/
@[spec] theorem allBools_complete_spec {F : Type} [Field F] [DecidableEq F]
    (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length + 1 → k ≤ bs.length + 1 → (j : F) = k → j = k)
    (Q : PostCond (BoolVar F) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => ∀ b ∈ bs, (((b : BoolVar F) : CVar F).eval env).isOk)
        (fun env (r : BoolVar F) env' => ∀ bl : List Bool, EvalBits env bs bl →
          (↑r : CVar F).eval env' = .ok (bit (bl.all id))) Q⦄
    allBools (c := ProverC F) bs
    ⦃Q⦄ := by
  match bs, hchar with
  | [], _ =>
    simp only [allBools]
    intro st hpre
    obtain ⟨-, hk⟩ := hpre
    exact fun _ => hk true_ st (fun bl hbl => by cases hbl; rfl)
      (Assignments.Le.refl st.env)
  | [a], _ =>
    simp only [allBools]
    intro st hpre
    obtain ⟨-, hk⟩ := hpre
    refine fun _ => hk a st (fun bl hbl => ?_) (Assignments.Le.refl st.env)
    obtain - | ⟨hb, hnil⟩ := hbl
    cases hnil
    simpa using hb
  | [a, b], _ =>
    simp only [allBools]
    intro st hpre
    obtain ⟨hok, hk⟩ := hpre
    refine and_complete_spec a b Q st
      ⟨⟨hok a (by simp), hok b (by simp)⟩, fun r st' hr hle => ?_⟩
    refine hk r st' (fun bl hbl => ?_) hle
    obtain - | ⟨ha', htl⟩ := hbl
    obtain - | ⟨hb', hnil⟩ := htl
    cases hnil
    simpa using hr _ _ ha' hb'
  | x₁ :: x₂ :: x₃ :: t, hchar =>
    simp only [allBools]
    set bs := x₁ :: x₂ :: x₃ :: t with hbs
    intro st hpre
    obtain ⟨hok, hk⟩ := hpre
    refine equals_complete_spec _ _ Q st
      ⟨⟨by rfl, sum_evalOk hok⟩, fun r st' hr hle => ?_⟩
    refine hk r st' (fun bl hbl => ?_) hle
    have hsum := sum_bits_eval hbl
    have hlen := forall₂_length hbl
    have hcount : bl.count true ≤ bs.length + 1 := by
      have := List.count_le_length (a := true) (l := bl)
      omega
    have hr' := hr _ _ (by rfl : (CVar.const (bs.length : F)).eval st.env
      = .ok (bs.length : F)) hsum
    rw [hr']
    simp only [equalsPure]
    by_cases hall : bl.all id = true
    · rw [hall]
      have hc : bl.count true = bl.length := count_true_eq_length.mpr hall
      rw [if_pos (by rw [hc, hlen]), bit_true]
    · have hall' : bl.all id = false := by revert hall; cases bl.all id <;> simp
      rw [hall']
      have hc : bl.count true ≠ bl.length := fun hcc =>
        absurd (count_true_eq_length.mp hcc) (by rw [hall']; simp)
      have hne : ¬((bs.length : F) = (bl.count true : F)) := by
        intro hcast
        have := hchar _ _ (by omega) hcount hcast
        omega
      rw [if_neg hne, bit_false]

open Std.Do in
/-- Asserts some bit is set — no characteristic
hypothesis, since a zero count casts to zero in any semiring. -/
@[spec] theorem assertAny_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (bs : List (BoolVar F)) (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => ∀ bl : List Bool, ReadBits V bs bl →
        bl.any id = true) Q⦄
    assertAny (c := c) bs
    ⦃Q⦄ := by
  simp only [assertAny]
  refine fun s hpre => assertNonZero_spec _ Q s (fun u nv' hne => ?_)
  dsimp only at hne
  refine hpre u nv' (fun bl hbl => ?_)
  have hsum := sum_bits_val (V := s.V) hbl
  rw [hsum] at hne
  by_contra hany
  have hany' : bl.any id = false := by revert hany; cases bl.any id <;> simp
  rw [count_true_eq_zero.mpr hany'] at hne
  exact hne (by simp)

open Std.Do in
/-- On bit operands with some
bit set the run succeeds — cast-injectivity makes the nonzero count a nonzero sum. -/
@[spec] theorem assertAny_complete_spec {F : Type} [Field F] [DecidableEq F]
    (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length + 1 → k ≤ bs.length + 1 → (j : F) = k → j = k)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (∀ b ∈ bs, ReadsBit ((b : BoolVar F) : CVar F) env) ∧
        ∀ bl : List Bool, EvalBits env bs bl → bl.any id = true)
        (fun _ _ _ => True) Q⦄
    assertAny (c := ProverC F) bs
    ⦃Q⦄ := by
  simp only [assertAny]
  intro st hpre
  obtain ⟨⟨hbits, hany⟩, hk⟩ := hpre
  obtain ⟨bl, hbl⟩ := exists_evalBits hbits
  have hsum := sum_bits_eval hbl
  have hlen := forall₂_length hbl
  have hcount : bl.count true ≤ bs.length + 1 := by
    have := List.count_le_length (a := true) (l := bl)
    omega
  have hne : bl.count true ≠ 0 := by
    intro h0
    have := hany bl hbl
    rw [count_true_eq_zero.mp h0] at this
    cases this
  refine assertNonZero_complete_spec _ Q st
    ⟨⟨by rw [hsum]; rfl, fun sv hsv => ?_⟩, hk⟩
  rw [hsum] at hsv
  injection hsv with hsv
  subst hsv
  intro hcast
  exact hne (hchar _ 0 hcount (by omega) (by simpa using hcast))

open Std.Do in
/-- Asserts every bit is set, under cast-injectivity
up to the length. -/
@[spec] theorem assertAll_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length + 1 → k ≤ bs.length + 1 → (j : F) = k → j = k)
    (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => ∀ bl : List Bool, ReadBits V bs bl →
        bl.all id = true) Q⦄
    assertAll (c := c) bs
    ⦃Q⦄ := by
  simp only [assertAll]
  refine fun s hpre => assertEqual_spec _ _ Q s (fun u nv' heq => ?_)
  dsimp only at heq
  refine hpre u nv' (fun bl hbl => ?_)
  have hsum := sum_bits_val (V := s.V) hbl
  have hlen := forall₂_length hbl
  have hcount : bl.count true ≤ bs.length + 1 := by
    have := List.count_le_length (a := true) (l := bl)
    omega
  rw [hsum] at heq
  have hconst : (CVar.const (bs.length : F)).val s.V = ((bs.length : Nat) : F) := rfl
  rw [hconst] at heq
  have := hchar _ _ hcount (by omega) heq
  exact count_true_eq_length.mp (by omega)

open Std.Do in
/-- On bit operands, all set,
the run succeeds — no characteristic hypothesis, the full count casts to the length
in any semiring. -/
@[spec] theorem assertAll_complete_spec {F : Type} [Field F] [DecidableEq F]
    (bs : List (BoolVar F))
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (∀ b ∈ bs, ReadsBit ((b : BoolVar F) : CVar F) env) ∧
        ∀ bl : List Bool, EvalBits env bs bl → bl.all id = true)
        (fun _ _ _ => True) Q⦄
    assertAll (c := ProverC F) bs
    ⦃Q⦄ := by
  simp only [assertAll]
  intro st hpre
  obtain ⟨⟨hbits, hall⟩, hk⟩ := hpre
  obtain ⟨bl, hbl⟩ := exists_evalBits hbits
  have hsum := sum_bits_eval hbl
  have hlen := forall₂_length hbl
  have hc : bl.count true = bl.length := count_true_eq_length.mpr (hall bl hbl)
  refine assertEqual_complete_spec _ _ Q st
    ⟨⟨by rw [hsum]; rfl, by rfl, fun xv yv hx hy => ?_⟩, hk⟩
  rw [hsum] at hx
  injection hx with hx
  injection hy with hy
  subst hx
  subst hy
  rw [hc, hlen]

open Std.Do in
/-- Asserts a one-hot list — the count is one,
under cast-injectivity up to the length plus one. -/
@[spec] theorem assertExactlyOne_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length + 1 → k ≤ bs.length + 1 → (j : F) = k → j = k)
    (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => ∀ bl : List Bool, ReadBits V bs bl →
        bl.count true = 1) Q⦄
    assertExactlyOne (c := c) bs
    ⦃Q⦄ := by
  simp only [assertExactlyOne]
  refine fun s hpre => assertEqual_spec _ _ Q s (fun u nv' heq => ?_)
  dsimp only at heq
  refine hpre u nv' (fun bl hbl => ?_)
  have hsum := sum_bits_val (V := s.V) hbl
  have hlen := forall₂_length hbl
  have hcount : bl.count true ≤ bs.length + 1 := by
    have := List.count_le_length (a := true) (l := bl)
    omega
  rw [hsum] at heq
  have hconst : (CVar.const (1 : F)).val s.V = ((1 : Nat) : F) := by
    simp [CVar.val]
  rw [hconst] at heq
  exact hchar _ _ hcount (by omega) heq

open Std.Do in
/-- On a one-hot bit list
the run succeeds — the unit count casts to one in any semiring. -/
@[spec] theorem assertExactlyOne_complete_spec {F : Type} [Field F] [DecidableEq F]
    (bs : List (BoolVar F))
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (∀ b ∈ bs, ReadsBit ((b : BoolVar F) : CVar F) env) ∧
        ∀ bl : List Bool, EvalBits env bs bl → bl.count true = 1)
        (fun _ _ _ => True) Q⦄
    assertExactlyOne (c := ProverC F) bs
    ⦃Q⦄ := by
  simp only [assertExactlyOne]
  intro st hpre
  obtain ⟨⟨hbits, hone⟩, hk⟩ := hpre
  obtain ⟨bl, hbl⟩ := exists_evalBits hbits
  have hsum := sum_bits_eval hbl
  have hc : bl.count true = 1 := hone bl hbl
  refine assertEqual_complete_spec _ _ Q st
    ⟨⟨by rw [hsum]; rfl, by rfl, fun xv yv hx hy => ?_⟩, hk⟩
  rw [hsum] at hx
  injection hx with hx
  injection hy with hy
  subst hx
  subst hy
  rw [hc]
  simp

end Snarky
