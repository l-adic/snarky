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
/-- `assertEqual x y` asserts that any satisfying valuation reads the operands equal —
through the fold, the unsatisfiable-constants row, and the general row. -/
@[spec] theorem assertEqual_spec {F c : Type} {V : Valuation F} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x y : FVar F) :
    ⦃⌜True⌝⦄
    assertEqual (c := Builder V c) x y
    ⦃⇓ _ _ => ⌜x.val V = y.val V⌝⦄ := by
  intro nv _
  cases x <;> cases y <;> simp only [assertEqual] <;>
    first
    | (rename_i f g
       split_ifs with hfg
       · intro _
         exact hfg
       · intro hsat
         exact (LawfulBasicSystem.holds_equal V _ _ (hsat _ (List.mem_cons_self ..))))
    | (intro hsat
       exact (LawfulBasicSystem.holds_equal V _ _ (hsat _ (List.mem_cons_self ..))))

open Std.Do in
/-- `assertEqual`'s honest run cannot fail on operands reading equal — it changes
nothing, so the postcondition is claimed at the incoming state. -/
@[spec] theorem assertEqual_complete_spec {F c : Type} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] [BasicSystem F c] [Checker F c] [LawfulChecker F c] (x y : FVar F)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (x.eval env).isOk ∧ (y.eval env).isOk ∧
          ∀ xv yv, x.eval env = .ok xv → y.eval env = .ok yv → xv = yv) (fun _ _ _ => True) Q⦄
    assertEqual (c := Prover c) x y
    ⦃Q⦄ := by
  intro st hpre
  rw [show (assertEqual (c := Prover c) x y : CircuitM F (Prover c) _)
      = (assertEqual (c := c) x y : CircuitM F c _) from rfl]
  obtain ⟨⟨hokx, hoky, heq⟩, hk⟩ := hpre
  obtain ⟨xv, hx⟩ := CVar.evalOk hokx
  obtain ⟨yv, hy⟩ := CVar.evalOk hoky
  have hxy := heq xv yv hx hy
  have hQ := hk PUnit.unit st trivial (Assignments.Le.refl st.env)
  have hch : Checker.holds (F := F) (c := c)
      (BasicSystem.equal (c := c) x y) st.env = true :=
    LawfulChecker.check_equal _ _ _ _ hx (hxy ▸ hy)
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
    (V : Valuation F) (x y z : FVar F) :
    ⦃⌜True⌝⦄
    (do assertEqual (c := Builder V c) x y
        assertEqual (c := Builder V c) y z : CircuitM F (Builder V c) PUnit)
    ⦃⇓ _ _ => ⌜x.val V = z.val V⌝⦄ := by
  mvcgen
  rename_i hxy _ _
  intro hyz
  exact hxy.trans hyz

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
    (V : Valuation F) (v w : FVar F) :
    ⦃⌜True⌝⦄
    (do let r ← inv (c := Builder V c) v
        assertEqual (c := Builder V c) r w : CircuitM F (Builder V c) PUnit)
    ⦃⇓ _ _ => ⌜w.val V = (v.val V)⁻¹⌝⦄ := by
  mvcgen
  rename_i r _ hr _ _
  intro heq
  rw [← heq]
  exact hr

end MvcgenDemosField

/-! ## The `assertNonZero`, `assertNotEqual`, and `assertSquare` laws -/

open Std.Do in
/-- `assertNonZero` asserts the operand reads nonzero — the zero-constant branch
carries an unsatisfiable row, the witnessing branch the inverse's product row. -/
@[spec] theorem assertNonZero_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (v : FVar F) :
    ⦃⌜True⌝⦄
    assertNonZero (c := Builder V c) v
    ⦃⇓ _ _ => ⌜v.val V ≠ 0⌝⦄ := by
  intro nv _
  cases v <;> simp only [assertNonZero]
  case const f =>
    split_ifs with h0
    · intro hsat
      exact absurd
        (LawfulBasicSystem.holds_equal V _ _ (hsat _ (List.mem_cons_self ..)))
        zero_ne_one
    · intro _
      exact h0
  all_goals
    (simp only [inv]
     mvcgen
     rename_i r _ hr
     exact left_ne_zero_of_mul_eq_one hr)

open Std.Do in
/-- `assertNonZero`'s honest run succeeds on a nonzero value, extending the table with
the witnessed inverse. -/
@[spec] theorem assertNonZero_complete_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c]
    (v : FVar F)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (v.eval env).isOk ∧
        ∀ vv, v.eval env = .ok vv → vv ≠ 0)
        (fun _ _ _ => True) Q⦄
    assertNonZero (c := Prover c) v
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
/-- `assertNotEqual` asserts the operands read unequal — delegated to `assertNonZero`
on the difference. -/
@[spec] theorem assertNotEqual_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x y : FVar F) :
    ⦃⌜True⌝⦄
    assertNotEqual (c := Builder V c) x y
    ⦃⇓ _ _ => ⌜x.val V ≠ y.val V⌝⦄ := by
  simp only [assertNotEqual]
  mvcgen
  intro hne
  rwa [CVar.val_sub_, sub_ne_zero] at hne

open Std.Do in
/-- `assertNotEqual`'s honest run succeeds on operands reading unequal —
`assertNonZero`'s law applied at the difference. -/
@[spec] theorem assertNotEqual_complete_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c]
    (x y : FVar F)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (x.eval env).isOk ∧ (y.eval env).isOk ∧
        ∀ xv yv, x.eval env = .ok xv → y.eval env = .ok yv → xv ≠ yv)
        (fun _ _ _ => True) Q⦄
    assertNotEqual (c := Prover c) x y
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
/-- `assertSquare x y` asserts `x · x = y` on the operands' readings. -/
@[spec] theorem assertSquare_spec {F c : Type} {V : Valuation F} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x y : FVar F) :
    ⦃⌜True⌝⦄
    assertSquare (c := Builder V c) x y
    ⦃⇓ _ _ => ⌜x.val V * x.val V = y.val V⌝⦄ := by
  intro nv _ hsat
  exact (LawfulBasicSystem.holds_square V _ _ (hsat _ (List.mem_cons_self ..)))

open Std.Do in
/-- `assertSquare`'s honest run succeeds on a true square, changing nothing. -/
@[spec] theorem assertSquare_complete_spec {F c : Type} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] [BasicSystem F c] [Checker F c] [LawfulChecker F c] (x y : FVar F)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (x.eval env).isOk ∧ (y.eval env).isOk ∧
        ∀ xv yv, x.eval env = .ok xv → y.eval env = .ok yv → xv * xv = yv)
        (fun _ _ _ => True) Q⦄
    assertSquare (c := Prover c) x y
    ⦃Q⦄ := by
  intro st hpre
  rw [show (assertSquare (c := Prover c) x y : CircuitM F (Prover c) _)
      = (assertSquare (c := c) x y : CircuitM F c _) from rfl]
  obtain ⟨⟨hokx, hoky, hsq'⟩, hk⟩ := hpre
  obtain ⟨xv, hx⟩ := CVar.evalOk hokx
  obtain ⟨yv, hy⟩ := CVar.evalOk hoky
  have hsq := hsq' xv yv hx hy
  have hch : Checker.holds (F := F) (c := c)
      (BasicSystem.square (c := c) x y) st.env = true :=
    LawfulChecker.check_square _ _ _ _ _ hx hy hsq
  simp [assertSquare, addConstraint, wp, PredTrans.apply, prove, hch]
  exact fun _ => hk PUnit.unit st trivial (Assignments.Le.refl st.env)

open Std.Do in
/-- `assert v` asserts the bit reads `1`. -/
@[spec] theorem assert_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (v : BoolVar F) :
    ⦃⌜True⌝⦄
    assert (c := Builder V c) v
    ⦃⇓ _ _ => ⌜(↑v : CVar F).val V = 1⌝⦄ := by
  simp only [assert]
  mvcgen

open Std.Do in
/-- `assert`'s honest run succeeds on a bit reading `1`. -/
@[spec] theorem assert_complete_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c]
    (v : BoolVar F)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => ((↑v : CVar F).eval env).isOk ∧
        ∀ bv, (↑v : CVar F).eval env = .ok bv → bv = 1)
        (fun _ _ _ => True) Q⦄
    assert (c := Prover c) v
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨⟨hokv, hone⟩, hk⟩ := hpre
  obtain ⟨bv, hv⟩ := CVar.evalOk hokv
  refine assertEqual_complete_spec (c := c) ↑v (.const 1) Q st
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
/-- `allBools`: on bit operands the result reads as the list's conjunction, under
cast-injectivity up to the length. -/
@[spec] theorem allBools_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length + 1 → k ≤ bs.length + 1 → (j : F) = k → j = k) :
    ⦃⌜True⌝⦄
    allBools (c := Builder V c) bs
    ⦃⇓ r _ => ⌜∀ bl : List Bool, ReadBits V bs bl →
        (↑r : CVar F).val V = bit (bl.all id)⌝⦄ := by
  match bs, hchar with
  | [], _ =>
    simp only [allBools]
    intro nv _ _ bl hbl
    cases hbl
    rfl
  | [a], _ =>
    simp only [allBools]
    intro nv _ _ bl hbl
    obtain - | ⟨hb, hnil⟩ := hbl
    cases hnil
    simpa using hb
  | [a, b], _ =>
    simp only [allBools]
    mvcgen
    intro hr bl hbl
    obtain - | ⟨ha', htl⟩ := hbl
    obtain - | ⟨hb', hnil⟩ := htl
    cases hnil
    simpa using hr _ _ ha' hb'
  | x₁ :: x₂ :: x₃ :: t, hchar =>
    simp only [allBools]
    set bs := x₁ :: x₂ :: x₃ :: t with hbs
    mvcgen
    intro hr bl hbl
    have hsum := sum_bits_val (V := V) hbl
    have hlen := forall₂_length hbl
    have hcount : bl.count true ≤ bs.length + 1 := by
      have := List.count_le_length (a := true) (l := bl)
      omega
    rw [hr, hsum]
    simp only [equalsPure]
    show (if (CVar.const (bs.length : F)).val V = (bl.count true : F) then 1 else 0) = _
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
/-- `allBools`'s honest run succeeds on evaluable operands; where they read as bits the
result is the conjunction bit. -/
@[spec] theorem allBools_complete_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c]
    (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length + 1 → k ≤ bs.length + 1 → (j : F) = k → j = k)
    (Q : PostCond (BoolVar F) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => ∀ b ∈ bs, (((b : BoolVar F) : CVar F).eval env).isOk)
        (fun env (r : BoolVar F) env' => ∀ bl : List Bool, EvalBits env bs bl →
          (↑r : CVar F).eval env' = .ok (bit (bl.all id))) Q⦄
    allBools (c := Prover c) bs
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
/-- `assertAny` asserts some bit is set — no characteristic hypothesis: a zero count
casts to zero in any semiring. -/
@[spec] theorem assertAny_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (bs : List (BoolVar F)) :
    ⦃⌜True⌝⦄
    assertAny (c := Builder V c) bs
    ⦃⇓ _ _ => ⌜∀ bl : List Bool, ReadBits V bs bl →
        bl.any id = true⌝⦄ := by
  simp only [assertAny]
  mvcgen
  intro hne bl hbl
  have hsum := sum_bits_val (V := V) hbl
  rw [hsum] at hne
  by_contra hany
  have hany' : bl.any id = false := by revert hany; cases bl.any id <;> simp
  rw [count_true_eq_zero.mpr hany'] at hne
  exact hne (by simp)

open Std.Do in
/-- `assertAny`'s honest run succeeds on bit operands with some bit set —
cast-injectivity makes the nonzero count a nonzero sum. -/
@[spec] theorem assertAny_complete_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c]
    (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length + 1 → k ≤ bs.length + 1 → (j : F) = k → j = k)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (∀ b ∈ bs, ReadsBit ((b : BoolVar F) : CVar F) env) ∧
        ∀ bl : List Bool, EvalBits env bs bl → bl.any id = true)
        (fun _ _ _ => True) Q⦄
    assertAny (c := Prover c) bs
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
/-- `assertAll` asserts every bit is set, under cast-injectivity up to the length. -/
@[spec] theorem assertAll_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length + 1 → k ≤ bs.length + 1 → (j : F) = k → j = k) :
    ⦃⌜True⌝⦄
    assertAll (c := Builder V c) bs
    ⦃⇓ _ _ => ⌜∀ bl : List Bool, ReadBits V bs bl →
        bl.all id = true⌝⦄ := by
  simp only [assertAll]
  mvcgen
  intro heq bl hbl
  have hsum := sum_bits_val (V := V) hbl
  have hlen := forall₂_length hbl
  have hcount : bl.count true ≤ bs.length + 1 := by
    have := List.count_le_length (a := true) (l := bl)
    omega
  rw [hsum] at heq
  have hconst : (CVar.const (bs.length : F)).val V = ((bs.length : Nat) : F) := rfl
  rw [hconst] at heq
  have := hchar _ _ hcount (by omega) heq
  exact count_true_eq_length.mp (by omega)

open Std.Do in
/-- `assertAll`'s honest run succeeds on bit operands all set — no characteristic
hypothesis: the full count casts to the length in any semiring. -/
@[spec] theorem assertAll_complete_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c]
    (bs : List (BoolVar F))
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (∀ b ∈ bs, ReadsBit ((b : BoolVar F) : CVar F) env) ∧
        ∀ bl : List Bool, EvalBits env bs bl → bl.all id = true)
        (fun _ _ _ => True) Q⦄
    assertAll (c := Prover c) bs
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
/-- `assertExactlyOne` asserts a one-hot list — the count is one, under
cast-injectivity up to the length plus one. -/
@[spec] theorem assertExactlyOne_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length + 1 → k ≤ bs.length + 1 → (j : F) = k → j = k) :
    ⦃⌜True⌝⦄
    assertExactlyOne (c := Builder V c) bs
    ⦃⇓ _ _ => ⌜∀ bl : List Bool, ReadBits V bs bl →
        bl.count true = 1⌝⦄ := by
  simp only [assertExactlyOne]
  mvcgen
  intro heq bl hbl
  have hsum := sum_bits_val (V := V) hbl
  have hlen := forall₂_length hbl
  have hcount : bl.count true ≤ bs.length + 1 := by
    have := List.count_le_length (a := true) (l := bl)
    omega
  rw [hsum] at heq
  have hconst : (CVar.const (1 : F)).val V = ((1 : Nat) : F) := by
    simp [CVar.val]
  rw [hconst] at heq
  exact hchar _ _ hcount (by omega) heq

open Std.Do in
/-- `assertExactlyOne`'s honest run succeeds on a one-hot bit list — the unit count
casts to one in any semiring. -/
@[spec] theorem assertExactlyOne_complete_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c]
    (bs : List (BoolVar F))
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (∀ b ∈ bs, ReadsBit ((b : BoolVar F) : CVar F) env) ∧
        ∀ bl : List Bool, EvalBits env bs bl → bl.count true = 1)
        (fun _ _ _ => True) Q⦄
    assertExactlyOne (c := Prover c) bs
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
