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

/-- `assertEqual`'s honest run on operands reading equal: the row accepted, nothing
allocated. -/
theorem assertEqual_run {F c : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {x y : FVar F}
    (st : ProverState F) (hx : x.Scoped st) (hy : y.Scoped st)
    (h : x.val st.env.toValuation = y.val st.env.toValuation) :
    prove (Checker.holds (F := F) (c := c)) (assertEqual (c := c) x y) st.nv st.env
      = .ok (st.out ()) := by
  have hrow := prove_addConstraint st (LawfulChecker.holds_equal (c := c) hx hy h)
  cases x <;> cases y <;> simp only [assertEqual] <;>
    first
    | (split_ifs with hfg
       · rfl
       · exact absurd (by simpa [CVar.val] using h) hfg)
    | exact hrow

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

/-- The same chain in the prover reading: on agreeing values the honest run lands at
the incoming state — one run equation per call. -/
example [BasicSystem F c] [Checker F c] [LawfulChecker F c] (st : ProverState F)
    (x y z : FVar F) (hx : x.Scoped st) (hy : y.Scoped st) (hz : z.Scoped st)
    (hxy : x.val st.env.toValuation = y.val st.env.toValuation)
    (hyz : y.val st.env.toValuation = z.val st.env.toValuation) :
    prove (Checker.holds (F := F) (c := c))
      (do assertEqual (c := c) x y
          assertEqual (c := c) y z : CircuitM F c PUnit) st.nv st.env = .ok (st.out ()) := by
  simp only [prove_bind, assertEqual_run st hx hy hxy, Except.bind]
  exact assertEqual_run st hy hz hyz

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

/-- `assertNonZero`'s honest run on a nonzero operand: `inv`'s run, result dropped. -/
theorem assertNonZero_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {v : FVar F}
    (st : ProverState F) (hv : v.Scoped st) (hne : v.val st.env.toValuation ≠ 0) :
    prove (Checker.holds (F := F) (c := c)) (assertNonZero (c := c) v) st.nv st.env
      = .ok ((invRun st v).1.out ()) := by
  cases v <;> simp only [assertNonZero]
  case const f =>
    rw [if_neg (by simpa [CVar.val] using hne)]
    rfl
  all_goals
    simp only [prove_bind, inv_run st hv hne, Except.bind]
    rfl

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

/-- `assertNotEqual`'s honest run on operands reading apart: `assertNonZero`'s on the
difference. -/
theorem assertNotEqual_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {x y : FVar F}
    (st : ProverState F) (hx : x.Scoped st) (hy : y.Scoped st)
    (hne : x.val st.env.toValuation ≠ y.val st.env.toValuation) :
    prove (Checker.holds (F := F) (c := c)) (assertNotEqual (c := c) x y) st.nv st.env
      = .ok ((invRun st (CVar.sub_ x y)).1.out ()) :=
  assertNonZero_run st (hx.sub_ hy) (by rw [CVar.val_sub_]; exact sub_ne_zero.mpr hne)

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

/-- `assertSquare`'s honest run on operands satisfying the identity: the row accepted. -/
theorem assertSquare_run {F c : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {x y : FVar F}
    (st : ProverState F) (hx : x.Scoped st) (hy : y.Scoped st)
    (h : x.val st.env.toValuation * x.val st.env.toValuation = y.val st.env.toValuation) :
    prove (Checker.holds (F := F) (c := c)) (assertSquare (c := c) x y) st.nv st.env
      = .ok (st.out ()) :=
  prove_addConstraint st (LawfulChecker.holds_square hx hy h)

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

/-- `assert`'s honest run on a set bit: `assertEqual`'s. -/
theorem assert_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {v : BoolVar F}
    (st : ProverState F) (hv : (↑v : CVar F).Scoped st)
    (h : (↑v : CVar F).val st.env.toValuation = 1) :
    prove (Checker.holds (F := F) (c := c)) (assert (c := c) v) st.nv st.env
      = .ok (st.out ()) :=
  assertEqual_run st hv (CVar.scoped_const _ _) (by simpa [CVar.val] using h)

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

/-- `allBools`'s honest run lands at `allRun` — `allBools` is `all`'s definition. -/
theorem allBools_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {bs : List (BoolVar F)}
    (st : ProverState F) (hbs : ∀ b ∈ bs, (↑b : CVar F).Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (allBools (c := c) bs) st.nv st.env
      = .ok ((allRun st bs).1.out (allRun st bs).2) := by
  match bs with
  | [] => rfl
  | [a] => rfl
  | [a, b] => exact and_run st (hbs a (by simp)) (hbs b (by simp))
  | _ :: _ :: _ :: _ =>
    exact equals_run st (CVar.scoped_const _ _) (CVar.Scoped.sum (List.forall_mem_map.mpr hbs))

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

/-- `assertAny`'s honest run on bit operands with some bit set: `assertNonZero`'s on
the bit-sum, under the cast injectivity that makes the count nonzero. -/
theorem assertAny_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {bs : List (BoolVar F)}
    (hchar : ∀ j k : Nat, j ≤ bs.length + 1 → k ≤ bs.length + 1 → (j : F) = k → j = k)
    (st : ProverState F) (hbs : ∀ b ∈ bs, (↑b : CVar F).Scoped st)
    {bl : List Bool} (hbl : ReadBits st.env.toValuation bs bl) (hany : bl.any id = true) :
    prove (Checker.holds (F := F) (c := c)) (assertAny (c := c) bs) st.nv st.env
      = .ok ((invRun st (sum (bs.map BoolVar.toCVar))).1.out ()) := by
  refine assertNonZero_run st (CVar.Scoped.sum (List.forall_mem_map.mpr hbs)) ?_
  rw [sum_bits_val hbl]
  have hlen := forall₂_length hbl
  have hcount : bl.count true ≤ bs.length + 1 := by
    have := List.count_le_length (a := true) (l := bl)
    omega
  intro hcast
  have h0 : bl.count true = 0 := hchar _ 0 hcount (by omega) (by simpa using hcast)
  rw [count_true_eq_zero.mp h0] at hany
  cases hany

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

/-- `assertAll`'s honest run on bit operands all set: `assertEqual`'s on the bit-sum. -/
theorem assertAll_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {bs : List (BoolVar F)}
    (st : ProverState F) (hbs : ∀ b ∈ bs, (↑b : CVar F).Scoped st)
    {bl : List Bool} (hbl : ReadBits st.env.toValuation bs bl) (hall : bl.all id = true) :
    prove (Checker.holds (F := F) (c := c)) (assertAll (c := c) bs) st.nv st.env
      = .ok (st.out ()) := by
  refine assertEqual_run st (CVar.Scoped.sum (List.forall_mem_map.mpr hbs))
    (CVar.scoped_const _ _) ?_
  rw [sum_bits_val hbl, count_true_eq_length.mpr hall, forall₂_length hbl]
  rfl

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

/-- `assertExactlyOne`'s honest run on a one-hot bit list: `assertEqual`'s on the
bit-sum. -/
theorem assertExactlyOne_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {bs : List (BoolVar F)}
    (st : ProverState F) (hbs : ∀ b ∈ bs, (↑b : CVar F).Scoped st)
    {bl : List Bool} (hbl : ReadBits st.env.toValuation bs bl) (hone : bl.count true = 1) :
    prove (Checker.holds (F := F) (c := c)) (assertExactlyOne (c := c) bs) st.nv st.env
      = .ok (st.out ()) := by
  refine assertEqual_run st (CVar.Scoped.sum (List.forall_mem_map.mpr hbs))
    (CVar.scoped_const _ _) ?_
  rw [sum_bits_val hbl, hone]
  simp [CVar.val]

end Snarky
