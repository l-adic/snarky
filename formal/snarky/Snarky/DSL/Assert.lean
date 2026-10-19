import Mathlib.Algebra.Field.Basic
import Snarky.DSL.Boolean

namespace Snarky

set_option mvcgen.warning false

variable {F c : Type}

/-! # Assertion gadgets

Constraints enforced without a result. An impossible constant assertion emits its
unsatisfiable row — the source library fails at construction instead, which a total
builder cannot — so the prover's table cannot satisfy it and soundness holds by
contradiction. -/

/-! ## Equality -/

/-- Assert equality: equal constants fold to nothing, unequal constants emit the
unsatisfiable `equal` row, otherwise one `equal` row. -/
def assertEqual [DecidableEq F] [BasicSystem F c] (x y : FVar F) : CircuitM F c PUnit :=
  match x, y with
  | .const f, .const g =>
    if f = g then pure PUnit.unit else addConstraint (BasicSystem.equal x y)
  | _, _ => addConstraint (BasicSystem.equal x y)

open Std.Do in
/-- `assertEqual x y` forces `x` and `y` to read equal. -/
@[spec] theorem assertEqual_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :
    ⦃⌜True⌝⦄
    assertEqual (c := Builder V c) x y
    ⦃⇓ _ _ => ⌜x.val V = y.val V⌝⦄ := by
  simp only [assertEqual]
  mvcgen
  all_goals
    intro h
    exact (LawfulBasicSystem.holds_equal V _ _).mp h

/-- `assertEqual`'s completeness law: where the operands read equal the run succeeds and
its row is satisfied — the unequal-constant arm is unreachable. -/
@[complete_law]
theorem assertEqual_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (v : F) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st x v ∧
      CircuitType.ReadsAs (val := F) st y v)
      (assertEqual (c := c) x y) (fun _ _ => True) := by
  have hrow : ∀ st : ProverState F, (CircuitType.ReadsAs (val := F) st x v ∧
      CircuitType.ReadsAs (val := F) st y v) → ∀ stf : ProverState F, st ≤ stf →
      ConstraintHolds.Holds stf.env.get (BasicSystem.equal (c := c) x y) := by
    rintro st ⟨⟨hx, hvx⟩, ⟨hy, hvy⟩⟩ stf hle
    rw [CircuitType.scoped_fvar] at hx hy
    rw [CircuitType.reads_fvar] at hvx hvy
    exact (LawfulBasicSystem.holds_equal _ _ _).mpr
      (by rw [CVar.val_of_le hle hx, CVar.val_of_le hle hy, hvx, hvy])
  simp only [assertEqual]
  split
  · split
    · exact Complete.pure_of fun _ _ => trivial
    · exact Complete.imp (fun _ h => h) (fun _ _ _ => trivial) (Complete.addConstraint hrow)
  · exact Complete.imp (fun _ h => h) (fun _ _ _ => trivial) (Complete.addConstraint hrow)

open Std.Do in
/-- `assertEqual`'s state-relative completeness: where the operands are in scope and read equal,
the run succeeds and the state only grows. -/
theorem Prover.assertEqual_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀ ∧ st₀.read x = st₀.read y⌝⦄
    assertEqual (c := Prover c) x y
    ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄ := by
  simp only [assertEqual]
  mvcgen
  all_goals (try simp only [LawfulBasicSystem.scoped_equal])
  all_goals grind [LawfulBasicSystem.holds_equal]

/-- Registered. -/
@[spec] private def Prover.assertEqual_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :=
  Prover.register (Prover.assertEqual_spec (c := c) x y)

attribute [irreducible] assertEqual

/-! ## Non-zeroness -/

/-- Assert non-zeroness by witnessing the inverse: a nonzero constant folds to nothing,
the constant zero emits the falsum `0 = 1`, otherwise `inv`'s row. -/
def assertNonZero [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (v : FVar F) :
    CircuitM F c PUnit :=
  match v with
  | .const f =>
    if f = 0 then addConstraint (BasicSystem.equal (.const 0 : CVar F) (.const 1))
    else pure PUnit.unit
  | _ => do
    let _ ← inv v
    pure PUnit.unit

open Std.Do in
/-- `assertNonZero v` forces `v` to read nonzero. -/
@[spec] theorem assertNonZero_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) :
    ⦃⌜True⌝⦄
    assertNonZero (c := Builder V c) v
    ⦃⇓ _ _ => ⌜v.val V ≠ 0⌝⦄ := by
  simp only [assertNonZero]
  mvcgen
  all_goals first
    | (intro h; exact absurd ((LawfulBasicSystem.holds_equal V _ _).mp h) (by simp))
    | (rename_i h; exact left_ne_zero_of_mul_eq_one h)

attribute [irreducible] assertNonZero

open Std.Do in
/-- `assertNonZero`'s state-relative completeness: where the operand is in scope and reads
nonzero, the run succeeds and the state only grows. -/
theorem Prover.assertNonZero_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ v.Scoped st₀ ∧ st₀.read v ≠ 0⌝⦄
    assertNonZero (c := Prover c) v
    ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄ := by
  unfold assertNonZero
  mvcgen
  all_goals grind [Prover.Reg.iff, CVar.val]

/-- Registered. -/
@[spec] private def Prover.assertNonZero_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) :=
  Prover.register (Prover.assertNonZero_spec (c := c) v)

/-! ## Inequality -/

/-- Assert inequality: the difference is nonzero — `assertNonZero`'s rows. -/
def assertNotEqual [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (x y : FVar F) :
    CircuitM F c PUnit :=
  assertNonZero (CVar.sub_ x y)

open Std.Do in
/-- `assertNotEqual x y` forces `x` and `y` to read unequal. -/
@[spec] theorem assertNotEqual_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :
    ⦃⌜True⌝⦄
    assertNotEqual (c := Builder V c) x y
    ⦃⇓ _ _ => ⌜x.val V ≠ y.val V⌝⦄ := by
  simp only [assertNotEqual]
  mvcgen
  intro h
  simpa [sub_eq_zero] using h

attribute [irreducible] assertNotEqual

open Std.Do in
/-- `assertNotEqual`'s state-relative completeness: where the operands are in scope and read
unequal, the run succeeds and the state only grows. -/
theorem Prover.assertNotEqual_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀ ∧ st₀.read x ≠ st₀.read y⌝⦄
    assertNotEqual (c := Prover c) x y
    ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄ := by
  simp only [assertNotEqual]
  mvcgen
  all_goals grind [Prover.Reg.iff, CVar.val_sub_, CVar.Scoped.sub_, sub_eq_zero]

/-- Registered. -/
@[spec] def Prover.assertNotEqual_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :=
  Prover.register (Prover.assertNotEqual_spec (c := c) x y)

/-! ## Squares -/

/-- Assert a square identity `x · x = y`: one `square` row. -/
def assertSquare [BasicSystem F c] (x y : FVar F) : CircuitM F c PUnit :=
  addConstraint (BasicSystem.square x y)

open Std.Do in
/-- `assertSquare x y` forces `y` to read as the square of `x`. -/
@[spec] theorem assertSquare_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :
    ⦃⌜True⌝⦄
    assertSquare (c := Builder V c) x y
    ⦃⇓ _ _ => ⌜x.val V * x.val V = y.val V⌝⦄ := by
  simp only [assertSquare]
  mvcgen
  intro h
  exact (LawfulBasicSystem.holds_square V _ _).mp h

/-- `assertSquare`'s completeness law: where the identity reads, the row is satisfied. -/
theorem assertSquare_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (xv yv : F)
    (hxy : xv * xv = yv) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st x xv ∧
      CircuitType.ReadsAs (val := F) st y yv)
      (assertSquare (c := c) x y) (fun _ _ => True) := by
  refine Complete.imp (fun _ h => h) (fun _ _ _ => trivial) (Complete.addConstraint ?_)
  rintro st ⟨⟨hx, hvx⟩, ⟨hy, hvy⟩⟩ stf hle
  rw [CircuitType.scoped_fvar] at hx hy
  rw [CircuitType.reads_fvar] at hvx hvy
  exact (LawfulBasicSystem.holds_square _ _ _).mpr
    (by rw [CVar.val_of_le hle hx, CVar.val_of_le hle hy, hvx, hvy]; exact hxy)

attribute [irreducible] assertSquare

open Std.Do in
/-- `assertSquare`'s state-relative completeness: where the operands are in scope and the
second reads the square of the first, the run succeeds and the state only grows. -/
theorem Prover.assertSquare_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀ ∧ st₀.read x * st₀.read x = st₀.read y⌝⦄
    assertSquare (c := Prover c) x y
    ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄ := by
  unfold assertSquare
  mvcgen
  all_goals (try simp only [LawfulBasicSystem.scoped_square])
  all_goals grind [LawfulBasicSystem.holds_square]

/-- Registered. -/
@[spec] private def Prover.assertSquare_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :=
  Prover.register (Prover.assertSquare_spec (c := c) x y)

/-! ## Booleans -/

/-- Assert a boolean holds: its bit equals `1` — `assertEqual`'s rows. -/
def assert [One F] [DecidableEq F] [BasicSystem F c] (v : BoolVar F) : CircuitM F c PUnit :=
  assertEqual ↑v (.const 1)

open Std.Do in
/-- `assert v` forces `v` to read `1`. -/
@[spec] theorem assert_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : BoolVar F) :
    ⦃⌜True⌝⦄
    assert (c := Builder V c) v
    ⦃⇓ _ _ => ⌜(↑v : CVar F).val V = 1⌝⦄ := by
  simp only [assert]
  mvcgen

attribute [irreducible] assert

open Std.Do in
/-- `assert`'s state-relative completeness: where the bit is in scope and reads `1`, the run
succeeds and the state only grows. -/
theorem Prover.assert_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : BoolVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ (↑v : CVar F).Scoped st₀ ∧ st₀.read v = 1⌝⦄
    assert (c := Prover c) v
    ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄ := by
  simp only [assert]
  mvcgen
  all_goals grind [Prover.Reg.iff, CVar.val, CVar.scoped_const]

/-- Registered. -/
@[spec] def Prover.assert_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : BoolVar F) :=
  Prover.register (Prover.assert_spec (c := c) v)

/-! ## Bit sums -/

/-- Assert at least one bit is set: the bit-sum is nonzero — `assertNonZero`'s rows. -/
def assertAny [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (bs : List (BoolVar F)) :
    CircuitM F c PUnit :=
  assertNonZero (sum (bs.map BoolVar.toCVar))

open Std.Do in
/-- `assertAny bs`, on bit operands, forces some operand to read `1`. -/
@[spec] theorem assertAny_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F)) :
    ⦃⌜True⌝⦄
    assertAny (c := Builder V c) bs
    ⦃⇓ _ _ => ⌜(∀ b ∈ bs, (↑b : CVar F).val V = 0 ∨ (↑b : CVar F).val V = 1) →
        ∃ b ∈ bs, (↑b : CVar F).val V = 1⌝⦄ := by
  simp only [assertAny]
  mvcgen
  intro h hbits
  have hbits' : ∀ x ∈ (bs.map BoolVar.toCVar).map (·.val V), x = 0 ∨ x = 1 := by
    intro x hx
    simp only [List.map_map, List.mem_map, Function.comp] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact hbits b hb
  rw [sum_eval, sum_of_bits _ hbits'] at h
  generalize hL : (bs.map BoolVar.toCVar).map (·.val V) = L at h
  have hpos : 0 < List.count (1 : F) L := by
    rcases Nat.eq_zero_or_pos (List.count (1 : F) L) with h0 | h0
    · exact absurd (by rw [h0]; simp) h
    · exact h0
  have hmem := List.count_pos_iff.mp hpos
  rw [← hL] at hmem
  simp only [List.map_map, List.mem_map, Function.comp] at hmem
  exact hmem

attribute [irreducible] assertAny

open Std.Do in
/-- `assertAny`'s state-relative completeness: where the bits are in scope and some reads `1`,
below the characteristic, the run succeeds and the state only grows. -/
theorem Prover.assertAny_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F))
    (hchar : ∀ k : Nat, k ≤ bs.length → (k : F) = 0 → k = 0) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ (∀ b ∈ bs, (↑b : CVar F).Scoped st₀) ∧
      (∀ b ∈ bs, st₀.read b = 0 ∨ st₀.read b = 1) ∧ ∃ b ∈ bs, st₀.read b = 1⌝⦄
    assertAny (c := Prover c) bs
    ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄ := by
  simp only [assertAny]
  mvcgen
  -- the bit-sum is in scope, and reads nonzero below the characteristic
  case vc1.pre =>
    rename_i s h
    obtain ⟨rfl, hsc, hbits, hone⟩ := h
    exact ⟨trivial, scoped_sum_of_bits hsc, (read_sum_ne_zero_iff hbits hchar).mpr hone⟩
  all_goals grind [Prover.Reg.iff]

/-- Registered. -/
@[spec] def Prover.assertAny_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F))
    (hchar : ∀ k : Nat, k ≤ bs.length → (k : F) = 0 → k = 0) :=
  Prover.register (Prover.assertAny_spec (c := c) bs hchar)

/-- Assert exactly one bit is set: the bit-sum equals `1` — `assertEqual`'s rows. -/
def assertExactlyOne [Field F] [DecidableEq F] [BasicSystem F c] (bs : List (BoolVar F)) :
    CircuitM F c PUnit :=
  assertEqual (sum (bs.map BoolVar.toCVar)) (.const 1)

open Std.Do in
/-- `assertExactlyOne bs`, on bit operands below the characteristic, forces exactly one
operand to read `1`. -/
@[spec] theorem assertExactlyOne_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length + 1 → k ≤ bs.length + 1 → (j : F) = k → j = k) :
    ⦃⌜True⌝⦄
    assertExactlyOne (c := Builder V c) bs
    ⦃⇓ _ _ => ⌜(∀ b ∈ bs, (↑b : CVar F).val V = 0 ∨ (↑b : CVar F).val V = 1) →
        (bs.map fun (b : BoolVar F) => (↑b : CVar F).val V).count 1 = 1⌝⦄ := by
  simp only [assertExactlyOne]
  mvcgen
  intro h hbits
  have hbits' : ∀ x ∈ bs.map (fun (b : BoolVar F) => (↑b : CVar F).val V), x = 0 ∨ x = 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hbits b hb
  rw [sum_eval, List.map_map] at h
  simp only [CVar.val, Function.comp_def] at h
  rw [sum_of_bits _ hbits'] at h
  have hle : (bs.map fun (b : BoolVar F) => (↑b : CVar F).val V).count 1 ≤ bs.length + 1 := by
    have := List.count_le_length (a := (1 : F))
      (l := bs.map fun (b : BoolVar F) => (↑b : CVar F).val V)
    simp only [List.length_map] at this
    omega
  exact hchar _ 1 hle (by omega) (by simpa using h)

attribute [irreducible] assertExactlyOne

open Std.Do in
/-- `assertExactlyOne`'s state-relative completeness: where the bits are in scope and exactly
one reads `1`, the run succeeds and the state only grows. -/
theorem Prover.assertExactlyOne_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F)) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ (∀ b ∈ bs, (↑b : CVar F).Scoped st₀) ∧
      (∀ b ∈ bs, st₀.read b = 0 ∨ st₀.read b = 1) ∧
      (bs.map fun b : BoolVar F => st₀.read b).count 1 = 1⌝⦄
    assertExactlyOne (c := Prover c) bs
    ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄ := by
  simp only [assertExactlyOne]
  mvcgen
  -- the bit-sum is in scope, and reads its count of ones
  case vc1.pre =>
    rename_i s h
    obtain ⟨rfl, hsc, hbits, hone⟩ := h
    refine ⟨trivial, scoped_sum_of_bits hsc, trivial, ?_⟩
    rw [read_sum_of_bits hbits, hone]
    simp [CVar.val]
  all_goals grind [Prover.Reg.iff]

/-- Registered. -/
@[spec] def Prover.assertExactlyOne_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F)) :=
  Prover.register (Prover.assertExactlyOne_spec (c := c) bs)

/-- Assert every bit is set: the bit-sum equals the length — `assertEqual`'s rows. -/
def assertAll [Field F] [DecidableEq F] [BasicSystem F c] (bs : List (BoolVar F)) :
    CircuitM F c PUnit :=
  assertEqual (sum (bs.map BoolVar.toCVar)) (.const (bs.length : F))

open Std.Do in
/-- `assertAll bs`, on bit operands below the characteristic, forces every operand to
read `1`. -/
@[spec] theorem assertAll_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length → k ≤ bs.length → (j : F) = k → j = k) :
    ⦃⌜True⌝⦄
    assertAll (c := Builder V c) bs
    ⦃⇓ _ _ => ⌜(∀ b ∈ bs, (↑b : CVar F).val V = 0 ∨ (↑b : CVar F).val V = 1) →
        ∀ b ∈ bs, (↑b : CVar F).val V = 1⌝⦄ := by
  simp only [assertAll]
  mvcgen
  intro h hbits
  have hbits' : ∀ x ∈ bs.map (fun (b : BoolVar F) => (↑b : CVar F).val V), x = 0 ∨ x = 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hbits b hb
  rw [sum_eval, List.map_map] at h
  simp only [CVar.val, Function.comp_def] at h
  rw [sum_of_bits _ hbits'] at h
  have hle : (bs.map fun (b : BoolVar F) => (↑b : CVar F).val V).count 1 ≤ bs.length := by
    have := List.count_le_length (a := (1 : F))
      (l := bs.map fun (b : BoolVar F) => (↑b : CVar F).val V)
    simpa only [List.length_map] using this
  have hcount := hchar _ _ hle (Nat.le_refl _) h
  have hall := List.count_eq_length.mp
    (show (bs.map fun (b : BoolVar F) => (↑b : CVar F).val V).count 1
        = (bs.map fun (b : BoolVar F) => (↑b : CVar F).val V).length by
      rw [hcount]; simp)
  intro b hb
  exact (hall _ (List.mem_map.mpr ⟨b, hb, rfl⟩)).symm

attribute [irreducible] assertAll

open Std.Do in
/-- `assertAll`'s state-relative completeness: where the bits are in scope and every one reads
`1`, the run succeeds and the state only grows. -/
theorem Prover.assertAll_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F)) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ (∀ b ∈ bs, (↑b : CVar F).Scoped st₀) ∧ ∀ b ∈ bs, st₀.read b = 1⌝⦄
    assertAll (c := Prover c) bs
    ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄ := by
  simp only [assertAll]
  mvcgen
  -- the bit-sum is in scope, and reads the number of operands
  case vc1.pre =>
    rename_i s h
    obtain ⟨rfl, hsc, hall⟩ := h
    refine ⟨trivial, scoped_sum_of_bits hsc, trivial, ?_⟩
    rw [read_sum_of_bits fun b hb => Or.inr (hall b hb), List.count_eq_length.mpr fun v hv => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
      exact (hall b hb).symm]
    simp [CVar.val]
  all_goals grind [Prover.Reg.iff]

/-- Registered. -/
@[spec] def Prover.assertAll_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F)) :=
  Prover.register (Prover.assertAll_spec (c := c) bs)

/-! ## Equality at a bundle

`assertEq` constrains two bundles to read equal, field by field in index order — the
order the source walks a product, a record and a vector alike, so one traversal over the
encoding's fields serves every shape. -/

/-- Constrain two bundles to read equal: one `assertEqual` per field, in order. -/
def assertEq [DecidableEq F] [BasicSystem F c] {val var : Type}
    [CircuitType F val var] (t e : var) : CircuitM F c PUnit := do
  let _ ← zipWithVecM assertEqual (CircuitType.varToFields (val := val) t)
    (CircuitType.varToFields (val := val) e)
  pure PUnit.unit

open Std.Do in
/-- `assertEq`'s rows force the two bundles' fields equal, field by field, whether or not
either reads as a value. -/
theorem assertEq_fields_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] {val var : Type} [CircuitType F val var]
    (t e : var) :
    ⦃⌜True⌝⦄
    assertEq (F := F) (c := Builder V c) (val := val) t e
    ⦃⇓ _ _ => ⌜mapVec (·.val V) (CircuitType.varToFields (val := val) t) =
      mapVec (·.val V) (CircuitType.varToFields (val := val) e)⌝⦄ := by
  have hzip := (builder_spec_iff _ _).mp (zipWithVecM_spec (V := V)
    (assertEqual (c := Builder V c)) (CircuitType.varToFields (val := val) t)
    (CircuitType.varToFields (val := val) e)
    (fun i _ => ((CircuitType.varToFields (val := val) t)[i.val]).val V
      = ((CircuitType.varToFields (val := val) e)[i.val]).val V)
    (fun i => assertEqual_spec (c := c) (V := V) _ _))
  refine (builder_spec_iff _ _).mpr fun nv hsat => ?_
  replace hsat : ∀ con ∈ (build (zipWithVecM (assertEqual (c := c))
      (CircuitType.varToFields (val := val) t) (CircuitType.varToFields (val := val) e) >>=
      fun _ => (pure PUnit.unit : CircuitM F c PUnit)) nv).constraints,
      ConstraintHolds.Holds V con := hsat
  simp only [build_bind, build, List.append_nil] at hsat
  ext i hi
  simpa using hzip nv hsat ⟨i, hi⟩

open Std.Do in
/-- `assertEq`'s rows force the two readings equal: the fields are equal
(`assertEq_fields_spec`), and an encoding determines its value. -/
@[spec] theorem assertEq_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] {val var : Type} [CircuitType F val var]
    (t e : var) {tv ev : val} (ht : CircuitType.Reads V t tv)
    (he : CircuitType.Reads V e ev) :
    ⦃⌜True⌝⦄
    assertEq (F := F) (c := Builder V c) (val := val) t e
    ⦃⇓ _ _ => ⌜tv = ev⌝⦄ := by
  refine (builder_spec_iff _ _).mpr fun nv hsat => ?_
  have hfields : CircuitType.valueToFields (F := F) tv = CircuitType.valueToFields (F := F) ev := by
    rw [← ht, ← he]
    exact (builder_spec_iff _ _).mp (assertEq_fields_spec (c := c) (val := val) t e) nv hsat
  rw [← CircuitType.value_roundTrip (F := F) (var := var) tv, hfields,
    CircuitType.value_roundTrip]

/-- `assertEq`'s completeness law: where the operands read the same value the run
succeeds and its rows are satisfied at every extension of the final table. -/
theorem assertEq_complete [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] {val var : Type} [CircuitType F val var] (t e : var) (a : val) :
    Complete (F := F) (c := c) (fun st => CircuitType.Scoped (val := val) st t ∧
        CircuitType.Scoped (val := val) st e ∧ CircuitType.Reads st.env.get t a ∧
        CircuitType.Reads st.env.get e a)
      (assertEq (c := c) (val := val) t e) (fun _ _ => True) := by
  refine Complete.bind
    (zipWithVecM_complete (c := c) assertEqual (CircuitType.varToFields (val := val) t)
      (CircuitType.varToFields (val := val) e)
      (fun st => CircuitType.Scoped (val := val) st t ∧ CircuitType.Scoped (val := val) st e ∧
        CircuitType.Reads st.env.get t a ∧ CircuitType.Reads st.env.get e a)
      (fun _ _ _ => True)
      (fun _ _ hle h => ⟨CircuitType.Scoped.mono (ProverState.nv_le_of_le hle) h.1,
        CircuitType.Scoped.mono (ProverState.nv_le_of_le hle) h.2.1, h.2.2.1.of_le h.1 hle,
        h.2.2.2.of_le h.2.1 hle⟩)
      (fun _ _ => monotone_const)
      (fun i st' h => by
        have h₁ := congrArg (fun v : Vector F (CircuitType.size F val) => v[i.val]) h.2.2.1
        have h₂ := congrArg (fun v : Vector F (CircuitType.size F val) => v[i.val]) h.2.2.2
        simp only [getElem_mapVec] at h₁ h₂
        exact assertEqual_complete (c := c) _ _
          ((CircuitType.valueToFields (F := F) a)[i.val]) st'
          ⟨⟨CircuitType.scoped_fvar.mpr (h.1 _ (by simp)),
              CircuitType.reads_fvar.mpr h₁⟩,
            ⟨CircuitType.scoped_fvar.mpr (h.2.1 _ (by simp)),
              CircuitType.reads_fvar.mpr h₂⟩⟩))
    fun _ => Complete.pure_of fun _ _ => trivial

open Std.Do in
/-- The fields' loop of `assertEq`, registered: `zipWithVecM`'s law at `assertEqual`, each field
pair in scope and reading equal. -/
@[spec] private def Prover.assertEq_loop_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] {n : Nat} (xs ys : Vector (FVar F) n) :=
  Prover.register (Prover.zipWithVecM_spec (c := c) assertEqual
    (fun st x y => x.Scoped st ∧ y.Scoped st ∧ st.read x = st.read y)
    (fun st _ _ _ s' => st ≤ s')
    (by grind [ProverState.read_of_le, CVar.Scoped.of_le]) (by grind) (by grind) (by grind)
    (fun st x y => Prover.assertEqual_spec (c := c) x y st) xs ys)

open Std.Do in
/-- `assertEq`'s state-relative completeness: where both bundles are in scope and their fields
read equal, the run succeeds and the state only grows. -/
theorem Prover.assertEq_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] {val var : Type} [CircuitType F val var] (t e : var)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ CircuitType.Scoped (val := val) st₀ t ∧
      CircuitType.Scoped (val := val) st₀ e ∧
      mapVec (·.val st₀.env.get) (CircuitType.varToFields (val := val) t) =
        mapVec (·.val st₀.env.get) (CircuitType.varToFields (val := val) e)⌝⦄
    assertEq (F := F) (c := Prover c) (val := val) t e
    ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄ := by
  simp only [assertEq]
  mvcgen
  -- the loop's entry: the bundles' scope and readings, field by field
  case vc1.pre =>
    rename_i s h
    obtain ⟨rfl, ht, he, hfields⟩ := h
    exact ⟨trivial, fun i => ⟨ht _ (by simp), he _ (by simp),
      by simpa [getElem_mapVec] using congrArg (·[i]) hfields⟩⟩
  all_goals grind [Prover.Reg.iff]

/-- Registered. -/
@[spec] def Prover.assertEq_reg [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] {val var : Type} [CircuitType F val var] (t e : var) :=
  Prover.register (Prover.assertEq_spec (F := F) (c := c) (val := val) t e)

end Snarky
