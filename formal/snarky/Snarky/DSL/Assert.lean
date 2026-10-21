import Mathlib.Algebra.Field.Basic
import Snarky.DSL.Boolean

namespace Snarky

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

open Std.WP in
/-- `assertEqual x y` forces `x` and `y` to read equal. -/
@[spec] theorem assertEqual_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :
    ⦃fun _ => True⦄
    assertEqual (c := Builder V c) x y
    ⦃fun _ _ => x.val V = y.val V⦄ := by
  simp only [assertEqual]
  vcgen
  all_goals first
    | exact (LawfulBasicSystem.holds_equal V _ _).mp ‹_›
    | (subst_vars; rfl)

open Snarky.Prover Std.WP in
/-- `assertEqual`'s completeness: where the operands read one value, the run succeeds. -/
theorem Prover.assertEqual_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (v : F) :
    ⦃Reads x v ⊓ Reads y v⦄ assertEqual (c := Prover c) x y ⦃fun _ ↦ ⊤⦄ := by
  unfold assertEqual
  vcgen
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, Checked.apply, LawfulBasicSystem.holds_equal,
      LawfulBasicSystem.cells_equal, CVar.val])

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

open Std.WP in
/-- `assertNonZero v` forces `v` to read nonzero. -/
@[spec] theorem assertNonZero_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) :
    ⦃fun _ => True⦄
    assertNonZero (c := Builder V c) v
    ⦃fun _ _ => v.val V ≠ 0⦄ := by
  simp only [assertNonZero]
  vcgen
  all_goals first
    | (rename_i h; exact absurd ((LawfulBasicSystem.holds_equal V _ _).mp h) (by simp))
    | (rename_i h; exact left_ne_zero_of_mul_eq_one h)
    | (rename_i h; subst_vars; exact h)

attribute [irreducible] assertNonZero

open Snarky.Prover Std.WP in
/-- `assertNonZero`'s completeness: where the operand reads nonzero, the run succeeds. -/
theorem Prover.assertNonZero_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) (a : F) (ha : a ≠ 0) :
    ⦃Reads v a⦄ assertNonZero (c := Prover c) v ⦃fun _ ↦ ⊤⦄ := by
  have hi := fun v' : FVar F ↦ Prover.inv_spec (c := c) v' a ha
  unfold assertNonZero
  vcgen [hi]
  all_goals prover_assert with (intros; simp_all [Reads.fvar_apply, CVar.val])

/-! ## Inequality -/

/-- Assert inequality: the difference is nonzero — `assertNonZero`'s rows. -/
def assertNotEqual [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (x y : FVar F) :
    CircuitM F c PUnit :=
  assertNonZero (CVar.sub_ x y)

open Std.WP in
/-- `assertNotEqual x y` forces `x` and `y` to read unequal. -/
@[spec] theorem assertNotEqual_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :
    ⦃fun _ => True⦄
    assertNotEqual (c := Builder V c) x y
    ⦃fun _ _ => x.val V ≠ y.val V⦄ := by
  simp only [assertNotEqual]
  vcgen
  rename_i h
  simpa [sub_eq_zero] using h

attribute [irreducible] assertNotEqual

open Snarky.Prover Std.WP in
/-- `assertNotEqual`'s completeness: where the operands read unequal, the run succeeds. -/
theorem Prover.assertNotEqual_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (a b : F) (hab : a ≠ b) :
    ⦃Reads x a ⊓ Reads y b⦄ assertNotEqual (c := Prover c) x y ⦃fun _ ↦ ⊤⦄ := by
  have hn := Prover.assertNonZero_spec (c := c) (CVar.sub_ x y) (a - b) (sub_ne_zero.mpr hab)
  unfold assertNotEqual
  vcgen [hn]
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, CVar.val_sub_, CVar.Scoped.sub_])

/-! ## Squares -/

/-- Assert a square identity `x · x = y`: one `square` row. -/
def assertSquare [BasicSystem F c] (x y : FVar F) : CircuitM F c PUnit :=
  addConstraint (BasicSystem.square x y)

open Std.WP in
/-- `assertSquare x y` forces `y` to read as the square of `x`. -/
@[spec] theorem assertSquare_spec {V : Valuation F} [Field F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :
    ⦃fun _ => True⦄
    assertSquare (c := Builder V c) x y
    ⦃fun _ _ => x.val V * x.val V = y.val V⦄ := by
  simp only [assertSquare]
  vcgen
  rename_i h
  exact (LawfulBasicSystem.holds_square V _ _).mp h

attribute [irreducible] assertSquare

open Snarky.Prover Std.WP in
/-- `assertSquare`'s completeness: where the second operand reads the square of the first, the
run succeeds. -/
theorem Prover.assertSquare_spec [Field F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (a : F) :
    ⦃Reads x a ⊓ Reads y (a * a)⦄ assertSquare (c := Prover c) x y ⦃fun _ ↦ ⊤⦄ := by
  unfold assertSquare
  vcgen
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, Checked.apply, LawfulBasicSystem.holds_square,
      LawfulBasicSystem.cells_square])

/-! ## Booleans -/

/-- Assert a boolean holds: its bit equals `1` — `assertEqual`'s rows. -/
def assert [One F] [DecidableEq F] [BasicSystem F c] (v : BoolVar F) : CircuitM F c PUnit :=
  assertEqual ↑v (.const 1)

open Std.WP in
/-- `assert v` forces `v` to read `1`. -/
@[spec] theorem assert_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : BoolVar F) :
    ⦃fun _ => True⦄
    assert (c := Builder V c) v
    ⦃fun _ _ => (↑v : CVar F).val V = 1⦄ := by
  simp only [assert]
  vcgen
  rename_i h
  exact h

attribute [irreducible] assert

open Snarky.Prover Std.WP in
/-- `assert`'s completeness: where the bit reads `true`, the run succeeds. -/
theorem Prover.assert_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : BoolVar F) :
    ⦃Reads v true⦄ assert (c := Prover c) v ⦃fun _ ↦ ⊤⦄ := by
  have he := Prover.assertEqual_spec (c := c) (↑v : CVar F) (.const 1) (1 : F)
  unfold assert
  vcgen [he]
  all_goals prover_assert with simp_all [Reads.fvar_apply, Reads.boolVar_apply, CVar.val, bit]

/-! ## Bit sums -/

/-- Assert at least one bit is set: the bit-sum is nonzero — `assertNonZero`'s rows. -/
def assertAny [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (bs : List (BoolVar F)) :
    CircuitM F c PUnit :=
  assertNonZero (sum (bs.map BoolVar.toCVar))

open Std.WP in
/-- `assertAny bs`, on bit operands, forces some operand to read `1`. -/
@[spec] theorem assertAny_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F)) :
    ⦃fun _ => True⦄
    assertAny (c := Builder V c) bs
    ⦃fun _ _ => (∀ b ∈ bs, (↑b : CVar F).val V = 0 ∨ (↑b : CVar F).val V = 1) →
        ∃ b ∈ bs, (↑b : CVar F).val V = 1⦄ := by
  simp only [assertAny]
  vcgen
  rename_i h hbits
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

open Snarky.Prover Std.WP in
/-- `assertAny`'s completeness: where the bits read values among which `true` occurs, below the
characteristic, the run succeeds. -/
theorem Prover.assertAny_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F)) (vs : List Bool)
    (hone : true ∈ vs) (hchar : ∀ k : Nat, k ≤ vs.length → (k : F) = 0 → k = 0) :
    ⦃All₂ Reads bs vs⦄ assertAny (c := Prover c) bs ⦃fun _ ↦ ⊤⦄ := by
  have hne : (vs.count true : F) ≠ 0 :=
    (cast_count_true_ne_zero_iff hchar).mpr (List.any_eq_true.mpr ⟨true, hone, rfl⟩)
  have hsum := (Pred.le_iff _ _).mp (all₂_reads_le_reads_sum (F := F) bs vs)
  have hn := Prover.assertNonZero_spec (c := c) (sum (bs.map BoolVar.toCVar))
    (vs.count true : F) hne
  unfold assertAny
  vcgen [hn]
  all_goals prover_assert

/-- Assert exactly one bit is set: the bit-sum equals `1` — `assertEqual`'s rows. -/
def assertExactlyOne [Field F] [DecidableEq F] [BasicSystem F c] (bs : List (BoolVar F)) :
    CircuitM F c PUnit :=
  assertEqual (sum (bs.map BoolVar.toCVar)) (.const 1)

open Std.WP in
/-- `assertExactlyOne bs`, on bit operands below the characteristic, forces exactly one
operand to read `1`. -/
@[spec] theorem assertExactlyOne_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length + 1 → k ≤ bs.length + 1 → (j : F) = k → j = k) :
    ⦃fun _ => True⦄
    assertExactlyOne (c := Builder V c) bs
    ⦃fun _ _ => (∀ b ∈ bs, (↑b : CVar F).val V = 0 ∨ (↑b : CVar F).val V = 1) →
        (bs.map fun (b : BoolVar F) => (↑b : CVar F).val V).count 1 = 1⦄ := by
  simp only [assertExactlyOne]
  vcgen
  rename_i h hbits
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

open Snarky.Prover Std.WP in
/-- `assertExactlyOne`'s completeness: where the bits read values with exactly one `true`, the
run succeeds. -/
theorem Prover.assertExactlyOne_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F)) (vs : List Bool)
    (hone : vs.count true = 1) :
    ⦃All₂ Reads bs vs⦄ assertExactlyOne (c := Prover c) bs ⦃fun _ ↦ ⊤⦄ := by
  have hsum := all₂_reads_le_reads_sum (F := F) bs vs
  rw [hone, Nat.cast_one] at hsum
  have he := Prover.assertEqual_spec (c := c) (sum (bs.map BoolVar.toCVar)) (.const 1) (1 : F)
  unfold assertExactlyOne
  vcgen [he]
  all_goals prover_assert with simp_all [Reads.fvar_apply, CVar.val]

/-- Assert every bit is set: the bit-sum equals the length — `assertEqual`'s rows. -/
def assertAll [Field F] [DecidableEq F] [BasicSystem F c] (bs : List (BoolVar F)) :
    CircuitM F c PUnit :=
  assertEqual (sum (bs.map BoolVar.toCVar)) (.const (bs.length : F))

open Std.WP in
/-- `assertAll bs`, on bit operands below the characteristic, forces every operand to
read `1`. -/
@[spec] theorem assertAll_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ bs.length → k ≤ bs.length → (j : F) = k → j = k) :
    ⦃fun _ => True⦄
    assertAll (c := Builder V c) bs
    ⦃fun _ _ => (∀ b ∈ bs, (↑b : CVar F).val V = 0 ∨ (↑b : CVar F).val V = 1) →
        ∀ b ∈ bs, (↑b : CVar F).val V = 1⦄ := by
  simp only [assertAll]
  vcgen
  rename_i h hbits b hb
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
  exact (hall _ (List.mem_map.mpr ⟨b, hb, rfl⟩)).symm

attribute [irreducible] assertAll

open Snarky.Prover Std.WP in
/-- `assertAll`'s completeness: where every bit reads `true`, the run succeeds. -/
theorem Prover.assertAll_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F)) (vs : List Bool)
    (hall : ∀ v ∈ vs, v = true) :
    ⦃All₂ Reads bs vs⦄ assertAll (c := Prover c) bs ⦃fun _ ↦ ⊤⦄ := by
  have hsum : All₂ (Reads (F := F)) bs vs ≤
      Reads (sum (bs.map BoolVar.toCVar)) (bs.length : F) := by
    rw [Pred.le_iff]
    intro s hs
    have h := (Pred.le_iff _ _).mp (all₂_reads_le_reads_sum (F := F) bs vs) s hs
    have hlen : bs.length = vs.length := by
      simpa using congrArg List.length (scoped_read_of_all₂_reads hs).2
    have hcount : vs.count true = vs.length :=
      List.count_eq_length.mpr fun v hv ↦ (hall v hv).symm
    rwa [hcount, ← hlen] at h
  have he := Prover.assertEqual_spec (c := c) (sum (bs.map BoolVar.toCVar))
    (.const (bs.length : F)) (bs.length : F)
  unfold assertAll
  vcgen [he]
  all_goals prover_assert with simp_all [Reads.fvar_apply, CVar.val]

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

open Std.WP in
/-- `assertEq`'s rows force the two bundles' fields equal, field by field, whether or not
either reads as a value. -/
theorem assertEq_fields_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] {val var : Type} [CircuitType F val var]
    (t e : var) :
    ⦃fun _ => True⦄
    assertEq (F := F) (c := Builder V c) (val := val) t e
    ⦃fun _ _ => mapVec (·.val V) (CircuitType.varToFields (val := val) t) =
      mapVec (·.val V) (CircuitType.varToFields (val := val) e)⦄ := by
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
  simp only [build_bind, build, build_pure, List.append_nil] at hsat
  ext i hi
  simpa using hzip nv hsat ⟨i, hi⟩

open Std.WP in
/-- `assertEq`'s rows force the two readings equal: the fields are equal
(`assertEq_fields_spec`), and an encoding determines its value. -/
@[spec] theorem assertEq_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] {val var : Type} [CircuitType F val var]
    (t e : var) {tv ev : val} (ht : CircuitType.Reads V t tv)
    (he : CircuitType.Reads V e ev) :
    ⦃fun _ => True⦄
    assertEq (F := F) (c := Builder V c) (val := val) t e
    ⦃fun _ _ => tv = ev⦄ := by
  refine (builder_spec_iff _ _).mpr fun nv hsat => ?_
  have hfields : CircuitType.valueToFields (F := F) tv = CircuitType.valueToFields (F := F) ev := by
    rw [← ht, ← he]
    exact (builder_spec_iff _ _).mp (assertEq_fields_spec (c := c) (val := val) t e) nv hsat
  rw [← CircuitType.value_roundTrip (F := F) (var := var) tv, hfields,
    CircuitType.value_roundTrip]

open Snarky.Prover Std.WP in
/-- `assertEqual` where its operands read some one value: the shape the bundle traversal
takes, since the value differs per field. -/
private theorem Prover.assertEqual_common [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :
    ⦃⨆ w : F, Reads x w ⊓ Reads y w⦄ assertEqual (c := Prover c) x y ⦃fun _ ↦ ⊤⦄ := by
  rw [triple_iff]
  intro s hs
  rw [Pred.iSup_apply] at hs
  obtain ⟨w, hw⟩ := hs
  exact (triple_iff _ _ _ _).mp (Prover.assertEqual_spec (c := c) x y w) s hw

open Snarky.Prover Std.WP in
/-- `assertEq`'s completeness: where both bundles read one value, the run succeeds. -/
theorem Prover.assertEq_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] {val var : Type} [CircuitType F val var] (t e : var) (a : val) :
    ⦃Reads t a ⊓ Reads e a⦄ assertEq (F := F) (c := Prover c) (val := val) t e ⦃fun _ ↦ ⊤⦄ := by
  have hz := Spec.zipWithVecM (c := c) assertEqual (fun x y ↦ ⨆ w : F, Reads x w ⊓ Reads y w)
    (fun _ _ _ ↦ ⊤) (fun x y ↦ Prover.assertEqual_common (c := c) x y)
    (CircuitType.varToFields (val := val) t) (CircuitType.varToFields (val := val) e)
  unfold assertEq
  vcgen [hz]
  all_goals prover_assert with
    intro s ht he i
    change CircuitType.ReadsAs s t a at ht
    change CircuitType.ReadsAs s e a at he
    refine ⟨(CircuitType.valueToFields (F := F) a)[i], ?_, ?_⟩
    · rw [Reads.fvar_apply]
      exact ⟨ht.1 _ (by simp), by simpa [getElem_mapVec] using congrArg (·[i]) ht.2⟩
    · rw [Reads.fvar_apply]
      exact ⟨he.1 _ (by simp), by simpa [getElem_mapVec] using congrArg (·[i]) he.2⟩

end Snarky
