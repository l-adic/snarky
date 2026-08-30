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
theorem assertEqual_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (v : F) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st x v ∧
      CircuitType.ReadsAs (val := F) st y v)
      (assertEqual (c := c) x y) (fun _ _ => True) := by
  rintro st ⟨hx, hy⟩
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]
    at hx hy
  obtain ⟨hx, hvx⟩ := hx
  obtain ⟨hy, hvy⟩ := hy
  have hxy : x.val st.env.get = y.val st.env.get := by rw [hvx, hvy]
  simp only [assertEqual]
  split
  · split
    · exact ⟨PUnit.unit, st, rfl, by simp [Sat, build], trivial⟩
    · simp only [CVar.val] at hxy
      exact absurd hxy ‹_›
  · exact ⟨PUnit.unit, st, Runs.addConstraint, fun hnv hle =>
      Sat.addConstraint ((LawfulBasicSystem.holds_equal _ _ _).mpr
        (by rw [CVar.val_of_le hle hx, CVar.val_of_le hle hy]; exact hxy)), trivial⟩

attribute [irreducible] assertEqual

/-! ## Non-zeroness -/

/-- Assert non-zeroness by witnessing the inverse: a nonzero constant folds to nothing,
the constant zero emits the falsum `0 = 1`, otherwise `inv`'s row. -/
def assertNonZero [Field F] [DecidableEq F] [BasicSystem F c] (v : FVar F) :
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

/-- `assertNonZero`'s completeness law: where the operand reads nonzero the run succeeds —
`inv`'s — and its row is satisfied; the constant-zero arm is unreachable. -/
theorem assertNonZero_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) (vv : F) (hvne : vv ≠ 0) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st v vv) (assertNonZero (c := c) v)
      (fun _ _ => True) := by
  intro st hv
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar] at hv
  obtain ⟨hv, hvv⟩ := hv
  subst hvv
  have hne := hvne
  simp only [assertNonZero]
  split
  · simp only [CVar.val] at hne
    exact ⟨PUnit.unit, st, by rw [Runs, if_neg hne]; rfl, by simp [Sat, build, if_neg hne],
      trivial⟩
  · obtain ⟨r, st₁, hrun, hsat, _⟩ :=
      inv_complete (c := c) v (v.val st.env.get) hne st
        ⟨CircuitType.scoped_fvar.mpr hv, rfl⟩
    exact ⟨PUnit.unit, st₁, hrun.bind rfl, fun hnv hle => Sat.bind hrun (hsat hnv hle) Sat.pure,
      trivial⟩

attribute [irreducible] assertNonZero

/-! ## Inequality -/

/-- Assert inequality: the difference is nonzero — `assertNonZero`'s rows. -/
def assertNotEqual [Field F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) :
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

/-- `assertNotEqual`'s completeness law: `assertNonZero`'s, at the difference. -/
theorem assertNotEqual_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (xv yv : F)
    (hne : xv ≠ yv) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st x xv ∧
      CircuitType.ReadsAs (val := F) st y yv)
      (assertNotEqual (c := c) x y) (fun _ _ => True) := by
  rintro st ⟨hx, hy⟩
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]
    at hx hy
  obtain ⟨hx, hvx⟩ := hx
  obtain ⟨hy, hvy⟩ := hy
  refine assertNonZero_complete (c := c) _ (xv - yv) (sub_ne_zero_of_ne hne) st ?_
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]
  exact ⟨CVar.Scoped.sub_ hx hy, by rw [CVar.val_sub_, hvx, hvy]⟩

attribute [irreducible] assertNotEqual

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
  rintro st ⟨hx, hy⟩
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]
    at hx hy
  obtain ⟨hx, hvx⟩ := hx
  obtain ⟨hy, hvy⟩ := hy
  have hsq : x.val st.env.get * x.val st.env.get = y.val st.env.get := by
    rw [hvx, hvy]; exact hxy
  exact ⟨PUnit.unit, st, Runs.addConstraint, fun hnv hle =>
    Sat.addConstraint ((LawfulBasicSystem.holds_square _ _ _).mpr
      (by rw [CVar.val_of_le hle hx, CVar.val_of_le hle hy]; exact hsq)), trivial⟩

attribute [irreducible] assertSquare

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

/-- `assert`'s completeness law: `assertEqual`'s, against the constant `1`. -/
theorem assert_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : BoolVar F) :
    Complete (fun st => CircuitType.ReadsAs (val := Bool) st v true) (assert (c := c) v)
      (fun _ _ => True) := by
  intro st hv
  simp only [CircuitType.ReadsAs, CircuitType.scoped_boolVar,
    CircuitType.reads_boolVar] at hv
  obtain ⟨hv, h1⟩ := hv
  refine assertEqual_complete (c := c) _ _ 1 st ?_
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]
  exact ⟨⟨hv, by simpa [bit] using h1⟩, ⟨trivial, rfl⟩⟩

attribute [irreducible] assert

/-! ## Bit sums -/

/-- Assert at least one bit is set: the bit-sum is nonzero — `assertNonZero`'s rows. -/
def assertAny [Field F] [DecidableEq F] [BasicSystem F c] (bs : List (BoolVar F)) :
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

/-- `assertAny`'s completeness law: where some scoped bit operand reads `1`, below the
characteristic, the bit-sum reads nonzero and `assertNonZero`'s law applies. -/
theorem assertAny_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F))
    (f : BoolVar F → Bool)
    (hchar : ∀ k : Nat, k ≤ bs.length → (k : F) = 0 → k = 0) :
    Complete (fun st => (∀ b ∈ bs, CircuitType.ReadsAs (val := Bool) st b (f b)) ∧ bs.any f = true)
      (assertAny (c := c) bs) (fun _ _ => True) := by
  rintro st ⟨hR, hany⟩
  obtain ⟨b₁, hb₁, hf₁⟩ := List.any_eq_true.mp hany
  have h : ∀ b ∈ bs, (↑b : CVar F).Scoped st ∧
      CircuitType.WellFormed (val := Bool) st.env.get b := fun b hb =>
    ⟨CircuitType.scoped_boolVar.mp (hR b hb).1, ⟨f b, (hR b hb).2⟩⟩
  have hv₁ : (↑b₁ : CVar F).val st.env.get = 1 := by
    rw [CircuitType.reads_boolVar.mp (hR b₁ hb₁).2, hf₁]
    rfl
  simp only [assertAny]
  have hsc : (sum (bs.map BoolVar.toCVar)).Scoped st :=
    CVar.Scoped.sum fun x hx => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact (h b hb).1
  refine assertNonZero_complete (c := c) _ ((sum (bs.map BoolVar.toCVar)).val st.env.get)
    ?_ st (by
      simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]
      exact ⟨hsc, trivial⟩)
  · have hbits' : ∀ x ∈ (bs.map BoolVar.toCVar).map (·.val st.env.get), x = 0 ∨ x = 1 := by
      intro x hx
      simp only [List.map_map, List.mem_map, Function.comp] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨bb, hbb⟩ := (h b hb).2
      rw [CircuitType.reads_boolVar.mp hbb]
      cases bb <;> simp [bit]
    rw [sum_eval, sum_of_bits _ hbits']
    generalize hL : (bs.map BoolVar.toCVar).map (·.val st.env.get) = L
    have hmem : (1 : F) ∈ L := by
      rw [← hL]
      simp only [List.map_map, List.mem_map, Function.comp]
      exact ⟨b₁, hb₁, hv₁⟩
    have hle : List.count (1 : F) L ≤ bs.length := by
      have := List.count_le_length (a := (1 : F)) (l := L)
      have hlen : L.length = bs.length := by rw [← hL]; simp
      omega
    intro hc
    exact absurd (hchar _ hle hc) (Nat.pos_iff_ne_zero.mp (List.count_pos_iff.mpr hmem))

attribute [irreducible] assertAny

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

/-- `assertExactlyOne`'s completeness law: where exactly one scoped bit operand reads `1`,
the bit-sum reads `1` and `assertEqual`'s law applies. -/
theorem assertExactlyOne_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F))
    (f : BoolVar F → Bool) :
    Complete (fun st => (∀ b ∈ bs, CircuitType.ReadsAs (val := Bool) st b (f b)) ∧
        (bs.map f).count true = 1)
      (assertExactlyOne (c := c) bs) (fun _ _ => True) := by
  rintro st ⟨hR, hcount⟩
  have h : ∀ b ∈ bs, (↑b : CVar F).Scoped st ∧
      CircuitType.WellFormed (val := Bool) st.env.get b := fun b hb =>
    ⟨CircuitType.scoped_boolVar.mp (hR b hb).1, ⟨f b, (hR b hb).2⟩⟩
  have hone : (bs.map fun (b : BoolVar F) => (↑b : CVar F).val st.env.get).count 1 = 1 := by
    rw [← hcount]
    simp only [List.count, List.countP_map]
    refine List.countP_congr fun b hb => ?_
    simp only [Function.comp_apply, beq_iff_eq,
      CircuitType.reads_boolVar.mp (hR b hb).2]
    cases f b <;> simp [bit]
  simp only [assertExactlyOne]
  have hsc : (sum (bs.map BoolVar.toCVar)).Scoped st :=
    CVar.Scoped.sum fun x hx => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact (h b hb).1
  have hval : (sum (bs.map BoolVar.toCVar)).val st.env.get = 1 := by
    have hbits' : ∀ x ∈ bs.map (fun (b : BoolVar F) => (↑b : CVar F).val st.env.get),
        x = 0 ∨ x = 1 := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      obtain ⟨bb, hbb⟩ := (h b hb).2
      rw [CircuitType.reads_boolVar.mp hbb]
      cases bb <;> simp [bit]
    rw [sum_eval, List.map_map]
    simp only [Function.comp_def]
    rw [sum_of_bits _ hbits', hone]
    simp
  exact assertEqual_complete (c := c) _ _ 1 st
    ⟨⟨CircuitType.scoped_fvar.mpr hsc, CircuitType.reads_fvar.mpr hval⟩,
      ⟨CircuitType.scoped_fvar.mpr trivial, CircuitType.reads_fvar.mpr rfl⟩⟩

attribute [irreducible] assertExactlyOne

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

/-- `assertAll`'s completeness law: where every scoped bit operand reads `1`, the bit-sum
reads the length and `assertEqual`'s law applies. -/
theorem assertAll_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (bs : List (BoolVar F))
    (f : BoolVar F → Bool) :
    Complete (fun st => (∀ b ∈ bs, CircuitType.ReadsAs (val := Bool) st b (f b)) ∧
      ∀ b ∈ bs, f b = true)
      (assertAll (c := c) bs) (fun _ _ => True) := by
  rintro st ⟨hR, hft⟩
  have h : ∀ b ∈ bs, (↑b : CVar F).Scoped st ∧
      CircuitType.WellFormed (val := Bool) st.env.get b := fun b hb =>
    ⟨CircuitType.scoped_boolVar.mp (hR b hb).1, ⟨f b, (hR b hb).2⟩⟩
  have hall : ∀ b ∈ bs, (↑b : CVar F).val st.env.get = 1 := fun b hb => by
    rw [CircuitType.reads_boolVar.mp (hR b hb).2, hft b hb]
    rfl
  simp only [assertAll]
  have hsc : (sum (bs.map BoolVar.toCVar)).Scoped st :=
    CVar.Scoped.sum fun x hx => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact (h b hb).1
  have hval : (sum (bs.map BoolVar.toCVar)).val st.env.get = (bs.length : F) := by
    have hbits' : ∀ x ∈ bs.map (fun (b : BoolVar F) => (↑b : CVar F).val st.env.get),
        x = 0 ∨ x = 1 := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      obtain ⟨bb, hbb⟩ := (h b hb).2
      rw [CircuitType.reads_boolVar.mp hbb]
      cases bb <;> simp [bit]
    rw [sum_eval, List.map_map]
    simp only [Function.comp_def]
    rw [sum_of_bits _ hbits', List.count_eq_length.mpr (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact (hall b hb).symm)]
    simp
  exact assertEqual_complete (c := c) _ _ (bs.length : F) st
    ⟨⟨CircuitType.scoped_fvar.mpr hsc, CircuitType.reads_fvar.mpr hval⟩,
      ⟨CircuitType.scoped_fvar.mpr trivial, CircuitType.reads_fvar.mpr rfl⟩⟩

attribute [irreducible] assertAll

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
/-- `assertEq`'s rows force the two readings equal. -/
@[spec] theorem assertEq_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] {val var : Type} [CircuitType F val var]
    (t e : var) {tv ev : val} (ht : CircuitType.Reads V t tv)
    (he : CircuitType.Reads V e ev) :
    ⦃⌜True⌝⦄
    assertEq (F := F) (c := Builder V c) (val := val) t e
    ⦃⇓ _ _ => ⌜tv = ev⌝⦄ := by
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
  have hfields : CircuitType.valueToFields (F := F) tv = CircuitType.valueToFields (F := F) ev := by
    rw [← ht, ← he]
    ext i hi
    simpa using hzip nv hsat ⟨i, hi⟩
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
  intro st hst
  obtain ⟨_, st₁, hrun, hsat, -⟩ :=
    zipWithVecM_complete (c := c) assertEqual (CircuitType.varToFields (val := val) t)
      (CircuitType.varToFields (val := val) e)
      (fun st => CircuitType.Scoped (val := val) st t ∧ CircuitType.Scoped (val := val) st e ∧
        CircuitType.Reads st.env.get t a ∧ CircuitType.Reads st.env.get e a)
      (fun _ _ _ => True)
      (fun {_ _} hnv hle h => ⟨CircuitType.Scoped.mono hnv h.1,
        CircuitType.Scoped.mono hnv h.2.1, h.2.2.1.of_le h.1 hle, h.2.2.2.of_le h.2.1 hle⟩)
      (fun _ {_ _ _} _ _ _ => trivial)
      (fun i st' h => by
        have h₁ := congrArg (fun v : Vector F (CircuitType.size F val) => v[i.val]) h.2.2.1
        have h₂ := congrArg (fun v : Vector F (CircuitType.size F val) => v[i.val]) h.2.2.2
        simp only [getElem_mapVec] at h₁ h₂
        exact assertEqual_complete (c := c) _ _
          ((CircuitType.valueToFields (F := F) a)[i.val]) st'
          ⟨⟨CircuitType.scoped_fvar.mpr (h.1 _ (by simp)),
              CircuitType.reads_fvar.mpr h₁⟩,
            ⟨CircuitType.scoped_fvar.mpr (h.2.1 _ (by simp)),
              CircuitType.reads_fvar.mpr h₂⟩⟩)
      st hst
  exact ⟨PUnit.unit, st₁, hrun.bind rfl, fun hnv hle =>
    Sat.bind hrun (hsat hnv hle) Sat.pure, trivial⟩

end Snarky
