import Mathlib.Data.List.Forall2
import Snarky.DSL.Bits
import Snarky.DSL.Boolean

/-!
# The canonical bit decomposition

Port of OCaml `Field.Checked.unpack_full` / `lt_bitstring_value` (snark0.ml, the base-DSL
checked runtime). Plain `unpack` (DSL/Bits.lean) pins the bits' weighted sum to the
operand only modulo the field, so any representative's decomposition satisfies its rows;
locking the decomposition to the canonical representative takes a further comparison
against the modulus.

`modBitsMsb` is the modulus as an MSB-first bit pattern; `ltBitstringValue` compares an
MSB-first bit vector against it, descending to the least significant bit and combining on
the way back out: at a `1` bit of the pattern the operand may drop below (`or`), at a `0`
bit it must stay equal (`and`). `ltPure` is the comparison's value-level mirror.

Deviation from the PS original (`packages/schnorr/src/Snarky/Circuit/Schnorr/
UnpackFull.purs`): PS builds the comparison as a `Binary` tree, regroups runs into N-ary
nodes evaluated with the sum-based `allBools`/`anyBools` constraint-savers, and
short-circuits the last one and two bits. This is the uniform binary recursion — the same
value, more rows.
-/

namespace Snarky

variable {F c : Type}

/-! ## The value layer -/

/-- MSB-first bit decomposition of `m` at width `n` (PS `modulusBitsMsb`). -/
def modBitsMsb (m n : ℕ) : List Bool :=
  ((List.range n).map m.testBit).reverse

/-- The pattern has the requested width. -/
theorem modBitsMsb_length (m n : ℕ) : (modBitsMsb m n).length = n := by
  simp [modBitsMsb]

/-- The comparison's value-level mirror: MSB-first `xs < ys`, `false` on any length
mismatch. -/
def ltPure : List Bool → List Bool → Bool
  | x :: xs, true :: ys => !x || ltPure xs ys
  | x :: xs, false :: ys => !x && ltPure xs ys
  | _, _ => false

/-! ## The comparison -/

/-- `xs < ys` for an MSB-first bit vector against a constant pattern (OCaml
`lt_bitstring_value`). -/
def ltBitstringValue [Field F] [DecidableEq F] [BasicSystem F c] :
    List (BoolVar F) → List Bool → CircuitM F c (BoolVar F)
  | x :: xs, true :: ys => do
    let r ← ltBitstringValue xs ys
    Snarky.or (Snarky.not x) r
  | x :: xs, false :: ys => do
    let r ← ltBitstringValue xs ys
    Snarky.and (Snarky.not x) r
  | _, _ => pure false_

/-- Outside the two matching shapes the comparison is `false`: the pattern is exhausted,
or the operands are and with them the bits they read as. -/
private theorem ltPure_eq_false {α : Type} {R : α → Bool → Prop} {xs : List α}
    {ys bs : List Bool}
    (h1 : ∀ (x : α) (xs' : List α) (ys' : List Bool), xs = x :: xs' → ys = true :: ys' → False)
    (h2 : ∀ (x : α) (xs' : List α) (ys' : List Bool), xs = x :: xs' → ys = false :: ys' → False)
    (hfa : List.Forall₂ R xs bs) : ltPure bs ys = false := by
  cases hfa with
  | nil => cases ys <;> rfl
  | cons _ _ =>
    rename_i x _ xs' _ _ _
    cases ys with
    | nil => rfl
    | cons y ys' =>
      cases y
      · exact (h2 x xs' ys' rfl rfl).elim
      · exact (h1 x xs' ys' rfl rfl).elim

open Std.Do in
/-- The comparison reads as `ltPure` of the operands' bits against the pattern. -/
@[spec] theorem ltBitstringValue_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (xs : List (BoolVar F)) (ys : List Bool) :
    ⦃⌜True⌝⦄
    ltBitstringValue (c := Builder V c) xs ys
    ⦃⇓ r _ => ⌜∀ bs : List Bool,
        List.Forall₂ (fun (x : BoolVar F) (b : Bool) => (↑x : CVar F).val V = bit b) xs bs →
        (↑r : CVar F).val V = bit (ltPure bs ys)⌝⦄ := by
  induction xs, ys using ltBitstringValue.induct with
  | case1 x xs ys ih =>
    simp only [ltBitstringValue]
    mvcgen [ih]
    rename_i _ _ _ hr _ _
    intro hor bs hbs
    cases hbs with
    | cons hx htl =>
      rename_i b bs'
      rw [hor (!b) (ltPure bs' ys) (not_val hx) (hr bs' htl)]
      simp [ltPure]
  | case2 x xs ys ih =>
    simp only [ltBitstringValue]
    mvcgen [ih]
    rename_i _ _ _ hr _ _
    intro hand bs hbs
    cases hbs with
    | cons hx htl =>
      rename_i b bs'
      rw [hand (!b) (ltPure bs' ys) (not_val hx) (hr bs' htl)]
      simp [ltPure]
  | case3 xs ys h1 h2 =>
    simp only [ltBitstringValue]
    mvcgen
    intro bs hbs
    rw [ltPure_eq_false h1 h2 hbs]
    simp [bit]

/-- The comparison's completeness law: on operands reading as `bs`, the run succeeds and
the result reads as `ltPure bs ys`. -/
theorem ltBitstringValue_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c]
    (xs : List (BoolVar F)) (ys bs : List Bool) :
    Complete (F := F) (c := c)
      (fun st => List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
        CircuitType.ReadsAs (val := Bool) st x b) xs bs)
      (ltBitstringValue (c := c) xs ys)
      (fun r st' => CircuitType.ReadsAs (val := Bool) st' r (ltPure bs ys)) := by
  induction xs, ys using ltBitstringValue.induct generalizing bs with
  | case1 x xs ys ih =>
    intro st hfa
    simp only [ltBitstringValue]
    cases hfa with
    | cons hx htl =>
      rename_i b bs'
      obtain ⟨r, st₁, hrun₁, hsat₁, hr⟩ := ih bs' st htl
      have hx₁ := hx.mono hrun₁.nv_le hrun₁.le
      obtain ⟨out, st₂, hrun₂, hsat₂, hout⟩ :=
        Snarky.or_complete (c := c) (Snarky.not x) r (!b) (ltPure bs' ys) st₁
          ⟨⟨CircuitType.scoped_boolVar.mpr
              (not_scoped (CircuitType.scoped_boolVar.mp hx₁.1)),
            CircuitType.reads_boolVar.mpr
              (not_val (CircuitType.reads_boolVar.mp hx₁.2))⟩, hr⟩
      refine ⟨out, st₂, hrun₁.bind hrun₂, ?_, ?_⟩
      · intro stf hnv hle
        exact Sat.bind hrun₁ (hsat₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle))
          (hsat₂ hnv hle)
      · simpa [ltPure] using hout
  | case2 x xs ys ih =>
    intro st hfa
    simp only [ltBitstringValue]
    cases hfa with
    | cons hx htl =>
      rename_i b bs'
      obtain ⟨r, st₁, hrun₁, hsat₁, hr⟩ := ih bs' st htl
      have hx₁ := hx.mono hrun₁.nv_le hrun₁.le
      obtain ⟨out, st₂, hrun₂, hsat₂, hout⟩ :=
        Snarky.and_complete (c := c) (Snarky.not x) r (!b) (ltPure bs' ys) st₁
          ⟨⟨CircuitType.scoped_boolVar.mpr
              (not_scoped (CircuitType.scoped_boolVar.mp hx₁.1)),
            CircuitType.reads_boolVar.mpr
              (not_val (CircuitType.reads_boolVar.mp hx₁.2))⟩, hr⟩
      refine ⟨out, st₂, hrun₁.bind hrun₂, ?_, ?_⟩
      · intro stf hnv hle
        exact Sat.bind hrun₁ (hsat₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle))
          (hsat₂ hnv hle)
      · simpa [ltPure] using hout
  | case3 xs ys h1 h2 =>
    intro st hfa
    simp only [ltBitstringValue]
    refine ⟨false_, st, rfl, fun _ _ => Sat.pure, ?_⟩
    rw [ltPure_eq_false h1 h2 hfa]
    exact ⟨CircuitType.scoped_boolVar.mpr (false_scoped st),
      CircuitType.reads_boolVar.mpr (by simp [bit])⟩

attribute [irreducible] ltBitstringValue

end Snarky
