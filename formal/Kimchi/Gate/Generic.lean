import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # The generic gate `cl·vl + cr·vr + co·vo + m·(vl·vr) + c = 0`, the "all gates
    hold" relation, and the executable checker that decides it. -/

namespace Kimchi.Gate

variable {F : Type*} [Field F]

/-- A variable index into the assignment. -/
abbrev Variable := Nat

/-- A witness: a value per variable. -/
abbrev Assignment (F : Type*) := Array F

/-- Read a variable's value; out-of-range as 0 for totality. -/
def Assignment.get (a : Assignment F) (v : Variable) : F := a.getD v 0

/-- An optional slot's value: an absent (`none`) slot contributes 0. -/
def slot (a : Assignment F) : Option Variable → F
  | none   => 0
  | some v => a.get v

/-- One generic gate: `cl·vl + cr·vr + co·vo + m·(vl·vr) + c = 0`. -/
structure Generic (F : Type*) where
  cl : F
  vl : Option Variable
  cr : F
  vr : Option Variable
  co : F
  vo : Option Variable
  m  : F
  c  : F

/-- Relational spec for one generic gate — a `Prop`. -/
def Generic.holds (g : Generic F) (a : Assignment F) : Prop :=
  g.cl * slot a g.vl + g.cr * slot a g.vr + g.co * slot a g.vo
    + g.m * (slot a g.vl * slot a g.vr) + g.c = 0

/-- Executable checker for one generic gate — a `Bool`. -/
def Generic.ok [DecidableEq F] (g : Generic F) (a : Assignment F) : Bool :=
  (g.cl * slot a g.vl + g.cr * slot a g.vr + g.co * slot a g.vo
    + g.m * (slot a g.vl * slot a g.vr) + g.c) == 0

def Satisfies (gs : List (Generic F)) (a : Assignment F) : Prop :=
  ∀ g ∈ gs, g.holds a

def satisfies [DecidableEq F] (gs : List (Generic F)) (a : Assignment F) : Bool :=
  gs.all (·.ok a)

theorem Generic.ok_iff [DecidableEq F] (g : Generic F) (a : Assignment F) :
    g.ok a = true ↔ g.holds a := by
  simp [Generic.ok, Generic.holds]

/-- **Soundness:** a witness accepted by the executable checker satisfies the gate's linear
    relation. (The generic gate is a decidable predicate, so soundness is one direction of
    `ok_iff`; the other is `complete`.) -/
theorem Generic.sound [DecidableEq F] (g : Generic F) (a : Assignment F) :
    g.ok a = true → g.holds a := (g.ok_iff a).mp

/-- **Completeness:** any witness satisfying the gate's linear relation is accepted by the
    executable checker. (The converse direction of `ok_iff`.) -/
theorem Generic.complete [DecidableEq F] (g : Generic F) (a : Assignment F) :
    g.holds a → g.ok a = true := (g.ok_iff a).mpr

theorem satisfies_iff [DecidableEq F] (gs : List (Generic F)) (a : Assignment F) :
    satisfies gs a = true ↔ Satisfies gs a := by
  simp [satisfies, Satisfies, List.all_eq_true, Generic.ok_iff]

/-! ## The double generic gate row

kimchi's generic gate row (`generic.rs`) packs **two** generic gates: the first on registers
`w 0, w 1, w 2` with coefficients `q 0 … q 4`, the second on `w 3, w 4, w 5` with `q 5 … q 9`
(coefficient order per gate: `l, r, o, m, c`). A row is 15 witness cells `w : Fin 15 → F` and
15 coefficient cells `q : Fin 15 → F` (`q 10 … q 14` unused). The two halves are literal
`Generic` gates over the row's first six cells viewed as an `Assignment`. -/

/-- The first generic gate of a double generic row: coefficients `q 0 … q 4`, registers at
assignment slots `0, 1, 2` (row cells `w 0, w 1, w 2`). -/
def DoubleGeneric.fst (q : Fin 15 → F) : Generic F :=
  { cl := q 0, vl := some 0, cr := q 1, vr := some 1, co := q 2, vo := some 2
  , m := q 3, c := q 4 }

/-- The second generic gate of a double generic row: coefficients `q 5 … q 9`, registers at
assignment slots `3, 4, 5` (row cells `w 3, w 4, w 5`). -/
def DoubleGeneric.snd (q : Fin 15 → F) : Generic F :=
  { cl := q 5, vl := some 3, cr := q 6, vr := some 4, co := q 7, vo := some 5
  , m := q 8, c := q 9 }

/-- The row's first six witness cells as an `Assignment` (the registers both halves read). -/
def DoubleGeneric.registers (w : Fin 15 → F) : Assignment F :=
  #[w 0, w 1, w 2, w 3, w 4, w 5]

/-- **The double generic gate holds at a row**: both packed `Generic` gates hold on the row's
registers. This is the row-level predicate the polynomial layer (`Kimchi/Quotient`) lifts. -/
def DoubleGeneric.Holds (q w : Fin 15 → F) : Prop :=
  (DoubleGeneric.fst q).holds (DoubleGeneric.registers w)
    ∧ (DoubleGeneric.snd q).holds (DoubleGeneric.registers w)

/-- `DoubleGeneric.Holds` unfolded to the two raw cell equations of `generic.rs` (l.245–250):
`q₀w₀ + q₁w₁ + q₂w₂ + q₃(w₀w₁) + q₄ = 0` and `q₅w₃ + q₆w₄ + q₇w₅ + q₈(w₃w₄) + q₉ = 0`. -/
theorem DoubleGeneric.holds_iff (q w : Fin 15 → F) :
    DoubleGeneric.Holds q w
      ↔ (q 0 * w 0 + q 1 * w 1 + q 2 * w 2 + q 3 * (w 0 * w 1) + q 4 = 0
          ∧ q 5 * w 3 + q 6 * w 4 + q 7 * w 5 + q 8 * (w 3 * w 4) + q 9 = 0) := by
  simp [DoubleGeneric.Holds, DoubleGeneric.fst, DoubleGeneric.snd, DoubleGeneric.registers,
    Generic.holds, slot, Assignment.get]

/-- Example: `w0 * w1 = w2`, as `1·w2 + (-1)·(w0·w1) = 0`, over the field `ZMod 17`. -/
instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

def mulGate : Generic (ZMod 17) :=
  { cl := 0, vl := some 0
  , cr := 0, vr := some 1
  , co := 1, vo := some 2
  , m  := -1
  , c  := 0 }

def egGood : Assignment (ZMod 17) := #[3, 4, 12]   -- 3 * 4 = 12  ✓
def egBad  : Assignment (ZMod 17) := #[3, 4, 13]   -- 3 * 4 ≠ 13  ✗

#eval satisfies [mulGate] egGood   -- true
#eval satisfies [mulGate] egBad    -- false

example : Satisfies [mulGate] egGood := by rw [← satisfies_iff]; decide
example : ¬ Satisfies [mulGate] egBad := by rw [← satisfies_iff]; decide

end Kimchi.Gate
