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
