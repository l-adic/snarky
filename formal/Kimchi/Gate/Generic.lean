import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # The kimchi generic gate, over a real 15-column row.

The single-row generic identity

    `cl·w0 + cr·w1 + co·w2 + m·(w0·w1) + c = 0`

reads the first three registers of the row (`w0,w1,w2`) and the five coefficients
`[cl, cr, co, m, c]` (the dump's coefficient order — a pure copy row is `[1,0,0,0,0]`).

`eval` is the polynomial's value; `holds`/`ok` are the `= 0` relation and its decidable
checker. The public-input contribution is *not* folded in here — that is added at the
circuit level (`Kimchi.Circuit`), since it comes from the protocol's public-input
polynomial, not the gate's coefficients. -/

namespace Kimchi.Gate

/-- A row is the 15 registers of one circuit row. We keep it an `Array` (totality via
    `getD`) rather than a length-indexed vector to avoid index side-conditions in proofs;
    the dump always supplies 15 entries. -/
abbrev Row (F : Type*) := Array F

namespace Generic

variable {F : Type*}

/-- The generic gate's polynomial value `cl·w0 + cr·w1 + co·w2 + m·(w0·w1) + c`. -/
def eval [CommRing F] (coeffs : Array F) (row : Row F) : F :=
  coeffs.getD 0 0 * row.getD 0 0
    + coeffs.getD 1 0 * row.getD 1 0
    + coeffs.getD 2 0 * row.getD 2 0
    + coeffs.getD 3 0 * (row.getD 0 0 * row.getD 1 0)
    + coeffs.getD 4 0

/-- Relational spec for one generic gate (no public-input term): the value is `0`. -/
def holds [CommRing F] (coeffs : Array F) (row : Row F) : Prop :=
  eval coeffs row = 0

/-- Executable checker for one generic gate. -/
def ok [CommRing F] [DecidableEq F] (coeffs : Array F) (row : Row F) : Bool :=
  eval coeffs row == 0

theorem ok_iff [CommRing F] [DecidableEq F] (coeffs : Array F) (row : Row F) :
    ok coeffs row = true ↔ holds coeffs row := by
  simp [ok, holds]

end Generic

/-! ## A concrete, runnable example over `ZMod 17`: `w0 * w1 = w2`. -/

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- `w0 · w1 = w2`, encoded as `1·w2 + (-1)·(w0·w1) = 0`: coeffs `[cl,cr,co,m,c] = [0,0,1,-1,0]`. -/
def mulCoeffs : Array (ZMod 17) := #[0, 0, 1, -1, 0]

def egGood : Row (ZMod 17) := #[3, 4, 12]   -- 3 * 4 = 12  ✓
def egBad  : Row (ZMod 17) := #[3, 4, 13]   -- 3 * 4 ≠ 13  ✗

#eval Generic.ok mulCoeffs egGood   -- true
#eval Generic.ok mulCoeffs egBad    -- false

example : Generic.holds mulCoeffs egGood := by rw [← Generic.ok_iff]; rfl
example : ¬ Generic.holds mulCoeffs egBad := by rw [← Generic.ok_iff]; decide

end Kimchi.Gate
