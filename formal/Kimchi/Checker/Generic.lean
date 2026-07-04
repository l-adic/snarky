import Kimchi.Checker.Row

/-! # The kimchi generic gate, over a real 15-column row (checker model).

The single-row generic identity

    `cl·w0 + cr·w1 + co·w2 + m·(w0·w1) + c = 0`

reads the first three registers of the row (`w0,w1,w2`) and the five coefficients
`[cl, cr, co, m, c]` (the dump's coefficient order — a pure copy row is `[1,0,0,0,0]`).

`eval` is the polynomial's value; `holds`/`ok` are the `= 0` relation and its decidable
checker. The public-input contribution is *not* folded in here — that is added at the
circuit level (`Kimchi.Circuit`), since it comes from the protocol's public-input
polynomial, not the gate's coefficients.

This is the **checker-facing**, row/coefficient-array model used by `Kimchi.Circuit`; the
soundness-oriented, structured generic gate lives separately at `Kimchi.Gate.Generic`. -/

namespace Kimchi.Checker.Generic

open Kimchi.Gate (Row)

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

end Kimchi.Checker.Generic
