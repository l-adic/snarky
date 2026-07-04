import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # `Row`: one circuit row, as consumed by the verified checker.

The ingested-constraint-system checker (`Kimchi.Circuit`) and its row-level gate models
(`Kimchi.Checker.*`, plus the custom gates `Kimchi.Gate.{EndoMul,EndoScalar,Poseidon}`)
work over a `Row` — the 15 registers of one circuit row. We keep it an `Array` (totality
via `getD`) rather than a length-indexed vector to avoid index side-conditions in proofs;
the dump always supplies 15 entries.

This module owns the `Row` abbreviation so the checker layer no longer threads it through
the generic-gate file — `Kimchi.Gate.Generic` is now the soundness-oriented model and does
not define `Row`. -/

namespace Kimchi.Gate

/-- A row is the 15 registers of one circuit row (`Array` for totality via `getD`). -/
abbrev Row (F : Type*) := Array F

end Kimchi.Gate
