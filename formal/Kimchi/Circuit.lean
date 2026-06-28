import Kimchi.Checker.Generic
import Kimchi.Gate.AddComplete
import Kimchi.Checker.VarBaseMul
import Kimchi.Gate.EndoMul
import Kimchi.Checker.EndoScalar
import Kimchi.Gate.Poseidon

/-!
# The compiled plonkish constraint system: ingest, satisfy, check

This is the faithful Lean model of the gate list a snarky circuit elaborates to — the
exact object kimchi proves about, and the object the PureScript dumpers emit. A
`Circuit` is rows of `(kind, coeffs, wires)`; a `Witness` is rows of 15 registers.

`Satisfies c w pub` is the **witness-satisfaction relation**: every row's gate identity
holds, *and* every wired cell equals the value at its permutation image (the copy
constraints). `check` is the executable decision procedure, and `check_iff` proves it
faithful. Running `check` over `ZMod p` uses real (compiled) field arithmetic — never
`decide`, which cannot evaluate a 255-bit field equality in the kernel.

## Two modelling notes (where the model is faithful but not literal)

* **Public input.** The first `publicInputSize` rows are `Generic` gates with `cl = 1`;
  kimchi's public-input polynomial subtracts `pub[r]` from that row's constraint. We fold
  that in as `Generic.eval coeffs (row r) = pubTerm r` (`pubTerm r = pub[r]` on those rows,
  else `0`). So a public row asserts `w[r][0] = pub[r]`. This is the one place a row's
  identity is not determined by its coefficients alone.
* **Permutation.** `copyHolds` models the *extensional* consequence of kimchi's permutation
  argument — each wired cell holds the same value as the cell its wire points to — not the
  grand-product polynomial. That polynomial is a protocol/completeness device; the value
  equalities are exactly what soundness consumes.
-/

-- The structure `Circuit` lives in namespace `Kimchi.Circuit` (giving `Kimchi.Circuit.Circuit`);
-- the repeated component is intentional and reads naturally at use sites.
set_option linter.dupNamespace false

namespace Kimchi.Circuit

open Kimchi.Gate

/-- The gate kinds the dump can carry (the `typ` field). -/
inductive GateKind
  | generic | zero | poseidon | completeAdd | varBaseMul | endoMul | endoMulScalar
deriving DecidableEq, Repr

/-- A permutation cell: `(row, col)`. -/
abbrev Cell := Nat × Nat

/-- One dumped gate/row: its kind, its coefficient row, and its 7 permutation wires
    (the targets for columns 0–6). -/
structure Gate (F : Type*) where
  kind : GateKind
  coeffs : Array F
  wires : Array Cell
deriving Repr

/-- A dumped circuit: the public-input count and the gate rows. -/
structure Circuit (F : Type*) where
  publicInputSize : Nat
  gates : Array (Gate F)
deriving Repr

/-- A witness: one 15-register `Row` per circuit row (row-major; the column-major dump
    is transposed once at the JSON boundary). -/
structure Witness (F : Type*) where
  rows : Array (Row F)
deriving Repr

variable {F : Type*}

/-- The all-`zero` gate, used as the out-of-range default (keeps every lookup total). -/
def defaultGate : Gate F := ⟨.zero, #[], #[]⟩

/-- The gate at row `r` (out-of-range → `defaultGate`). -/
def Circuit.gateAt (c : Circuit F) (r : Nat) : Gate F := c.gates.getD r defaultGate

/-- The full register row at index `r` (out-of-range → empty row, reads as `0`). -/
def Witness.row (w : Witness F) (r : Nat) : Row F := w.rows.getD r #[]

/-- The value at cell `(row, col)` (out-of-range → `0`). -/
def Witness.cell [Zero F] (w : Witness F) (c : Cell) : F := (w.row c.1).getD c.2 0

/-- The public-input term subtracted at row `r`: `pub[r]` for the first
    `publicInputSize` rows, else `0`. -/
def Circuit.pubTerm [Zero F] (c : Circuit F) (pub : Array F) (r : Nat) : F :=
  if r < c.publicInputSize then pub.getD r 0 else 0

/-! ## Per-row gate identities (the dispatch over all 7 kinds). -/

/-- RELATIONAL: row `g`'s gate identity holds for register rows `curr`/`next`, with the
    public-input term `pubr` folded into the generic case. `zero` is vacuous; `completeAdd`
    delegates to the proven `AddComplete.Holds`; the four custom gates are currently
    `True`-stubbed (their constraint polynomials are not yet transcribed). -/
def rowHolds [CommRing F] (g : Gate F) (curr next : Row F) (pubr : F) : Prop :=
  match g.kind with
  | .generic       => Checker.Generic.eval g.coeffs curr = pubr
  | .zero          => True
  | .completeAdd   => AddComplete.Holds (AddComplete.ofRow curr)
  | .poseidon      => Poseidon.holds g.coeffs curr next
  | .varBaseMul    => Checker.VarBaseMul.holds curr next
  | .endoMul       => EndoMul.holds curr next
  | .endoMulScalar => Checker.EndoScalar.holds curr next

/-- EXECUTABLE mirror of `rowHolds`. -/
def rowOk [CommRing F] [DecidableEq F] (g : Gate F) (curr next : Row F) (pubr : F) : Bool :=
  match g.kind with
  | .generic       => Checker.Generic.eval g.coeffs curr == pubr
  | .zero          => true
  | .completeAdd   => AddComplete.ok (AddComplete.ofRow curr)
  | .poseidon      => Poseidon.ok g.coeffs curr next
  | .varBaseMul    => Checker.VarBaseMul.ok curr next
  | .endoMul       => EndoMul.ok curr next
  | .endoMulScalar => Checker.EndoScalar.ok curr next

theorem rowOk_iff [CommRing F] [DecidableEq F] (g : Gate F) (curr next : Row F) (pubr : F) :
    rowOk g curr next pubr = true ↔ rowHolds g curr next pubr := by
  cases h : g.kind <;>
    simp [rowOk, rowHolds, h, AddComplete.ok_iff, Checker.VarBaseMul.ok_iff, EndoMul.ok_iff,
      Checker.EndoScalar.ok_iff, Poseidon.ok_iff]

/-- BRIDGE: on a `completeAdd` row, the dispatcher's identity *is* the proven
    `AddComplete.Holds` of the witness extracted from the row's cells — so the entire
    soundness suite in `Gate/AddComplete.lean` (`sound`, …) applies verbatim. -/
theorem rowHolds_completeAdd [CommRing F] (g : Gate F) (curr next : Row F) (pubr : F)
    (h : g.kind = .completeAdd) :
    rowHolds g curr next pubr ↔ AddComplete.Holds (AddComplete.ofRow curr) := by
  simp [rowHolds, h]

/-! ## The three obligations: gate identities, copy constraints, and their conjunction. -/

/-- Every row's gate identity holds (public-input term folded in). -/
def gatesHold [CommRing F] (c : Circuit F) (w : Witness F) (pub : Array F) : Prop :=
  ∀ r, r < c.gates.size →
    rowHolds (c.gateAt r) (w.row r) (w.row (r + 1)) (c.pubTerm pub r)

/-- Every wired cell (cols 0–6) equals the value at the cell its wire points to. A missing
    wire defaults to a self-loop `(r, k)`, which is vacuous. -/
def copyHolds [Zero F] (c : Circuit F) (w : Witness F) : Prop :=
  ∀ r, r < c.gates.size → ∀ k, k < 7 →
    w.cell (r, k) = w.cell ((c.gateAt r).wires.getD k (r, k))

/-- The witness satisfies the circuit on public inputs `pub`. -/
def Satisfies [CommRing F] (c : Circuit F) (w : Witness F) (pub : Array F) : Prop :=
  gatesHold c w pub ∧ copyHolds c w

/-- The executable verified checker. -/
def check [CommRing F] [DecidableEq F] (c : Circuit F) (w : Witness F) (pub : Array F) : Bool :=
  (List.range c.gates.size).all (fun r =>
      rowOk (c.gateAt r) (w.row r) (w.row (r + 1)) (c.pubTerm pub r))
  && (List.range c.gates.size).all (fun r =>
      (List.range 7).all (fun k =>
        w.cell (r, k) == w.cell ((c.gateAt r).wires.getD k (r, k))))

/-- REFLECTION: the executable checker decides the satisfaction relation faithfully.
    Proven symbolically (no `decide`), so it holds at the 255-bit Pasta field. -/
theorem check_iff [CommRing F] [DecidableEq F]
    (c : Circuit F) (w : Witness F) (pub : Array F) :
    check c w pub = true ↔ Satisfies c w pub := by
  simp only [check, Satisfies, gatesHold, copyHolds, Bool.and_eq_true,
    List.all_eq_true, List.mem_range, rowOk_iff, beq_iff_eq]

end Kimchi.Circuit
