import Kimchi.Checker.Generic
import Kimchi.Gate.AddComplete
import Kimchi.Checker.VarBaseMul
import Kimchi.Checker.EndoMul
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
    `True`-stubbed (their constraint polynomials are not yet transcribed). The generic case
    checks **both** gates of kimchi's double generic row (`eval` on cols 0–2, `eval2` on
    cols 3–5; a 5-coefficient row leaves the second half vacuous). -/
def rowHolds [CommRing F] (g : Gate F) (curr next : Row F) (pubr : F) : Prop :=
  match g.kind with
  | .generic       => Checker.Generic.eval g.coeffs curr = pubr
                        ∧ Checker.Generic.eval2 g.coeffs curr = 0
  | .zero          => True
  | .completeAdd   => AddComplete.Holds (AddComplete.ofRow curr)
  | .poseidon      => Poseidon.holds g.coeffs curr next
  | .varBaseMul    => Checker.VarBaseMul.holds curr next
  | .endoMul       => Checker.EndoMul.holds curr next
  | .endoMulScalar => Checker.EndoScalar.holds curr next

/-- EXECUTABLE mirror of `rowHolds`. -/
def rowOk [CommRing F] [DecidableEq F] (g : Gate F) (curr next : Row F) (pubr : F) : Bool :=
  match g.kind with
  | .generic       => (Checker.Generic.eval g.coeffs curr == pubr)
                        && (Checker.Generic.eval2 g.coeffs curr == 0)
  | .zero          => true
  | .completeAdd   => AddComplete.ok (AddComplete.ofRow curr)
  | .poseidon      => Poseidon.ok g.coeffs curr next
  | .varBaseMul    => Checker.VarBaseMul.ok curr next
  | .endoMul       => Checker.EndoMul.ok curr next
  | .endoMulScalar => Checker.EndoScalar.ok curr next

theorem rowOk_iff [CommRing F] [DecidableEq F] (g : Gate F) (curr next : Row F) (pubr : F) :
    rowOk g curr next pubr = true ↔ rowHolds g curr next pubr := by
  cases h : g.kind <;>
    simp [rowOk, rowHolds, h, AddComplete.ok_iff, Checker.VarBaseMul.ok_iff, Checker.EndoMul.ok_iff,
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

/-! ## Extending a circuit: the `append` combinator

Every reconstructed sub-circuit so far is "a proven block plus a few extra rows" (setup pins, an
init doubling, a trailing combine gate). `Circuit.append` is that pattern once: appended rows leave
the prefix's gates, wires, and public-input term untouched, so a `Satisfies` of the extension
*projects* onto the prefix (`Satisfies.of_append`) — the sub-circuit's own composition theorem then
applies verbatim, and only the appended rows need bespoke reasoning. -/

/-- `Array.ofFn` lookup below its length — the workhorse for reducing `gateAt`/`wires` lookups on
    reconstructed circuits (shared here; previously re-derived per file). -/
theorem getD_ofFn_lt {α} (n : ℕ) (f : Fin n → α) (r : ℕ) (d : α) (h : r < n) :
    (Array.ofFn f).getD r d = f ⟨r, h⟩ := by
  rw [Array.getD, dif_pos (by simpa using h)]; simp [Array.getElem_ofFn]

/-- Extend a circuit with extra gate rows (same public-input prefix). -/
def Circuit.append (c : Circuit F) (gs : Array (Gate F)) : Circuit F :=
  { publicInputSize := c.publicInputSize, gates := c.gates ++ gs }

@[simp] theorem Circuit.size_append (c : Circuit F) (gs : Array (Gate F)) :
    (c.append gs).gates.size = c.gates.size + gs.size := by
  simp [Circuit.append]

/-- Rows below the prefix length are the prefix's gates, unchanged. -/
theorem Circuit.gateAt_append_left (c : Circuit F) (gs : Array (Gate F)) (r : ℕ)
    (hr : r < c.gates.size) : (c.append gs).gateAt r = c.gateAt r := by
  rw [Circuit.gateAt, Circuit.gateAt, Circuit.append,
    Array.getD, dif_pos (by rw [Array.size_append]; omega), Array.getD, dif_pos hr]
  exact Array.getElem_append_left hr

/-- Row `c.gates.size + j` is the `j`-th appended gate. -/
theorem Circuit.gateAt_append_right (c : Circuit F) (gs : Array (Gate F)) (j : ℕ)
    (hj : j < gs.size) : (c.append gs).gateAt (c.gates.size + j) = gs[j] := by
  rw [Circuit.gateAt, Circuit.append, Array.getD,
    dif_pos (by rw [Array.size_append]; omega)]
  simp

/-- A witness satisfying the extension satisfies the prefix (public-input term unchanged; the
    appended rows can only add obligations). -/
theorem Satisfies.of_append [CommRing F] {c : Circuit F} {gs : Array (Gate F)} {w : Witness F}
    {pub : Array F} (h : Satisfies (c.append gs) w pub) : Satisfies c w pub := by
  obtain ⟨hg, hc⟩ := h
  refine ⟨fun r hr => ?_, fun r hr k hk => ?_⟩
  · have hh := hg r (by rw [Circuit.size_append]; omega)
    rwa [Circuit.gateAt_append_left c gs r hr] at hh
  · have hh := hc r (by rw [Circuit.size_append]; omega) k hk
    rwa [Circuit.gateAt_append_left c gs r hr] at hh

/-! ## Embedding a block at a row offset

A multi-block circuit places a proven block (a `vbmCircuit`, an `emCircuit`, …) at rows
`[k, k + size)` of a larger host — with the block's internal copy-wires shifted by `k`. The host's
`Satisfies` then *projects* onto the block against the row-shifted view of the witness
(`Satisfies.of_embed`), so the block's composition theorem applies verbatim at offset `k`. This is
the general form of `append` (which is the case `k = c.gates.size` of a suffix block), and the
enabler for reconstructing dumped circuits whole — setup rows first, chain in the middle. -/

/-- Shift a gate's copy-wires `k` rows deeper. Kind and coefficients unchanged, so the gate
    identity (`rowHolds`) is untouched — only the permutation targets move. -/
def Gate.shiftWires (k : ℕ) (g : Gate F) : Gate F :=
  { g with wires := g.wires.map fun c => (k + c.1, c.2) }

/-- The row-shifted view of a witness: `(w.shift k).row i = w.row (k + i)`. -/
def Witness.shift (k : ℕ) (w : Witness F) : Witness F :=
  ⟨Array.ofFn (n := w.rows.size - k) fun i => w.row (k + i.val)⟩

theorem Witness.row_shift (w : Witness F) (k i : ℕ) : (w.shift k).row i = w.row (k + i) := by
  by_cases h : i < w.rows.size - k
  · rw [Witness.row, Witness.shift, getD_ofFn_lt _ _ _ _ h]
  · rw [Witness.row, Witness.shift, Array.getD, dif_neg (by simpa using h),
      Witness.row, Array.getD, dif_neg (by omega)]

theorem Witness.cell_shift [Zero F] (w : Witness F) (k : ℕ) (c : Cell) :
    (w.shift k).cell c = w.cell (k + c.1, c.2) := by
  show ((w.shift k).row c.1).getD c.2 0 = (w.row (k + c.1)).getD c.2 0
  rw [Witness.row_shift]

/-- A shifted gate's wire lookup is the shift of the original lookup (defaults align because
    `shiftWires` uses `k + ·`). -/
theorem Gate.wires_getD_shift (g : Gate F) (k j r c : ℕ) :
    (g.shiftWires k).wires.getD j (k + r, c)
      = ((fun p : Cell => (k + p.1, p.2)) (g.wires.getD j (r, c))) := by
  by_cases hj : j < g.wires.size
  · rw [Gate.shiftWires, Array.getD, dif_pos (by simpa using hj), Array.getD, dif_pos hj]
    simp
  · rw [Gate.shiftWires, Array.getD, dif_neg (by simpa using hj), Array.getD, dif_neg hj]

/-- **Projection onto an embedded block.** If rows `[k, k + block.size)` of the host are exactly
    the block's gates with wires shifted by `k`, and the block sits past the host's public rows,
    then a witness satisfying the host satisfies the block against the shifted witness view (the
    block itself carrying no public input — its `pubTerm` is `0` against the empty vector). -/
theorem Satisfies.of_embed [CommRing F] {host block : Circuit F} {w : Witness F} {pub : Array F}
    (k : ℕ) (hpub : host.publicInputSize ≤ k)
    (hsz : k + block.gates.size ≤ host.gates.size)
    (hgates : ∀ r, r < block.gates.size → host.gateAt (k + r) = (block.gateAt r).shiftWires k)
    (h : Satisfies host w pub) : Satisfies block (w.shift k) #[] := by
  obtain ⟨hg, hc⟩ := h
  refine ⟨fun r hr => ?_, fun r hr j hj => ?_⟩
  · have hh := hg (k + r) (by omega)
    rw [hgates r hr] at hh
    have hpt : host.pubTerm pub (k + r) = 0 := by
      rw [Circuit.pubTerm, if_neg (by omega)]
    rw [hpt] at hh
    have hpt' : block.pubTerm #[] r = (0 : F) := by
      rw [Circuit.pubTerm]; split <;> simp
    rw [hpt', Witness.row_shift, Witness.row_shift]
    exact hh
  · have hh := hc (k + r) (by omega) j hj
    rw [hgates r hr, Gate.wires_getD_shift] at hh
    rw [Witness.cell_shift, Witness.cell_shift]
    exact hh

/-- `rowHolds` only reads a gate's kind and coefficients — never its wires. -/
theorem rowHolds_congr [CommRing F] {g g' : Gate F} (hk : g.kind = g'.kind)
    (hc : g.coeffs = g'.coeffs) (curr next : Row F) (pubr : F) :
    rowHolds g curr next pubr ↔ rowHolds g' curr next pubr := by
  unfold rowHolds
  rw [hk, hc]

/-- **Generalized embedding.** Like `Satisfies.of_embed`, but the host's rows need only match the
    block's *kind and coefficients*; per wire, either the block's wire is a self-loop (its copy
    obligation is vacuous — the host may pin that cell however it likes, e.g. tying a block input
    to a setup row) or the host's wire is the shifted block wire. This is how a dumped circuit
    embeds a proven block whose boundary cells participate in the dump's own permutation cycles. -/
theorem Satisfies.of_embed' [CommRing F] {host block : Circuit F} {w : Witness F} {pub : Array F}
    (k : ℕ) (hpub : host.publicInputSize ≤ k)
    (hsz : k + block.gates.size ≤ host.gates.size)
    (hkind : ∀ r, r < block.gates.size → (host.gateAt (k + r)).kind = (block.gateAt r).kind)
    (hcoeffs : ∀ r, r < block.gates.size → (host.gateAt (k + r)).coeffs = (block.gateAt r).coeffs)
    (hwires : ∀ r j, r < block.gates.size → j < 7 →
      (block.gateAt r).wires.getD j (r, j) = (r, j)
      ∨ (host.gateAt (k + r)).wires.getD j (k + r, j)
          = ((fun p : Cell => (k + p.1, p.2)) ((block.gateAt r).wires.getD j (r, j))))
    (h : Satisfies host w pub) : Satisfies block (w.shift k) #[] := by
  obtain ⟨hg, hc⟩ := h
  refine ⟨fun r hr => ?_, fun r hr j hj => ?_⟩
  · have hh := hg (k + r) (by omega)
    rw [rowHolds_congr (hkind r hr) (hcoeffs r hr)] at hh
    have hpt : host.pubTerm pub (k + r) = 0 := by
      rw [Circuit.pubTerm, if_neg (by omega)]
    rw [hpt] at hh
    have hpt' : block.pubTerm #[] r = (0 : F) := by
      rw [Circuit.pubTerm]; split <;> simp
    rw [hpt', Witness.row_shift, Witness.row_shift]
    exact hh
  · rcases hwires r j hr hj with hself | hmatch
    · rw [hself]
    · have hh := hc (k + r) (by omega) j hj
      rw [hmatch] at hh
      rw [Witness.cell_shift, Witness.cell_shift]
      exact hh

end Kimchi.Circuit
