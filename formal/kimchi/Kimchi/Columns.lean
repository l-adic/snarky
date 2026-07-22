/-!
# The kimchi shape constants

Every structural dimension of the kimchi wire and batch, named at its production
origin. The names are **scoped notations expanding to the literals** — deliberately
not `def`s or `abbrev`s: the elaborated terms are the bare numerals, so bound
arithmetic (`omega`, `interval_cases`, `decide`) and every existing proof see exactly
the literals they need, while the source and the goals name the dimension. Each
derived constant carries an `rfl` theorem machine-checking its derivation, so the
connection to the primitive constants is kernel-checked, not prose.

The primitives:

* `wCols = 15` — production `COLUMNS` (proof-systems `circuits/wires.rs`): the
  witness columns, and equally the per-gate coefficient cells.
* `permCols = 7` — production `PERMUTS` (`circuits/wires.rs`): the wired columns —
  seven wire pointers per row, seven σ polynomials, seven coset shifts.
* `selCount = 6` — the transcribed basic gate set (generic, poseidon, completeAdd,
  varBaseMul, endoMul, endoScalar). This is a SCOPE CHOICE of the formalization, not
  a production constant: production carries further selectors behind optional-gate
  flags, all declared deferrals here.
* `evalPts = 2` — the two evaluation points of every batch row, `(ζ, ζω)`.

The derived batch layout (`to_batch`, verifier.rs):

* `sigmaRows = permCols − 1 = 6` — the σ columns IN THE BATCH: production commits
  seven σ polynomials but batches only the first six (`sigma_comm[PERMUTS − 1]` is
  consumed by the linearization instead). Distinct from `selCount` even though both
  are `6`.
* `litRowCount = 1 + selCount = 7` — the literal single-column rows of the batch
  tail: the accumulator `z` plus the six selectors. Distinct from `permCols` even
  though both are `7` (and distinct from the Poseidon S-box exponent and the
  AddComplete constraint count, two further incidental sevens).
* `tailRowCount = litRowCount + wCols + coeffCols + sigmaRows = 43` — the batch rows
  after the public row and the ft row: `z`, the selectors, the witness columns, the
  coefficient columns, the six σ columns.
* `batchRows = 1 + tailRowCount = 44` — the abstract batch: the public row joins at
  chunking (its claims are proof-carried, bound through the opening), the ft row is
  consumed separately by the `_ft` terminals.

The flat segment stream of a run is `nc + 1 + tailRowCount · nc` segments: the
public row's `nc` chunks, the single-chunk ft row, then `nc` chunks per tail row.
-/

namespace Kimchi

/-- Production `COLUMNS = 15`: the witness columns (= the coefficient cells). -/
scoped notation "wCols" => (15 : Nat)

/-- Production `PERMUTS = 7`: the wired columns (wire pointers, σ, shifts). -/
scoped notation "permCols" => (7 : Nat)

/-- The coefficient cells per row — production types this at `COLUMNS` too
(`coefficients_comm : [PolyComm; COLUMNS]`, one coefficient per witness column);
named separately because it counts a different batch region than the witness rows. -/
scoped notation "coeffCols" => (15 : Nat)

/-- The transcribed basic gate set (a scope choice — see the module docstring). -/
scoped notation "selCount" => (6 : Nat)

/-- The two evaluation points of every batch row, `(ζ, ζω)`. -/
scoped notation "evalPts" => (2 : Nat)

/-- The σ columns in the batch: `permCols − 1` (the seventh is linearized away). -/
scoped notation "sigmaRows" => (6 : Nat)

/-- The literal single-column batch rows: `z` + the six selectors. -/
scoped notation "litRowCount" => (7 : Nat)

/-- The batch rows after the public and ft rows. -/
scoped notation "tailRowCount" => (43 : Nat)

/-- The abstract batch rows (public row included, ft row excluded). -/
scoped notation "batchRows" => (44 : Nat)

/-- `coeffCols` is production's `COLUMNS`, like `wCols` — kernel-checked. -/
theorem coeffCols_eq : coeffCols = wCols := rfl

/-- `sigmaRows` is `permCols − 1` — kernel-checked. -/
theorem sigmaRows_eq : sigmaRows = permCols - 1 := rfl

/-- `litRowCount` is `z` plus the selectors — kernel-checked. -/
theorem litRowCount_eq : litRowCount = 1 + selCount := rfl

/-- `tailRowCount` is the four tail regions — kernel-checked. -/
theorem tailRowCount_eq :
    tailRowCount = litRowCount + wCols + coeffCols + sigmaRows := rfl

/-- `batchRows` is the public row plus the tail — kernel-checked. -/
theorem batchRows_eq : batchRows = 1 + tailRowCount := rfl

end Kimchi
