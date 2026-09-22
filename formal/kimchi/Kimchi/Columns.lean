/-!
# The kimchi shape constants

Every structural dimension of the kimchi wire and batch, named once. The names are scoped
notations expanding to the literals, not `def`s: the elaborated terms are bare numerals, so
bound arithmetic and existing proofs see exactly the literals they need. The notations carry
no unexpander, so goals print bare `7`s and `15`s: one numeral serves several roles (`7` is
`permCols` and `litRowCount`), and a name printed for a goal's `7` would be a guess. Each
derived constant is checked against its derivation by an `rfl` example at the end of the file.

## The primitives

The first two transcribe proof-systems' `circuits/wires.rs`.

* `wCols = 15` — the witness columns; the per-gate coefficient cells number the same.
* `permCols = 7` — the wired columns: seven wire pointers per row, seven σ polynomials,
  seven coset shifts.
* `evalPts = 2` — the evaluation points of every batch row, `ζ` and `ζω`.

## The derived batch layout

The batch order transcribes `verifier.rs`.

* `sigmaRows = permCols − 1 = 6` — the σ columns in the batch; the last σ polynomial is
  consumed by the linearization instead.
* `litRowCount = 7` — the single-column batch rows: the permutation accumulator `z` and the
  six selectors of the transcribed basic gate set (generic, poseidon, completeAdd,
  varBaseMul, endoMul, endoScalar). The selector count is a scope choice of the
  formalization, not a production constant: optional gates are out of scope.
* `tailRowCount = litRowCount + wCols + coeffCols + sigmaRows = 43` — the batch rows after
  the public row and the ft row.

A run's flat segment stream is its old accumulators' rows, then `nc + 1 + tailRowCount · nc`
segments: the public row's `nc` chunks, the ft row, then `nc` chunks per tail row.
-/

namespace Kimchi

/-- The witness columns. -/
scoped notation "wCols" => (15 : Nat)

/-- The wired columns, each with a wire pointer, a σ polynomial and a coset shift. -/
scoped notation "permCols" => (7 : Nat)

/-- The coefficient cells per row, one per witness column; named apart from `wCols` because
it counts a different batch region. -/
scoped notation "coeffCols" => (15 : Nat)

/-- The two evaluation points of every batch row, `(ζ, ζω)`. -/
scoped notation "evalPts" => (2 : Nat)

/-- The σ columns in the batch: `permCols − 1`, the last is linearized away. -/
scoped notation "sigmaRows" => (6 : Nat)

/-- The single-column batch rows: `z` and the six basic-gate selectors. -/
scoped notation "litRowCount" => (7 : Nat)

/-- The batch rows after the public and ft rows. -/
scoped notation "tailRowCount" => (43 : Nat)

/-! Each derived constant against its derivation. -/
example : sigmaRows = permCols - 1 := rfl
example : tailRowCount = litRowCount + wCols + coeffCols + sigmaRows := rfl

end Kimchi
