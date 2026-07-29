/-!
# The kimchi shape constants

Every structural dimension of the kimchi wire and batch, named at its production
origin. The names are **scoped notations expanding to the literals** — deliberately
not `def`s or `abbrev`s: the elaborated terms are the bare numerals, so bound
arithmetic (`omega`, `interval_cases`, `decide`) and every existing proof see exactly
the literals they need. Only the source names the dimension: the notations carry no
unexpander, so goals print the bare `7`s and `15`s. That is deliberate — the same
numeral serves several roles (`7` is `permCols` and `litRowCount`, `15` is `wCols`
and `coeffCols`), so any name a delaborator picked for a goal's `7` would be a guess,
and often the wrong one. Each derived constant carries an `rfl` theorem machine-checking
its derivation, so the connection to the primitive constants is kernel-checked, not prose.

## The primitives

* `wCols = 15` — production `COLUMNS` (proof-systems `circuits/wires.rs`): the
  witness columns, and equally the per-gate coefficient cells.
* `permCols = 7` — production `PERMUTS` (`circuits/wires.rs`): the wired columns —
  seven wire pointers per row, seven σ polynomials, seven coset shifts.
* `selCount = 6` — the transcribed basic gate set (generic, poseidon, completeAdd,
  varBaseMul, endoMul, endoScalar). This is a *scope choice* of the formalization, not
  a production constant: production carries further selectors behind optional-gate
  flags, all declared deferrals here.
* `evalPts = 2` — the two evaluation points of every batch row, `(ζ, ζω)`.

## The derived batch layout

From `to_batch` (verifier.rs).

* `sigmaRows = permCols − 1 = 6` — the σ columns *in the batch*: production commits
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

/-- The six pre-IPA squeezes of a kimchi run — `β, γ, α, ζ`, then the batching scalars
`polyscale` and `evalscale`: the challenge tuple the knowledge-soundness game hands a run
(`Verifier/KnowledgeSoundness.lean`'s `Squeeze` minus the IPA rounds and the Schnorr
squeeze). A formalization-side count, and a third incidental six, distinct from `selCount`
and `sigmaRows`. -/
scoped notation "preIpaChals" => (6 : Nat)

/-- The counted Schwartz–Zippel exclusion sets of the knowledge-soundness endpoint —
`szBudget`'s seven summands, the seven disjuncts of `arm4_hits_badChallenge`. A
formalization-side count, distinct from the incidental sevens `permCols` and
`litRowCount`. -/
scoped notation "szSets" => (7 : Nat)

/-! The derivation checks the module docstring promises (external-audit A-12): each derived
constant is kernel-checked against its defining arithmetic. -/
example : sigmaRows = permCols - 1 := rfl
example : litRowCount = 1 + selCount := rfl
example : tailRowCount = litRowCount + wCols + coeffCols + sigmaRows := rfl
example : batchRows = 1 + tailRowCount := rfl

end Kimchi
