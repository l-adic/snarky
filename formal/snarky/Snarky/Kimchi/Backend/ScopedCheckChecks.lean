import Snarky.Kimchi.Backend.ScopedCheck
import Snarky.Kimchi.Backend.WiredFixtures

/-!
# Scope-checker checks

The checker decided on the wired-fragment checks' sources, in the kernel: it accepts the eight
accepted sources, and it reports the expected failure on each source out of scope. The
reported failure is not covered by `checkScoped_eq_true_iff`, so these are its tests.

The rejections cover a variable at or above the counter in the source and among the public
variables; an identifier far above the counter, reported without a set of its size being
built; constraints that are not wired, by a constant or a sum in an unwired column or a
Poseidon block off the shape; and an unwired operand occurring again later in the list,
earlier in the list, within its own constraint, and as a public variable. The last theorem
fixes the order: the range pass first, then the earliest constraint, its wiredness before the
uniqueness of its operands.

## Main results

- `checkScoped_accepts`: the eight accepted sources are accepted.
- `scopedFailure_range`, `scopedFailure_notWired`, `scopedFailure_reused`: the reported
  failure, by kind.
- `scopedFailure_precedence`: the order in which failures are reported.
-/

namespace Snarky.Kimchi

open Snarky WiredFixture

/-- The checker accepts every accepted source of the wired-fragment checks. -/
theorem checkScoped_accepts :
    checkScoped 20 source publicVars = true ∧
    checkScoped 11 endoSource endoPublic = true ∧
    checkScoped 22 chainSource chainPublic = true ∧
    checkScoped 25 scaleSource scalePublic = true ∧
    checkScoped 46 scaleChainSource scaleChainPublic = true ∧
    checkScoped 28 endoMulSource endoMulPublic = true ∧
    checkScoped 32 poseidonSource poseidonPublic = true ∧
    checkScoped 5 padSource padPublic = true := by
  decide +kernel

/-- A variable at the counter is reported with its constraint's index, or as a public
variable; so is an identifier far above the counter, whose bit is never set. -/
theorem scopedFailure_range :
    scopedFailure? 20 highSource publicVars = some (.outOfRange 5 20) ∧
    scopedFailure? 20 source [0, 1, 20] = some (.publicOutOfRange 20) ∧
    scopedFailure? 20 (source ++ [.basic (.boolean (.var (2 ^ 30)))]) publicVars =
      some (.outOfRange 5 (2 ^ 30)) := by
  decide +kernel

/-- A constant or a sum in an unwired column, and a Poseidon block off the shape, are
reported as not wired at their constraint. -/
theorem scopedFailure_notWired :
    scopedFailure? 20 constSource publicVars = some (.notWired 2) ∧
    scopedFailure? 22 [.endoScalar [round1, summedRound]] chainPublic = some (.notWired 0) ∧
    scopedFailure? 25 [.varBaseMul [summedScale]] scalePublic = some (.notWired 0) ∧
    scopedFailure? 28 [.endoMul summedEndoMul] endoMulPublic = some (.notWired 0) ∧
    scopedFailure? 32 [.poseidon summedPoseidon] poseidonPublic = some (.notWired 0) ∧
    scopedFailure? 32 [.poseidon { pblock with state := pblock.state.take 5 }] poseidonPublic =
      some (.notWired 0) := by
  decide +kernel

/-- An unwired operand occurring again is reported at the constraint that places it: named
later in the list, within its own constraint, earlier in the list, as a public variable, and
for each gate. -/
theorem scopedFailure_reused :
    scopedFailure? 20 equalSource publicVars = some (.reused 2 9) ∧
    scopedFailure? 20 termSource publicVars = some (.reused 2 9) ∧
    scopedFailure? 20 (.basic (.boolean (.var 9)) :: source) publicVars = some (.reused 3 9) ∧
    scopedFailure? 20 source [0, 1, 9] = some (.reused 2 9) ∧
    scopedFailure? 20 padReuse publicVars = some (.reused 2 9) ∧
    scopedFailure? 22 reusedSource chainPublic = some (.reused 0 12) ∧
    scopedFailure? 25 reusedScale scalePublic = some (.reused 0 20) ∧
    scopedFailure? 28 reusedEndoMul endoMulPublic = some (.reused 0 7) ∧
    scopedFailure? 32 reusedPoseidon poseidonPublic = some (.reused 0 5) := by
  decide +kernel

/-- The order of reports: a variable out of range anywhere comes before a constraint that is
not wired earlier in the list; then the earliest failing constraint, a reuse before a later
constraint that is not wired; and within one constraint, wiredness before uniqueness. -/
theorem scopedFailure_precedence :
    scopedFailure? 20 (constSource ++ [.basic (.boolean (.var 20))]) publicVars =
      some (.outOfRange 5 20) ∧
    scopedFailure? 22 (equalSource ++ [.endoScalar [summedRound]]) publicVars =
      some (.reused 2 9) ∧
    scopedFailure? 20 (constSource ++ [.basic (.boolean (.var 10))]) publicVars =
      some (.notWired 2) := by
  decide +kernel

end Snarky.Kimchi
