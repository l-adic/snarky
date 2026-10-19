# Retiring the `Complete` form

The snarky package states completeness in two forms: the `Complete` relation with its
combinators (`Snarky/Prover.lean`), and the prover's weakest-precondition reading, whose laws are
`Std.Do` triples at the `Prover c` tag (`Snarky/Prover/WP.lean`). Every gadget under
`Snarky/DSL/` has its triple. This note lists what outside `Snarky/DSL/` depends on the
`Complete` form: the DSL laws nothing outside the DSL reaches are retired, and the rest stay
until the kimchi gadgets that cite them migrate.

## The `Complete` form

- The relation and its rules, in `Snarky/Prover.lean`: `Complete`; `Complete.bind`, `.frame`,
  `.imp`, `.seq`, `.pure`, `.pure_of`, `.addConstraint`, `.of_false`, `.instantiate` and `.post`;
  the run accessors `run_le` and `runs_post`; the private `Runs` and `Sat` with their lemmas.
- The witness rule and the check's law, in `Snarky/Witness.lean`: `Complete.witness`, the
  `CheckedType.check_complete` field, each instance's proof of it (field cells, unit, bits,
  products, vectors, `UnChecked`, `CheckedType.ofEquiv`) and the private `checkAll_complete`.
- The traversal laws, in `Snarky/Traverse.lean`: `zipWithVecM_complete` over the private
  `zipGo_complete`, `mapAccumM_complete` and `forM_complete`.
- The walker, in `Snarky/Tactic.lean` and `Snarky/Tactic/Attr.lean`: the `complete_walk`,
  `complete_mono_tac`, `complete_ctx` and `complete_apply_law` tactics, and the `complete_law`
  and `complete_mono` attributes that drive them.
- The DSL laws: the 15 declarations named `*_complete` under `Snarky/DSL/` that a kimchi
  gadget law or the `solve_complete` seam reaches, listed below.

## Method

Four methods, each covering what another cannot see.

- Declaration level: every authored constant's type and compiled proof, through the dead-code
  gate's dependency function, with compiler-generated auxiliaries folded into the declaration
  they belong to. A law the walker selects by attribute appears here as a constant in the proof
  term; a name search misses it.
- Name level: grep for the form's names and for the walker's tactic syntax. A tactic leaves no
  constant in a proof term, so only the source shows where the walker runs: the kimchi circuits
  `AddComplete`, `EndoMul`, `EndoScalar`, `GroupMap`, `RangeCheck` and `Sponge`.
- Module level: `lake exe graph --include-deps --from Snarky.Tactic --to Pickles`. The walker's
  module is imported directly by `Snarky.Kimchi.Circuit.AddComplete`, `.EndoScalar`, `.GroupMap`
  and `.Sponge` only; the other circuits reach it through those.
- The CI drivers, read from their compiled modules as the dead-code gate reads them: none of the
  twelve cites a declaration of the form.

The root lists in `snarky/scripts/check_axioms.lean` are not consumers: they keep the form's
results alive without using them.

## Consumers

Every consumer outside `Snarky/DSL/` and the machinery, with the laws it cites beside the
combinators. Each row also cites the relation itself.

| Consumer | File | Laws cited | Combinators cited | Kind |
|---|---|---|---|---|
| `addFast_complete` | `Snarky/Kimchi/Circuit/AddComplete.lean` | `Complete.witness` | addConstraint, bind, frame, imp, instantiate, post, pure_of, seq | kimchi gadget law |
| `infColumn_complete` | `Snarky/Kimchi/Circuit/AddComplete.lean` | `Complete.witness` | bind, imp, pure_of | kimchi gadget law |
| `sealPoint_complete` | `Snarky/Kimchi/Circuit/AddComplete.lean` | `sealVar_complete` | imp, pure_of, seq | kimchi gadget law |
| `CheckedPoint.check_complete` | `Snarky/Kimchi/Circuit/CheckedPoint.lean` | `assertSquare_complete`, `mul_complete`, `square_complete` | bind, frame, imp | kimchi gadget law |
| `EndoMul.endoInv_complete` | `Snarky/Kimchi/Circuit/EndoMul.lean` | `assertEqual_complete` | imp, pure_of, seq | kimchi gadget law |
| `EndoMul.endoMulRound_complete` | `Snarky/Kimchi/Circuit/EndoMul.lean` | `Complete.witness` | bind, frame, imp, instantiate, pure_of | kimchi gadget law |
| `EndoMul.endoMul_complete` | `Snarky/Kimchi/Circuit/EndoMul.lean` | `Complete.witness`, `assertEqual_complete`, `mapAccumM_complete`, `sealVar_complete` | addConstraint, bind, frame, imp, instantiate, pure_of, seq | kimchi gadget law |
| `EndoMul.vesta_endoMul_complete` | `Snarky/Kimchi/Circuit/EndoMul.lean` | — | Runs/Sat (unfolded) | kimchi gadget law |
| `EndoMul.witnessAt_complete` | `Snarky/Kimchi/Circuit/EndoMul.lean` | `Complete.witness` | imp | kimchi gadget law |
| `EndoScalar.row_complete` | `Snarky/Kimchi/Circuit/EndoScalar.lean` | `Complete.witness` | bind, frame, imp, instantiate, pure_of | kimchi gadget law |
| `EndoScalar.toFieldChecked'_complete` | `Snarky/Kimchi/Circuit/EndoScalar.lean` | `Complete.witness`, `mapAccumM_complete` | addConstraint, bind, imp, instantiate, pure_of | kimchi gadget law |
| `EndoScalar.toField_complete` | `Snarky/Kimchi/Circuit/EndoScalar.lean` | — | — | kimchi gadget law |
| `EndoScalar.toField_complete_rows` | `Snarky/Kimchi/Circuit/EndoScalar.lean` | `assertEqual_complete`, `mul_complete` | imp, pure_of, seq | kimchi gadget law |
| `groupMapCircuit_complete` | `Snarky/Kimchi/Circuit/GroupMap.lean` | `and_complete`, `assertNonZero_complete`, `div_complete`, `mul_complete` | imp, pure_of, seq | kimchi gadget law |
| `groupMapCircuit_toGroup_complete` | `Snarky/Kimchi/Circuit/GroupMap.lean` | — | Runs/Sat (unfolded) | kimchi gadget law |
| `sqrtFlagged_complete` | `Snarky/Kimchi/Circuit/GroupMap.lean` | `Complete.witness`, `assertSquare_complete`, `selectField_complete` | bind, frame, imp, pure_of | kimchi gadget law |
| `ySquared_complete` | `Snarky/Kimchi/Circuit/GroupMap.lean` | `mul_complete` | imp, pure_of, seq | kimchi gadget law |
| `Poseidon.poseidon_complete` | `Snarky/Kimchi/Circuit/Poseidon.lean` | `Complete.witness` | addConstraint, bind, frame, imp, pure_of | kimchi gadget law |
| `RandomOracle.foldBlocks_complete` | `Snarky/Kimchi/Circuit/RandomOracle.lean` | — | bind, frame, imp, of_false, pure_of | kimchi gadget law |
| `RandomOracle.hash2_complete` | `Snarky/Kimchi/Circuit/RandomOracle.lean` | — | bind, imp, pure_of | kimchi gadget law |
| `RandomOracle.hashVec_complete` | `Snarky/Kimchi/Circuit/RandomOracle.lean` | — | bind, imp, pure_of | kimchi gadget law |
| `RandomOracle.updateBlock_complete` | `Snarky/Kimchi/Circuit/RandomOracle.lean` | — | imp | kimchi gadget law |
| `RandomOracle.update_complete` | `Snarky/Kimchi/Circuit/RandomOracle.lean` | — | imp | kimchi gadget law |
| `assertSplitBelow_complete` | `Snarky/Kimchi/Circuit/RangeCheck.lean` | `equals_complete`, `selectField_complete` | bind, imp, pure_of, seq | kimchi gadget law |
| `lowest128Bits'_complete` | `Snarky/Kimchi/Circuit/RangeCheck.lean` | `Complete.witness`, `assertEqual_complete` | imp, pure, pure_of, seq | kimchi gadget law |
| `rangeCheck128_complete` | `Snarky/Kimchi/Circuit/RangeCheck.lean` | — | imp, pure_of, seq | kimchi gadget law |
| `SpongeVar.absorb_complete` | `Snarky/Kimchi/Circuit/Sponge.lean` | — | imp, instantiate, pure_of, seq | kimchi gadget law |
| `SpongeVar.addSlotVar_complete` | `Snarky/Kimchi/Circuit/Sponge.lean` | `sealVar_complete` | imp, pure_of, seq | kimchi gadget law |
| `SpongeVar.squeeze_complete` | `Snarky/Kimchi/Circuit/Sponge.lean` | — | imp, instantiate, pure_of, seq | kimchi gadget law |
| `VarBaseMul.scaleRound_complete` | `Snarky/Kimchi/Circuit/VarBaseMul.lean` | `Complete.witness` | bind, frame, imp, instantiate, pure_of | kimchi gadget law |
| `scaleFast1_complete` | `Snarky/Kimchi/Circuit/VarBaseMul.lean` | `assertEqual_complete`, `forM_complete` | bind, frame, imp, pure_of | kimchi gadget law |
| `scaleFast2'_complete` | `Snarky/Kimchi/Circuit/VarBaseMul.lean` | — | bind, frame, imp | kimchi gadget law |
| `scaleFast2_complete` | `Snarky/Kimchi/Circuit/VarBaseMul.lean` | `assertEqual_complete`, `forM_complete`, `selectField_complete` | bind, frame, imp, instantiate, pure_of | kimchi gadget law |
| `splitFieldVar_complete` | `Snarky/Kimchi/Circuit/VarBaseMul.lean` | `Complete.witness`, `assertEqual_complete` | bind, frame, imp, pure_of | kimchi gadget law |
| `varBaseMul_complete` | `Snarky/Kimchi/Circuit/VarBaseMul.lean` | `Complete.witness`, `assertEqual_complete`, `mapAccumM_complete` | addConstraint, bind, frame, imp, instantiate, pure_of, seq | kimchi gadget law |
| `vesta_varBaseMul_complete` | `Snarky/Kimchi/Circuit/VarBaseMul.lean` | — | — | kimchi gadget law |
| `instCheckedTypeAffinePointFVar` | `Snarky/Kimchi/Circuit/AddComplete.lean` | proves `check_complete` | pure | kimchi checked-type instance |
| `instCheckedTypeCheckedPoint` | `Snarky/Kimchi/Circuit/CheckedPoint.lean` | proves `check_complete` | imp | kimchi checked-type instance |
| `instCheckedTypeSpongeState` | `Snarky/Kimchi/Circuit/Poseidon.lean` | proves `check_complete` | pure | kimchi checked-type instance |
| `solve_complete` | `Snarky/Compile.lean` | `CheckedType.check_complete`, `Complete.witness`, `assertEq_complete` | bind, frame, imp, instantiate, pure_of, Runs/Sat (unfolded) | `solve_complete` seam |
| `Pickles.instAllocBranchDataCheckedType` | `Pickles/StepSlot.lean` | proves `check_complete`; cites `CheckedType.check_complete` and the kimchi law `EndoScalar.toField_complete_rows` | bind, frame, imp, pure | pickles checked-type instance |

## Retained DSL laws

Each DSL law something outside the DSL still reaches, with its citers there, the DSL laws it is
reached through, and the kimchi circuits whose migration releases it.

| DSL law | File | Cited by, outside the DSL | Through | Retained until these migrate |
|---|---|---|---|---|
| `assertEq_complete` | `Snarky/DSL/Assert.lean` | `solve_complete` | — | the `solve` seam |
| `assertEqual_complete` | `Snarky/DSL/Assert.lean` | `EndoMul.endoInv_complete`, `EndoMul.endoMul_complete`, `EndoScalar.toField_complete_rows`, `lowest128Bits'_complete`, `scaleFast1_complete`, `scaleFast2_complete`, `splitFieldVar_complete`, `varBaseMul_complete` | `assertEq_complete`, `sealVar.core_complete` | AddComplete, EndoMul, EndoScalar, RangeCheck, Sponge, VarBaseMul, the `solve` seam |
| `assertNonZero_complete` | `Snarky/DSL/Assert.lean` | `groupMapCircuit_complete` | — | GroupMap |
| `assertSquare_complete` | `Snarky/DSL/Assert.lean` | `CheckedPoint.check_complete`, `sqrtFlagged_complete` | — | CheckedPoint, GroupMap |
| `and_complete` | `Snarky/DSL/Boolean.lean` | `groupMapCircuit_complete` | — | GroupMap |
| `selectField.core_complete` | `Snarky/DSL/Boolean.lean` | — | `selectField_complete` | GroupMap, RangeCheck, VarBaseMul |
| `selectField_complete` | `Snarky/DSL/Boolean.lean` | `assertSplitBelow_complete`, `scaleFast2_complete`, `sqrtFlagged_complete` | — | GroupMap, RangeCheck, VarBaseMul |
| `div_complete` | `Snarky/DSL/Field.lean` | `groupMapCircuit_complete` | — | GroupMap |
| `equals_complete` | `Snarky/DSL/Field.lean` | `assertSplitBelow_complete` | — | RangeCheck |
| `inv_complete` | `Snarky/DSL/Field.lean` | — | `assertNonZero_complete`, `div_complete` | GroupMap |
| `isZero_complete` | `Snarky/DSL/Field.lean` | — | `equals_complete` | RangeCheck |
| `mul_complete` | `Snarky/DSL/Field.lean` | `CheckedPoint.check_complete`, `EndoScalar.toField_complete_rows`, `groupMapCircuit_complete`, `ySquared_complete` | `and_complete`, `div_complete` | CheckedPoint, EndoScalar, GroupMap |
| `square_complete` | `Snarky/DSL/Field.lean` | `CheckedPoint.check_complete` | — | CheckedPoint |
| `sealVar.core_complete` | `Snarky/DSL/Utils.lean` | — | `sealVar_complete` | AddComplete, EndoMul, Sponge |
| `sealVar_complete` | `Snarky/DSL/Utils.lean` | `EndoMul.endoMul_complete`, `SpongeVar.addSlotVar_complete`, `sealPoint_complete` | — | AddComplete, EndoMul, Sponge |

## Retired

- The DSL laws nothing outside the DSL reaches: `or_complete`, `xor_complete` with the private
  `xor.core_complete`, `any_complete`, `all_complete`, `neq_complete`, `pow_complete` with the
  private `powGo_complete`, `unpack_complete`, `assertNotEqual_complete`, `assert_complete`,
  `assertAny_complete`, `assertExactlyOne_complete` and `assertAll_complete`. Each gadget's law
  is its triple at the prover's reading.
- `LawfulIfThenElse.select_complete` and its five instances' proofs. The class keeps
  `select_sound`, and nothing outside the DSL consumes it.
- `CircuitType.scoped_unit`, whose only citer was the unit instance's proof of
  `select_complete`.

The traversal laws, `check_complete`, the relation, its combinators and the walker stay: each
has a consumer outside the DSL, listed in the findings.

## Findings

- The DSL's `Complete` laws are consumed by kimchi gadget laws and by `solve_complete`, which
  cites `assertEq_complete`. No pickles theorem, script or fixture check cites a DSL law, and no
  CI driver cites any declaration of the form.
- The traversal laws are all consumed: `mapAccumM_complete` by the endoMul, EndoScalar and
  varBaseMul laws, `forM_complete` by `scaleFast1_complete` and `scaleFast2_complete`, and
  `zipWithVecM_complete` by `assertEq_complete`, so by the seam.
- `check_complete` is consumed by `Complete.witness`, `solve_complete`, the kimchi checked-type
  instances and the pickles instance below. `WPCheckedType.check_wp` is its replacement; the
  field goes when its last consumer does.
- The relation, its combinators and the walker are consumed by the kimchi gadget laws.
- One consumer is neither a kimchi gadget law nor the seam:
  `Pickles.instAllocBranchDataCheckedType` in `Pickles/StepSlot.lean`. Its `check_complete`
  proof uses the combinators and the kimchi law `EndoScalar.toField_complete_rows`. The kimchi
  migration does not replace it. The proof goes when `check_complete` does, and branch data's
  check needs a `WPCheckedType` instance, built on the EndoScalar decomposition's law at the
  prover's reading. Through `toField_complete_rows` it also reaches `mul_complete` and
  `assertEqual_complete`, so EndoScalar's migration has to carry this instance with it.
