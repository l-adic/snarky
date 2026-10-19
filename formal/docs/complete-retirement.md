# Retiring the `Complete` form

The snarky package states completeness in two forms: the `Complete` relation with its
combinators (`Snarky/Prover.lean`), and the prover's weakest-precondition reading, whose laws are
`Std.Do` triples at the `Prover c` tag (`Snarky/Prover/WP.lean`). Every gadget under
`Snarky/DSL/` has its triple. This note lists what outside `Snarky/DSL/` depends on the
`Complete` form. A `Complete` law goes once its gadget has its triple and nothing without one
cites it; the rest stay until the kimchi gadgets that cite them migrate.

## The `Complete` form

- The relation and its rules, in `Snarky/Prover.lean`: `Complete`; `Complete.bind`, `.frame`,
  `.imp`, `.seq`, `.pure`, `.pure_of`, `.addConstraint`, `.of_false` and `.instantiate`; the run
  accessor `run_le`; the private `Runs` and `Sat` with their lemmas.
- The witness rule and the check's law, in `Snarky/Witness.lean`: `Complete.witness`, the
  `CheckedType.check_complete` field, each instance's proof of it (field cells, unit, bits,
  products, vectors, `UnChecked`, `CheckedType.ofEquiv`) and the private `checkAll_complete`.
- The traversal laws, in `Snarky/Traverse.lean`: `zipWithVecM_complete` over the private
  `zipGo_complete`, and `mapAccumM_complete`.
- The walker, in `Snarky/Tactic.lean` and `Snarky/Tactic/Attr.lean`: the `complete_walk`,
  `complete_mono_tac`, `complete_ctx` and `complete_apply_law` tactics, and the `complete_law`
  and `complete_mono` attributes that drive them.
- The DSL laws: the 11 declarations named `*_complete` under `Snarky/DSL/` that a kimchi
  gadget law or the `solve_complete` seam reaches, listed below.

## Method

Four methods, each covering what another cannot see.

- Declaration level: every authored constant's type and compiled proof, through the dead-code
  gate's dependency function, with compiler-generated auxiliaries folded into the declaration
  they belong to. A law the walker selects by attribute appears here as a constant in the proof
  term; a name search misses it.
- Name level: grep for the form's names and for the walker's tactic syntax. A tactic leaves no
  constant in a proof term, so only the source shows where the walker runs: the kimchi circuits
  `EndoScalar`, `RangeCheck` and `Sponge`.
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
| `CheckedPoint.check_complete` | `Snarky/Kimchi/Circuit/CheckedPoint.lean` | `assertSquare_complete`, `mul_complete`, `square_complete` | bind, frame, imp | kimchi gadget law |
| `EndoScalar.row_complete` | `Snarky/Kimchi/Circuit/EndoScalar.lean` | `Complete.witness` | bind, frame, imp, instantiate, pure_of | kimchi gadget law |
| `EndoScalar.toFieldChecked'_complete` | `Snarky/Kimchi/Circuit/EndoScalar.lean` | `Complete.witness`, `mapAccumM_complete` | addConstraint, bind, imp, instantiate, pure_of | kimchi gadget law |
| `EndoScalar.toField_complete` | `Snarky/Kimchi/Circuit/EndoScalar.lean` | — | — | kimchi gadget law |
| `EndoScalar.toField_complete_rows` | `Snarky/Kimchi/Circuit/EndoScalar.lean` | `assertEqual_complete`, `mul_complete` | imp, pure_of, seq | kimchi gadget law |
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
| `assertEqual_complete` | `Snarky/DSL/Assert.lean` | `EndoScalar.toField_complete_rows`, `lowest128Bits'_complete` | `assertEq_complete`, `sealVar.core_complete` | EndoScalar, RangeCheck, Sponge, the `solve` seam |
| `assertSquare_complete` | `Snarky/DSL/Assert.lean` | `CheckedPoint.check_complete` | — | CheckedPoint (with the `check_complete` field) |
| `selectField.core_complete` | `Snarky/DSL/Boolean.lean` | — | `selectField_complete` | RangeCheck |
| `selectField_complete` | `Snarky/DSL/Boolean.lean` | `assertSplitBelow_complete` | — | RangeCheck |
| `equals_complete` | `Snarky/DSL/Field.lean` | `assertSplitBelow_complete` | — | RangeCheck |
| `isZero_complete` | `Snarky/DSL/Field.lean` | — | `equals_complete` | RangeCheck |
| `mul_complete` | `Snarky/DSL/Field.lean` | `CheckedPoint.check_complete`, `EndoScalar.toField_complete_rows` | — | CheckedPoint (with the `check_complete` field), EndoScalar |
| `square_complete` | `Snarky/DSL/Field.lean` | `CheckedPoint.check_complete` | — | CheckedPoint (with the `check_complete` field) |
| `sealVar.core_complete` | `Snarky/DSL/Utils.lean` | — | `sealVar_complete` | Sponge |
| `sealVar_complete` | `Snarky/DSL/Utils.lean` | `SpongeVar.addSlotVar_complete` | — | Sponge |

## Retired

- The DSL laws nothing outside the DSL reaches: `or_complete`, `xor_complete` with the private
  `xor.core_complete`, `any_complete`, `all_complete`, `neq_complete`, `pow_complete` with the
  private `powGo_complete`, `unpack_complete`, `assertNotEqual_complete`, `assert_complete`,
  `assertAny_complete`, `assertExactlyOne_complete` and `assertAll_complete`. Each gadget's law
  is its triple at the prover's reading.
- `LawfulIfThenElse.select_complete` and its five instances' proofs. The class keeps
  `select_sound`, and nothing outside the DSL consumes it.
- The kimchi laws whose gadgets have their triples: `addFast_complete` with the private
  `sealPoint_complete` and `infColumn_complete`, `EndoMul.endoMul_complete` with its round,
  `EndoMul.endoInv_complete`, `varBaseMul_complete` with its round, `scaleFast1_complete`,
  `scaleFast2_complete`, `scaleFast2'_complete` and `splitFieldVar_complete`.
- The deployed-curve completeness instances `vesta_varBaseMul_complete` and
  `EndoMul.vesta_endoMul_complete`, without a restatement; their soundness readings stay.
- GroupMap's laws, now that the map has its triples (`Prover.groupMapCircuit_spec` and the
  wire form `Prover.groupMapCircuit_toGroup_spec`): `groupMapCircuit_complete`,
  `groupMapCircuit_toGroup_complete` and the private `ySquared_complete`,
  `sqrtFlagged_complete` and `flagSum`. With them the DSL laws only they reached:
  `and_complete`, `assertNonZero_complete`, `div_complete` and `inv_complete`.
- What only those laws used: `forM_complete`, `Complete.post` with `runs_post`, the
  Complete-form walks in EndoMul and VarBaseMul, `HasCurve.vesta_ladderCompleteRegime`, and
  `CircuitType.scoped_unit`.

The relation, its remaining rules, the walker, `zipWithVecM_complete`, `mapAccumM_complete` and
`check_complete` stay: each has a consumer outside the DSL, listed in the findings.

## Findings

- The DSL's `Complete` laws are consumed by the kimchi gadget laws without a triple and by
  `solve_complete`, which cites `assertEq_complete`. No pickles theorem, script or fixture check
  cites a DSL law, and no CI driver cites any declaration of the form.
- `mapAccumM_complete` is consumed by EndoScalar's `toFieldChecked'_complete`, which
  `toField_complete_rows` keeps; `zipWithVecM_complete` by `assertEq_complete`, so by the seam.
- `check_complete` is consumed by `Complete.witness`, `solve_complete`, the kimchi checked-type
  instances and the pickles instance below. `WPCheckedType.check_wp` is its replacement; the
  field goes when its last consumer does.
- The relation, its rules and the walker are consumed by the kimchi gadget laws of
  CheckedPoint, EndoScalar's wrapper, Poseidon, RandomOracle, RangeCheck and Sponge.
  `toField` has its triples (`Prover.toField_spec_rows`, `Prover.toField_spec`), but its
  `Complete` laws stay while RangeCheck's laws and the pickles instance cite them.
- One consumer is neither a kimchi gadget law nor the seam:
  `Pickles.instAllocBranchDataCheckedType` in `Pickles/StepSlot.lean`. Its `check_complete`
  proof uses the combinators and the kimchi law `EndoScalar.toField_complete_rows`. The kimchi
  migration does not replace it. Branch data's check needs a `WPCheckedType` instance, which
  `Prover.toField_spec_rows` now makes possible, and the `check_complete` proof goes when the
  field does.
