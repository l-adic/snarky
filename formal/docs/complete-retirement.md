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
- The DSL laws: the 5 declarations named `*_complete` under `Snarky/DSL/` that a kimchi
  gadget law or the `solve_complete` seam reaches, listed below.

## Method

Four methods, each covering what another cannot see.

- Declaration level: every authored constant's type and compiled proof, through the dead-code
  gate's dependency function, with compiler-generated auxiliaries folded into the declaration
  they belong to. A law the walker selects by attribute appears here as a constant in the proof
  term; a name search misses it.
- Name level: grep for the form's names and for the walker's tactic syntax. A tactic leaves no
  constant in a proof term, so only the source shows where the walker runs: the kimchi circuit
  `EndoScalar`.
- Module level: `lake exe graph --include-deps --from Snarky.Tactic --to Pickles`, with the
  import lines read alongside, since the graph drops an import another one already implies. The
  walker's module is imported directly by `Snarky.Kimchi.Circuit.AddComplete`, `.EndoScalar`
  and `.GroupMap`. `GroupMap` no longer runs the walker, and shake keeps its import. The other
  circuits reach the module through these.
- The CI drivers, read from their compiled modules as the dead-code gate reads them: none of the
  twelve cites a law, rule or walker declaration of the form. Two use consumer instances as
  instances: `check_cs` the `AffinePoint`, `SpongeState` and branch-data instances, and
  `check_slot_chunks` the branch-data instance. Retiring the `check_complete` field edits those
  instances; the drivers keep them.

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
| `EndoScalar.toField_complete_rows` | `Snarky/Kimchi/Circuit/EndoScalar.lean` | `assertEqual_complete`, `mul_complete` | imp, pure_of, seq | kimchi gadget law |
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
| `assertEqual_complete` | `Snarky/DSL/Assert.lean` | `EndoScalar.toField_complete_rows` | `assertEq_complete` | EndoScalar (with the pickles instance), the `solve` seam |
| `assertSquare_complete` | `Snarky/DSL/Assert.lean` | `CheckedPoint.check_complete` | — | CheckedPoint (with the `check_complete` field) |
| `mul_complete` | `Snarky/DSL/Field.lean` | `CheckedPoint.check_complete`, `EndoScalar.toField_complete_rows` | — | CheckedPoint (with the `check_complete` field), EndoScalar |
| `square_complete` | `Snarky/DSL/Field.lean` | `CheckedPoint.check_complete` | — | CheckedPoint (with the `check_complete` field) |

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
- What only the laws above used, as the dead-code gate listed it: `forM_complete`,
  `Complete.post` with `runs_post`, the Complete-form walks in EndoMul and VarBaseMul,
  `HasCurve.vesta_ladderCompleteRegime`, and `CircuitType.scoped_unit`.
- GroupMap's laws, now that the map has its triples (`Prover.groupMapCircuit_spec` and the
  wire form `Prover.groupMapCircuit_toGroup_spec`): `groupMapCircuit_complete`,
  `groupMapCircuit_toGroup_complete` and the private `ySquared_complete`,
  `sqrtFlagged_complete` and `flagSum`. With them the DSL laws only they reached:
  `and_complete`, `assertNonZero_complete`, `div_complete` and `inv_complete`.
- The permutation's and the hashes' laws, now that each gadget has its triple
  (`Poseidon.Prover.poseidon_spec`, `SpongeVar.Prover.absorb_spec` and `squeeze_spec`,
  `RandomOracle.Prover.update_spec`, `hash2_spec` and `hashVec_spec`): `poseidon_complete`,
  `SpongeVar.absorb_complete`, `squeeze_complete` and the private `addSlotVar_complete`, and
  `RandomOracle.update_complete`, `hash2_complete`, `hashVec_complete` and the private
  `updateBlock_complete` and `foldBlocks_complete`. With them the DSL law only they reached,
  `sealVar_complete` with the private `sealVar.core_complete`; then what only those used, as the
  dead-code gate listed it: Sponge's `monotone_reads`, `CircuitType.monotone_forall₂` and
  `valid_spongeState`.
- RangeCheck's laws, now that its gadgets have their triples (`Prover.rangeCheck128_spec`,
  `Prover.lowest128Bits'_spec`): `rangeCheck128_complete`, `lowest128Bits'_complete` and the
  private `assertSplitBelow_complete`. With them `EndoScalar.toField_complete`, which only they
  cited, and the DSL laws only they reached: `selectField_complete` with the private
  `selectField.core_complete`, `equals_complete` and `isZero_complete`; then the private
  `asField` the dead-code gate listed.

The relation, its remaining rules, the walker, `zipWithVecM_complete`, `mapAccumM_complete` and
`check_complete` stay: each has a consumer outside the DSL, listed in the findings.

## Findings

- The DSL's `Complete` laws are consumed by the kimchi gadget laws without a triple and by
  `solve_complete`, which cites `assertEq_complete`. No pickles theorem, script or fixture check
  cites a DSL law, and no CI driver cites a law of the form; two use consumer instances, as the
  method section records.
- `mapAccumM_complete` is consumed by EndoScalar's `toFieldChecked'_complete`, which
  `toField_complete_rows` keeps; `zipWithVecM_complete` by `assertEq_complete`, so by the seam.
- `check_complete` is consumed by `Complete.witness`, `solve_complete`, the kimchi checked-type
  instances and the pickles instance below. `WPCheckedType.check_wp` is its replacement; the
  field goes when its last consumer does.
- The relation, its rules and the walker are consumed by CheckedPoint's `check_complete` and
  EndoScalar's `toField_complete_rows`. `toField` has its triples (`Prover.toField_spec_rows`,
  `Prover.toField_spec`); `toField_complete_rows`, with `toFieldChecked'_complete` and
  `row_complete` beneath it, stays while the pickles instance cites it.
- `Complete.of_false` has no consumer left: `foldBlocks_complete` was its last. It stays among
  the relation's rules, rooted with them.
- One consumer is neither a kimchi gadget law nor the seam:
  `Pickles.instAllocBranchDataCheckedType` in `Pickles/StepSlot.lean`. Its `check_complete`
  proof uses the combinators and the kimchi law `EndoScalar.toField_complete_rows`. The kimchi
  migration does not replace it. Branch data's check needs a `WPCheckedType` instance, which
  `Prover.toField_spec_rows` now makes possible, and the `check_complete` proof goes when the
  field does.
