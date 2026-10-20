# Retiring the `Complete` form

The snarky package states completeness at the prover's weakest-precondition reading: `Std.Do`
triples at the `Prover c` tag (`Snarky/Prover/WP.lean`), composed by `mvcgen`, with the adequacy
theorem `proverWP_prove` reading a run off a triple. The `Complete` relation with its
combinators, the package's other form, is retired. This note records what the form comprised,
how its consumers were found, what each unit retired, and where each result now lives.

## The `Complete` form

What the form comprised, by where it lived:

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
- The `*_complete` laws of the DSL gadgets and of the kimchi circuits, and the seam law
  `solve_complete` stated in the form.

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
  walker's module was imported directly by three kimchi circuits, `AddComplete`, `EndoScalar`
  and `GroupMap`; the others reached it through them.
- The CI drivers, read from their compiled modules as the dead-code gate reads them: none of the
  twelve cited a law, rule or walker declaration of the form. Two use checked-type instances as
  instances, `check_cs` and `check_slot_chunks`; retiring the `check_complete` field edited
  those instances, and the drivers keep them.

The root lists in `snarky/scripts/check_axioms.lean` were not consumers: they kept the form's
results alive without using them.

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

- The rest, once every checked type had its law at the prover's reading (the pickles branch
  data's `instAllocBranchDataWPCheckedType` the last): the `check_complete` field with every
  instance's proof of it and the private `checkAll_complete`; `Complete.witness`, whose proof
  reads the field, and the laws that cite it: EndoScalar's `toField_complete_rows` with
  `toFieldChecked'_complete`, `row_complete` and their helpers, `mul_complete` and
  `square_complete`, and `CheckedPoint.check_complete`, which cites both; then
  `assertEqual_complete`, `assertSquare_complete` and `assertEq_complete`; the traversal laws;
  the walker's two modules and their attributes; and last `Runs`, `Sat`, the relation, its
  rules and `run_le`, with what only they used, `prove_le` and `CVar.monotone_scoped`. The
  field's group could not be split as the inventory ordered it: `Complete.witness` reads the
  field, the pickles instance's proof of it cited EndoScalar's chain, and the chain and the two
  DSL laws cite `Complete.witness`, so they went in one build step. No consumer appeared that
  the inventory had not listed.

The form is gone: no declaration of the package states or uses `Complete`.

## Where the results live

| Retired | At the prover's reading |
|---|---|
| `Complete` and its rules, `run_le`, `Runs`, `Sat` | `proverWP` with its `WP` and `WPMonad` instances at the `Prover c` tag (`Snarky/Prover/WP.lean`); `proverWP_prove` for what a run delivers |
| `solve_complete`'s `Complete`-form statement | `solve_spec` (`Snarky/Compile.lean`); `solve_complete` is a theorem with its statement, proved by it |
| `CheckedType.check_complete` and its instance proofs | `WPCheckedType.check_wp`, applied through `Prover.check_spec` (`Snarky/Witness.lean`), an instance beside each checked type |
| `Complete.witness` | `Prover.witness_spec` and `Prover.witness_of_run` (`Snarky/Witness.lean`) |
| `zipWithVecM_complete`, `mapAccumM_complete` | `Prover.zipWithVecM_spec`, `Prover.mapAccumM_spec`, `Prover.mapAccumM_scan_spec` (`Snarky/Traverse.lean`) |
| the DSL gadgets' `*_complete` laws | `Prover.<gadget>_spec` beside each gadget in `Snarky/DSL/` |
| `CheckedPoint.check_complete` | `instWPCheckedTypeCheckedPoint` (`Snarky/Kimchi/Circuit/CheckedPoint.lean`) |
| EndoScalar's `toField_complete_rows` chain | `Prover.toField_spec_rows`, `Prover.toField_spec` (`Snarky/Kimchi/Circuit/EndoScalar.lean`) |
| the kimchi circuits' other `*_complete` laws | each circuit's `Prover.*_spec` triples, in its module under `Snarky/Kimchi/Circuit/` |
| the walker and its attributes | `mvcgen` over the specs each gadget registers through `Prover.register` |
