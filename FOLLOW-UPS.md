# Follow-ups

Tracked items for future work. Each item has a tag for searchability (grep for `TODO(<tag>)` in source).

## Multi-chunk commitments — `TODO(num_chunks)`

When `num_chunks > 1` (circuits exceeding SRS polynomial degree), each polynomial commitment becomes an array of chunk points rather than a single curve point.

Affected locations:
- `StepVK` type (`VerificationKey.purs`): each field becomes `Vector numChunks (AffinePoint f)`
- `chooseKey` operations: `scalePt`, `sealPt`, `addPt` need to map over chunks
- `FqSpongeInput` (`FqSpongeTranscript.purs`): wComm/zComm/tComm need chunking
- `allBases` assembly (`Verify.purs`): totalBases scales by numChunks
- `combinePolynomials` (`IPA.purs`): needs inner loops over chunks (see OCaml `Pcs_batch.combine_split_commitments`)

Currently `num_chunks = 1` is correct for all Mina circuits. This would only matter for very large circuits exceeding the SRS degree bound.

## Retire or retarget `Pickles.Wrap.Circuit` sub-circuit — `TODO(wrap_subcircuit)`

Phase 5 of the wrap_main advice refactor introduced a separate
`WrapSubCircuitWitnessM` class in `Pickles.Wrap.Advice` to keep the
deprecated `wrapCircuit` sub-circuit (and its `WrapProverM`-based test
infrastructure in `Test.Pickles.TestContext`) compiling. It's now the
only consumer of that legacy class, and all of its real test surface
(`createWrapProofContext`, `buildWrapProverWitness`, `WrapE2E`) is
the pre-`wrap_main` shape.

Options:
- Delete `Pickles.Wrap.Circuit` and its consumers entirely, reroute
  `wrap0` in `InductiveTestContext` to use `wrapMain` directly (and
  build a `WrapMainAdvice` from a real `StepProofContext`).
- Keep `Pickles.Wrap.Circuit` but migrate it onto the new
  `WrapWitnessM` class, deleting `WrapSubCircuitWitnessM`.

The first option is cleaner; it matches what step_main did with its
predecessor sub-circuit.

## FOP domain as separate argument

`wrapFinalizeOtherProofCircuit` currently receives the per-proof domain merged into static params via `Record.merge`. Cleaner to separate static params (endo, srsLengthLog2, linearizationPoly) from per-proof domain (generator, shifts, vanishingPolynomial) as distinct arguments. See `TODO` comment in `WrapMain.purs` at the FOP call sites.

## Abstract ones_vector

The `ones_vector` logic in `WrapMain.purs` (block1) computes the `actual_proofs_verified_mask` inline. This mirrors OCaml's `Util.Wrap.ones_vector`. For the general N case (not just N1), this should be extracted as a reusable function, likely in `Pickles.Pseudo` or a utilities module.

## assertAll_ is defined but uncalled

`Snarky.Circuit.DSL.Assert.assertAll_` matches OCaml's `Boolean.Assert.all` (void assertion, sum-based). It's implemented and exported but not yet called by any circuit code. It exists for completeness — the OCaml equivalent is used in some circuit paths we haven't translated yet.
