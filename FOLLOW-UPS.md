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

## N2 wrap_main variant

The current `wrap_main_circuit` fixture is for `max_proofs_verified = N1` (1 real previous proof, 1 dummy padded to N2). A separate fixture and equivalence test is needed for `max_proofs_verified = N2` (2 real previous proofs), which would exercise:
- `actual_proofs_verified_mask = [true, true]`
- Two real challenge vectors in FOP (no dummy padding)
- Different message hash sponge starting states
- Full sgOld absorption with both flags true

OCaml's `dump_circuit_impl.ml` can generate this variant.

## assertAll_ is defined but uncalled

`Snarky.Circuit.DSL.Assert.assertAll_` matches OCaml's `Boolean.Assert.all` (void assertion, sum-based). It's implemented and exported but not yet called by any circuit code. It exists for completeness — the OCaml equivalent is used in some circuit paths we haven't translated yet.
