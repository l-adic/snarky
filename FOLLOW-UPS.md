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

## CircuitType instances for WrapMain input parsing

The manual parsers in `WrapMain.purs` (`parseUnfinalizedProof`, `parseEvals`) decode flat field arrays by hardcoded offsets. These should be replaced with proper `CircuitType` newtypes that handle serialization/deserialization, matching OCaml's `Typ` mechanism for `exists`/`alloc_typ`.

Affected:
- `parseUnfinalizedProof` (27 fields) — should be a `CircuitType` instance on `UnfinalizedProof`
- `parseEvals` (89 fields) — should be a `CircuitType` instance on `AllEvals`
- `stmtTuple` construction (nested Tuples for `pack_statement`) — should be hidden behind a newtype with a clean API

## FOP domain as separate argument

`wrapFinalizeOtherProofCircuit` currently receives the per-proof domain merged into static params via `Record.merge`. Cleaner to separate static params (endo, srsLengthLog2, linearizationPoly) from per-proof domain (generator, shifts, vanishingPolynomial) as distinct arguments. See `TODO` comment in `WrapMain.purs` at the FOP call sites.

## Abstract ones_vector

The `ones_vector` logic in `WrapMain.purs` (block1) computes the `actual_proofs_verified_mask` inline. This mirrors OCaml's `Util.Wrap.ones_vector`. For the general N case (not just N1), this should be extracted as a reusable function, likely in `Pickles.Pseudo` or a utilities module.

## assertAll_ is defined but uncalled

`Snarky.Circuit.DSL.Assert.assertAll_` matches OCaml's `Boolean.Assert.all` (void assertion, sum-based). It's implemented and exported but not yet called by any circuit code. It exists for completeness — the OCaml equivalent is used in some circuit paths we haven't translated yet.
