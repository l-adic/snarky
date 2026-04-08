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

## Refactor wrap_main to advice pattern (symmetric to step_main) — `TODO(wrap_main_advice)`

step_main now uses a clean advice pattern (`Pickles.Step.Main.stepMain` takes a rule, allocates everything via `exists advice` in OCaml hlist order, Unit input → flat output Vector). wrap_main does NOT — it cheats.

**Current wrap_main shortcut:**
- OCaml fixture `mina/src/lib/crypto/pickles/dump_circuit_impl.ml:2147 wrap_main_circuit` is INLINED. Takes a flat input array, uses `var_of_fields` to allocate structured vars manually, replacing each `exists ~request`. Does NOT call the production `Wrap_main.wrap_main`.
- PureScript `Pickles.Wrap.Main.wrapMainCircuit` takes a `WrapMainAdvice` record of pre-allocated CVars built by `parseUnfinalizedProof`/`parseEvals` from public input parsing in the test wrappers. The "advice" name is a misnomer — it's just typed CVars, not advice in any monadic sense.

**Why this is wrong for top-level circuits:** Sub-circuit fixtures can cheat with public-input parsing. wrap_main and step_main are top-level — in production, all this data MUST enter via `exists ~request:...` (private witness from prover requests), not via public input. step_main is now correct; wrap_main is still wrong.

**Required refactor:**

OCaml side:
- Add `wrap_main_for_dump.ml` mirroring `step_main_for_dump.ml` — calls real `Wrap_main.wrap_main` with `~input_typ:Typ.unit` and `~request:Req.*` for all witnesses
- Regenerate `wrap_main_circuit.json`, `wrap_main_n2_circuit.json` (and any other variants) with matching gate_labels.jsonl and cached_constants.json

PureScript side:
- Refactor `Pickles.Wrap.Main.wrapMainCircuit` to take Unit input, do its own `exists advice` allocations in OCaml hlist order, return wrap statement as flat output Vector
- Delete `WrapMainAdvice`, `parseUnfinalizedProof`, `parseEvals` (this obsoletes the previous "CircuitType instances for WrapMain input parsing" follow-up)
- Test wrappers in `pickles-circuit-diffs` become thin specializations like `compileStepMainSimpleChain` — just config + a `compileWrapMain` call

**Scope:** Bigger than step_main work because wrap_main has more variety (branches, step_widths, slot widths, choose_key, feature flags). Multiple wrap fixtures to regenerate.

**Reference pattern:** `packages/pickles/src/Pickles/Step/Main.purs` (the symmetric step_main library — uses `throwAsProver` for advice via `Pickles.Step.Main.advice`, individual `exists` calls in OCaml hlist order, parameterized by `n` and rule).

## FOP domain as separate argument

`wrapFinalizeOtherProofCircuit` currently receives the per-proof domain merged into static params via `Record.merge`. Cleaner to separate static params (endo, srsLengthLog2, linearizationPoly) from per-proof domain (generator, shifts, vanishingPolynomial) as distinct arguments. See `TODO` comment in `WrapMain.purs` at the FOP call sites.

## Abstract ones_vector

The `ones_vector` logic in `WrapMain.purs` (block1) computes the `actual_proofs_verified_mask` inline. This mirrors OCaml's `Util.Wrap.ones_vector`. For the general N case (not just N1), this should be extracted as a reusable function, likely in `Pickles.Pseudo` or a utilities module.

## assertAll_ is defined but uncalled

`Snarky.Circuit.DSL.Assert.assertAll_` matches OCaml's `Boolean.Assert.all` (void assertion, sum-based). It's implemented and exported but not yet called by any circuit code. It exists for completeness — the OCaml equivalent is used in some circuit paths we haven't translated yet.
