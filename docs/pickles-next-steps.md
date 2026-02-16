# Pickles Circuit Gap Analysis & Next Steps

## Current State

### Step Circuit (`Pickles.Step.Circuit`)

What OCaml `verify_one` does (`step_main.ml:23-123`):
1. Assert `shouldFinalize == mustVerify`
2. Call `Step_verifier.finalize_other_proof` -> `(finalized, chals)`
3. Compute `hash_messages_for_next_step_proof`
4. Call `Step_verifier.verify` -> `verified` (wraps `incrementallyVerifyProof` on the actual Wrap proof)
5. Return `(chals, verified &&& finalized ||| not must_verify)`

What PureScript `stepCircuit` currently does:
1. Assert `shouldFinalize == mustVerify`
2. Call `finalizeOtherProof` -> `(finalized, chals)`
3. **STUB** `hashMessagesForNextStepProofStub` -> returns zero
4. **MISSING** -- never calls `verify` / `incrementallyVerifyProof` on the Wrap proof
5. Returns only `finalized ||| not shouldFinalize` (no `verified` component)

### Wrap Circuit (`Pickles.Wrap.Circuit`)

What OCaml `wrap_main.ml` does:
1. Select branch / validate `branch_data`
2. For each unfinalized Step proof: call `Wrap_verifier.finalize_other_proof`
3. Compute `hash_messages_for_next_wrap_proof`
4. Call `Wrap_verifier.incrementally_verify_proof` on the Step proof
5. Assert digest + challenges + message hash match

What PureScript `wrapCircuit` currently does:
1. No branch selection
2. No `finalize_other_proof` for unfinalized Step proofs
3. No message hashing
4. Call `incrementallyVerifyProof` on Step proof
5. Assert digest + challenges match (partial -- no message hash assertion)

## Three Priorities

### 1. Wrap-side `finalizeOtherProof` for Step proofs

**Why it's low-hanging fruit:** `finalizeOtherProofCircuit` is already generic over field `f` and shifted type `sf`. The Step-side version (`f = Vesta.ScalarField`, `sf = Type2`) works and is tested. The Wrap side just needs `f = Pallas.ScalarField`, `sf = Type1`.

**What to build:**
- A `WrapInputBuilder.purs` (analogous to existing `StepInputBuilder.purs`) that extracts Step proof deferred values and formats them as Wrap-circuit inputs
- `buildWrapFinalizeParams`: domain generator/shifts from Step verifier index, appropriate endo coefficient, Vesta linearization polynomial
- `buildWrapFinalizeInput`: extract Step proof's PlonkMinimal, CIP, b, xi, bulletproof challenges, polynomial evaluations -- coerce Fp to Fq

**Test:** Mirror the existing `Step/FinalizeOtherProof.purs realDataSpec` -- use `createStepProofContext`, build Wrap-side params/input, run `finalizeOtherProofCircuit` on `Pallas.ScalarField`, assert `finalized = true`.

**OCaml reference:** `wrap_verifier.ml:107+` (`finalize_other_proof` for the Wrap side)

**Risk:** Getting the endo coefficient right for the Wrap side (it's `endoScalar @Pallas.BaseField @Pallas.ScalarField`, the Tock-field endo). Also getting the linearization polynomial for Vesta (currently only have Pallas linearization).

### 2. Message hashing for next wrap proof (`computeMessageForNextWrapProof`)

**Why it's isolated:** It's a pure Poseidon sponge computation -- absorb curve point + bulletproof challenges, squeeze.

**OCaml reference:** `wrap_hack.ml:46-59`:
```ocaml
Tock_field_sponge.digest Tock_field_sponge.params
  (Messages_for_next_wrap_proof.to_field_elements t
     ~g1:(fun ((x, y) : Tick.Curve.Affine.t) -> [ x; y ]))
```

**What `Messages_for_next_wrap_proof` contains:**
- `challenge_polynomial_commitment`: a Pallas curve point (the `sg` from the IPA opening)
- `old_bulletproof_challenges`: Vector of 16 scalar challenges (padded to length 2)

**What to build:**
- Replace `computeMessageForNextWrapProofStub` with real Poseidon hash
- Input: `sg` point (x, y coords) + bulletproof challenges flattened to field elements
- The sponge uses Fq (Tock field / `Pallas.ScalarField`) params

**Test:** Compute the hash in pure PureScript, compare against Rust FFI. The test infrastructure already has real bulletproof challenges from `createWrapProofContext`.

**Risk:** Low. Need to match the exact field-element serialization order from `to_field_elements`. The padded challenges (for `max_proofs_verified = 2`) need to match OCaml's `pad_challenges`.

### 3. Step-side `verify` call (IVP on Wrap proof)

**Why it's high-impact:** This is the single biggest missing piece. Without it, the Step circuit never actually verifies the Wrap proof structure -- it only checks deferred values. The OCaml returns `verified &&& finalized`, we only have `finalized`.

**What to build:**
- Add Wrap proof data to `StepInput` (commitments, opening proof, sgOld)
- Add `IncrementallyVerifyProofParams` construction from Wrap verifier index to `StepInputBuilder`
- In `stepCircuit`, call `verify @nChunks @PallasG type2ScalarOps` on the Wrap proof
- Combine: `(verified &&& finalized) ||| not mustVerify`

The `verify` function already exists and is generic. It's currently called by the Wrap circuit with `@VestaG` and `Type1`. For Step, it would be called with `@PallasG` and `Type2`.

**Test:** Extend `Step/Circuit.purs realDataSpec` -- the test already creates a real Wrap proof and runs the Step circuit. The test would now also exercise the IVP path. Can also add a sub-circuit test for Step-side IVP in isolation (similar to `Wrap/SubCircuits.purs incrementallyVerifyProofTest`).

**Risk:** The `nChunks` type parameter and commitment counts need to match the Wrap circuit's structure. Statement packing (encoding the Wrap statement as public input for the Step verifier) is needed -- OCaml does this in `step_verifier.ml verify`. This is the most involved of the three tasks.

## Summary

| Priority | Side | Effort | Impact | Isolated? |
|----------|------|--------|--------|-----------|
| 1. Wrap-side `finalizeOtherProof` | Wrap | Medium | Enables deeper recursion | Yes -- standalone circuit test |
| 2. Message hashing for next wrap proof | Step (output) | Low | Correct proof linking | Yes -- pure sponge test |
| 3. Step-side IVP (`verify` call) | Step | High | Completes basic recursion | Mostly -- touches core combinator |

Priorities 1 and 2 are genuinely low-hanging fruit. Priority 3 is the highest impact but also the most integration work. All three are grounded in specific OCaml functions with clear test strategies.
