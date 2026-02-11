# Phase A: Fq-Sponge Transcript for `incrementallyVerifyProof`

## Goal

Implement and test the Fq-sponge transcript — the first sub-circuit of `incrementallyVerifyProof`. This replays the Fiat-Shamir transcript by absorbing VK + proof commitments and squeezing PLONK challenges (beta, gamma, alpha, zeta). Validate against Rust oracle FFI.

This is the smallest testable unit for the incremental proof verifier. Everything else (ft_comm, commitment batching, IPA check) depends on getting this transcript correct.

**OCaml reference**: `step_verifier.ml:504-560`

## Field Conventions

Step circuit runs on **Fp** = `Vesta.ScalarField`. The Fq-sponge operates natively on Fp — it absorbs Fp-valued curve point coordinates and squeezes Fp elements. No non-native field operations involved.

## What the Transcript Does

```
1. absorb indexDigest                                     (1 field element)
2. for each sg in sg_old: absorb sg.x, sg.y              (2n field elements)
3. absorb x_hat.x, x_hat.y                               (2 field elements)
4. for each w in w_comm[0..14]: absorb w[j].x, w[j].y    (2 * 15 * chunks field elements)
5. squeeze beta  (128-bit, constrained)
6. squeeze gamma (128-bit, constrained)
7. absorb z_comm[j].x, z_comm[j].y                       (2 * chunks field elements)
8. squeeze alpha (128-bit scalar challenge)
9. absorb t_comm[j].x, t_comm[j].y                       (2 * chunks field elements)
10. squeeze zeta (128-bit scalar challenge)
11. sponge_digest_before_evaluations = squeeze             (full field element)
```

For Pasta with wrap domain ≤ 2^16, all commitments are single-point (chunks = 1).

## Existing Code to Reuse

- `Pickles.Sponge` — `SpongeM`, `PureSpongeM`, `absorb`, `absorbPoint`, `squeeze`, `squeezeScalarChallenge`, `squeezeScalarChallengePure` (`packages/pickles/src/Pickles/Sponge.purs`)
- `lowestNBitsPure` from `Snarky.Data.SizedF` — for pure 128-bit extraction (`packages/snarky/src/Snarky/Data/SizedF.purs`)
- `SizedF.toField` — convert `SizedF 128 f` back to plain `f` for beta/gamma
- `initialSponge` — fresh sponge state
- `createTestContext` from `Test.Pickles.E2E` — existing Schnorr proof + oracles

## New FFI Required

All FFI data comes from the existing `ProverIndex` and `Proof` types already available in tests.

### Rust FFI (crypto-provider/src/kimchi/circuit.rs)

1. **`pallas_prover_index_vk_commitments`** — Extract VK commitment points from ProverIndex
   - sigma_comm (7 arrays of points), coefficients_comm (15 arrays), generic_comm, psm_comm, complete_add_comm, mul_comm, emul_comm, endomul_scalar_comm
   - Returns: JS object with `{sigmaComm, coefficientsComm, genericComm, ...}` where each is `Array<{x, y}>` or `Array<Array<{x, y}>>`

2. **`pallas_proof_messages`** — Extract proof message commitments
   - w_comm (15 arrays of points), z_comm (array of points), t_comm (array of points)
   - Returns: `{wComm, zComm, tComm}`

3. **`pallas_sponge_digest_after_index`** — Compute VK digest (squeeze from sponge_after_index)
   - Returns: single field element

4. **`pallas_x_hat`** — Compute public input commitment
   - Input: proverIndex, publicInput array
   - Returns: `{x, y}` point (already negated and blinded as per OCaml x_hat computation)

### PureScript FFI bindings (Test/Pickles/ProofFFI.purs + .js)

```purescript
pallasProverIndexVkCommitments :: ProverIndex Vesta.G Vesta.ScalarField -> WrapVerificationKey (AffinePoint Vesta.ScalarField)
pallasProofMessages :: Proof Vesta.G Vesta.ScalarField -> ProofMessages (AffinePoint Vesta.ScalarField)
pallasSpongeDigestAfterIndex :: ProverIndex Vesta.G Vesta.ScalarField -> Vesta.ScalarField
pallasXHat :: ProverIndex Vesta.G Vesta.ScalarField -> Array Vesta.ScalarField -> AffinePoint Vesta.ScalarField
```

## New Types

### `WrapVerificationKey` — `Pickles/Step/WrapVerificationKey.purs` (new file)

```purescript
type WrapVerificationKey g =
  { sigmaComm :: Vector 7 (Array g)
  , coefficientsComm :: Vector 15 (Array g)
  , genericComm :: Array g
  , psmComm :: Array g
  , completeAddComm :: Array g
  , mulComm :: Array g
  , emulComm :: Array g
  , endomulScalarComm :: Array g
  }
```

OCaml reference: `pickles_types.ml:162-175`

### `ProofMessages` — (could be in the same file or inline in test)

```purescript
type ProofMessages g =
  { wComm :: Vector 15 (Array g)
  , zComm :: Array g
  , tComm :: Array g
  }
```

## Implementation

### 1. Pure transcript function (testable without circuit)

```purescript
-- In a new module or test module
fqSpongeTranscriptPure
  :: forall n f
   . PrimeField f => PoseidonField f => FieldSizeInBits f 255
  => Reflectable n Int
  => { indexDigest :: f
     , sgOld :: Vector n (AffinePoint f)
     , xHat :: AffinePoint f
     , wComm :: Vector 15 (Array (AffinePoint f))
     , zComm :: Array (AffinePoint f)
     , tComm :: Array (AffinePoint f)
     }
  -> { beta :: f, gamma :: f
     , alphaChal :: SizedF 128 f, zetaChal :: SizedF 128 f
     , spongeDigestBeforeEvaluations :: f
     }
fqSpongeTranscriptPure input = evalPureSpongeM initialSponge do
  -- 1. Absorb VK digest
  absorb input.indexDigest
  -- 2. Absorb sg_old
  for_ input.sgOld absorbPoint
  -- 3. Absorb x_hat
  absorbPoint input.xHat
  -- 4. Absorb w_comm
  for_ input.wComm \chunks -> for_ chunks absorbPoint
  -- 5. Squeeze beta, gamma
  betaChal <- squeezeScalarChallengePure
  gammaChal <- squeezeScalarChallengePure
  -- 6. Absorb z_comm
  for_ input.zComm absorbPoint
  -- 7. Squeeze alpha
  alphaChal <- squeezeScalarChallengePure
  -- 8. Absorb t_comm
  for_ input.tComm absorbPoint
  -- 9. Squeeze zeta
  zetaChal <- squeezeScalarChallengePure
  -- 10. Squeeze digest
  spongeDigestBeforeEvaluations <- squeeze
  pure { beta: SizedF.toField betaChal, gamma: SizedF.toField gammaChal
       , alphaChal, zetaChal, spongeDigestBeforeEvaluations }
```

### 2. Test: compare against Rust oracles

```purescript
spec = beforeAll createTestContext $
  describe "Fq-sponge transcript" do
    it "produces correct challenges matching Rust oracles" \ctx -> do
      let
        vk = pallasProverIndexVkCommitments ctx.proverIndex
        messages = pallasProofMessages ctx.proof
        indexDigest = pallasSpongeDigestAfterIndex ctx.proverIndex
        xHat = pallasXHat ctx.proverIndex ctx.publicInputs

        result = fqSpongeTranscriptPure
          { indexDigest
          , sgOld: Vector.nil  -- base case: no previous proofs
          , xHat
          , wComm: messages.wComm
          , zComm: messages.zComm
          , tComm: messages.tComm
          }

      -- Compare against oracle values
      result.beta `shouldEqual` ctx.oracles.beta
      result.gamma `shouldEqual` ctx.oracles.gamma
      SizedF.toField result.alphaChal `shouldEqual` SizedF.toField ctx.oracles.alphaChal
      SizedF.toField result.zetaChal `shouldEqual` SizedF.toField ctx.oracles.zetaChal
      result.spongeDigestBeforeEvaluations `shouldEqual` ctx.oracles.fqDigest
```

**Note**: `sgOld = Vector.nil` because the base case (first proof) has no previous challenge polynomial commitments. The OCaml pads to 2 entries with dummy commitments — we need to check if this padding is needed. If so, we'd pad with the identity point or a generator.

## sg_old Padding Detail

The OCaml pads `sg_old` to `Wrap_hack.Padded_length.n` (= 2) using `pad_commitments`. For base case with 0 previous proofs, it pads with 2 dummy commitments. We need to check what the dummy value is — likely `Inner_curve.Params.one` (the curve generator) or the identity point. This affects the sponge transcript.

If the Rust `proofOracles` was computed with 0 sg_old entries (no padding), then `sgOld = Vector.nil` is correct. If the Rust includes padding, we need to match.

**Action**: Check the Rust oracle computation to determine if/how sg_old is padded.

## Files Modified

1. `packages/crypto-provider/src/kimchi/circuit.rs` — 4 new Rust FFI functions
2. `packages/pickles/test/Test/Pickles/ProofFFI.js` — JS bindings for new functions
3. `packages/pickles/test/Test/Pickles/ProofFFI.purs` — PureScript FFI types
4. `packages/pickles/src/Pickles/Step/WrapVerificationKey.purs` — **new file**, type only
5. `packages/pickles/test/Test/Pickles/Step/FqSpongeTranscript.purs` — **new test file**

## NOT Changed (yet)

- `Pickles/Step/Types.purs` — DeferredValues extension deferred to Phase B
- `Pickles/Step/Dummy.purs` — deferred
- `Pickles/Sponge.purs` — no changes needed (existing `squeezeScalarChallengePure` suffices)
- `Pickles/IPA.purs` — not involved in this phase

## Verification

```bash
# Build crypto-provider with new FFI
npm run build:crypto

# Build pickles
npx spago build -p pickles

# Run just the transcript test
npx spago test -p pickles -- --example "Fq-sponge transcript"

# Verify existing tests still pass
npx spago test -p pickles
```

Success criteria: `fqSpongeTranscriptPure` produces beta, gamma, alphaChal, zetaChal, and fqDigest that exactly match the Rust `proofOracles` output.

## Follow-up Phases (not in this plan)

- **Phase B**: Circuit version of sponge transcript + DeferredValues extension
- **Phase C**: ft_comm + combineSplitCommitments
- **Phase D**: Full `incrementallyVerifyProof` composing all sub-circuits
