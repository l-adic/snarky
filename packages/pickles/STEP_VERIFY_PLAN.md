# Fix Plan: Self-Consistent Base Case Unfinalized Proof

## Root Cause

The base case test uses `Dummy.stepDummyUnfinalizedProof` (Ro-derived values from
`unfinalized.ml:Constant.dummy`) as the active proof slot's unfinalized proof. But
OCaml's prover uses `expand_proof` (step.ml:515-536) which computes values from the
actual proof data via `Oracles.create`. The Ro-derived values are only for **padding**
unused slots.

## What expand_proof computes

Given advisory data (VK, commitments, opening proof), compute:

1. **Sponge transcript** → beta, gamma, alpha, zeta, spongeDigestBeforeEvaluations
2. **Fr-sponge** → xi, evalscale
3. **Derived deferred values** → CIP, b, perm, zetaToSrsLength, zetaToDomainSize

## Changes

### Step 1: Lagrange comms for base case

`createStepProofContext BaseCase` already creates CRS. Compute lagrange comms from
CRS + known public input size (`sizeInFields` of WrapStatementPublicInput).

### Step 2: `computeStepIvpTranscript` (TestContext.purs)

Pure Poseidon sponge in IVP order on dummy data:
- Absorb VK → index_digest
- Absorb sgOld
- Compute x_hat (publicInputCommit on Wrap Statement)
- Absorb x_hat, wComm → squeeze beta, gamma
- Absorb zComm → squeeze alpha
- Absorb tComm → squeeze zeta
- Squeeze spongeDigest

Returns { beta, gamma, alpha, zeta, spongeDigest }.

### Step 3: `buildBaseCaseUnfinalizedProof` (TestContext.purs)

Uses transcript output + dummy evals to build self-consistent UnfinalizedProof:
- plonk.{alpha,beta,gamma,zeta} ← from transcript
- spongeDigestBeforeEvaluations ← from transcript
- CIP, b, perm, zetaToSrsLength, zetaToDomainSize ← derived from plonk + evals
- xi ← from Fr-sponge
- bulletproofChallenges ← Wrap IPA (N=15)
- shouldFinalize ← false

### Step 4: Update test generators

Replace `stepDummyUnfinalizedProof` in active slot with `buildBaseCaseUnfinalizedProof`.
Keep `stepDummyUnfinalizedProof` for padding unused slots.

### Step 5: Wire IVP back into stepCircuit

Re-enable the `incrementallyVerifyProof` call in the per-proof loop.

### Step 6: Verify

- All 60 pickles tests pass
- All 50 circuit-diff tests pass
