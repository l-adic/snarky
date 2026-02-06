# FinalizeOtherProof Real Data Test Plan

## Goal

Update `Test/Pickles/Step/FinalizeOtherProof.purs` so that the `realDataSpec` test constructs **all** deferred values with real Schnorr proof data and passes with `shouldFinalize = true`. Currently only `xi_correct` uses real data; `combinedInnerProduct`, `b`, and `perm` are zero dummies.

## What the circuit does (recap)

`finalizeOtherProofCircuit` receives an `UnfinalizedProof` containing `DeferredValues` (claimed values) and a `WrapProofWitness` (evaluation data). It:

1. Expands raw 128-bit `alpha`/`zeta` via endo → full field `PlonkExpanded`
2. Absorbs `fqDigest`, `prevChallengeDigest`, all evals into Fr-sponge
3. Squeezes `rawXi`, compares with `deferred.xi` → `xiCorrect`
4. Squeezes `rawR`, expands both via endo → `polyscale`, `evalscale`
5. Computes CIP from evaluations, compares with `deferred.combinedInnerProduct` → `cipCorrect`
6. Expands 16 bulletproof challenges via endo, computes `b`, compares with `deferred.b` → `bOk`
7. Computes perm scalar, compares with `deferred.perm` → `permOk`
8. Returns `finalized = xiCorrect && cipCorrect && bOk && permOk`

## Data needed for the test

### A. FinalizeOtherProofParams (compile-time)

| Field | Source |
|---|---|
| `domain.generator` | `ProofFFI.domainGenerator ctx.domainLog2` |
| `domain.shifts` | `ProofFFI.proverIndexShifts ctx.proverIndex` |
| `endo` | `endoScalar @Vesta.BaseField @Vesta.ScalarField` |
| `zkRows` | `3` |
| `linearizationPoly` | `Linearization.pallas` |

### B. UnfinalizedProof.deferredValues

| Field | Type | How to compute |
|---|---|---|
| `plonk.alpha` | `SizedF 128 (F StepField)` | `fromField @128 ctx.oracles.alphaChal` then coerce to `F` wrapper |
| `plonk.beta` | `F StepField` | `F ctx.oracles.beta` |
| `plonk.gamma` | `F StepField` | `F ctx.oracles.gamma` |
| `plonk.zeta` | `SizedF 128 (F StepField)` | `fromField @128 ctx.oracles.zetaChal` then coerce |
| `xi` | `SizedF 128 (F StepField)` | `frSpongeChallengesPure(spongeInput).rawXi` then coerce (already done) |
| `combinedInnerProduct` | `Type1 (F StepField)` | `toType1 ctx.oracles.combinedInnerProduct` (see shifting below) |
| `b` | `Type1 (F StepField)` | `toType1 (ProofFFI.computeB0 {...})` |
| `perm` | `Type1 (F StepField)` | `toType1 (permScalar permInput)` |
| `bulletproofChallenges` | `Vector 16 (SizedF 128 (F StepField))` | Extract from IPA sponge, coerce cross-field (see below) |

**Other UnfinalizedProof fields:**
- `shouldFinalize = true`
- `spongeDigestBeforeEvaluations = F ctx.oracles.fqDigest`

### C. WrapProofWitness

| Field | Source |
|---|---|
| `allEvals.ftEval1` | `F ctx.oracles.ftEval1` |
| `allEvals.publicEvals` | `coerce { zeta: ctx.oracles.publicEvalZeta, omegaTimesZeta: ctx.oracles.publicEvalZetaOmega }` |
| `allEvals.zEvals` | `coerce (ProofFFI.proofZEvals ctx.proof)` |
| `allEvals.indexEvals` | `coerce (evalSelectorPolys ctx.proverIndex ctx.oracles.zeta)` |
| `allEvals.witnessEvals` | `coerce (ProofFFI.proofWitnessEvals ctx.proof)` |
| `allEvals.coeffEvals` | `coerce (ProofFFI.proofCoefficientEvals ctx.proof)` |
| `allEvals.sigmaEvals` | `coerce (ProofFFI.proofSigmaEvals ctx.proof)` |
| `domainValues.zkPolynomial` | `F $ ProofFFI.permutationVanishingPolynomial { domainLog2, zkRows, pt: zeta }` |
| `domainValues.zetaToNMinus1` | `F $ pow zeta n - one` |
| `domainValues.omegaToMinusZkRows` | `F $ pow omega (n - BigInt.fromInt zkRows)` |
| `domainValues.vanishesOnZk` | `F $ vanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }` |
| `domainValues.lagrangeFalse0` | `F $ unnormalizedLagrangeBasis { domainLog2, zkRows: 0, offset: 0, pt: zeta }` |
| `domainValues.lagrangeTrue1` | `F $ unnormalizedLagrangeBasis { domainLog2, zkRows, offset: -1, pt: zeta }` |
| `publicEvalForFt` | `F $ computePublicEval ctx.publicInputs ctx.domainLog2 ctx.oracles.zeta` |

### D. prevChallengeDigest

`F (emptyPrevChallengeDigest :: Vesta.ScalarField)` — no previous recursion in base case.

## Key computations explained

### Type1 shifting

The circuit stores deferred scalars as `Type1 (F StepField)` where `StepField = Vesta.ScalarField`. The shift formula is:

```
s = 2*t + 2^255 + 1    (in StepField)
t = (s - 2^255 - 1) / 2
```

where `s` is the original value and `t` is the shifted representation stored in `Type1 t`.

We define a local helper:

```purescript
toType1 :: Vesta.ScalarField -> Type1 (F StepField)
toType1 s =
  let
    shiftConst = pow (fromBigInt (BigInt.fromInt 2) :: Vesta.ScalarField) (BigInt.fromInt 255) + one
    t = (s - shiftConst) * recip (fromBigInt (BigInt.fromInt 2))
  in
    Type1 (F t)
```

### Bulletproof challenges (cross-field)

The IPA sponge operates on `Pallas.ScalarField` (commitment curve), producing `SizedF 128 Pallas.ScalarField`. The circuit needs `SizedF 128 (F Vesta.ScalarField)`.

Steps:
1. Get sponge checkpoint from `ProofFFI.pallasSpongeCheckpointBeforeChallenges`
2. Get L/R pairs from `ProofFFI.pallasProofOpeningLr`
3. Run `extractScalarChallengesPure` in pure sponge (squeeze once for `u` first)
4. `coerceViaBits` each challenge: `Pallas.ScalarField → Vesta.ScalarField`
5. `coerce` to wrap in `F`: `Vesta.ScalarField → F Vesta.ScalarField`

```purescript
rawBpChallenges :: Vector 16 (SizedF 128 Pallas.ScalarField)
rawBpChallenges = Pickles.Sponge.evalPureSpongeM ipaSpongeState do
  _ <- Pickles.Sponge.squeeze  -- squeeze for u
  IPA.extractScalarChallengesPure lrPairs

bpChallenges :: Vector 16 (SizedF 128 (F StepField))
bpChallenges = coerce $ map coerceViaBits rawBpChallenges
```

### Perm scalar

Use the pure `permScalar` function with expanded plonk values from oracles and real domain values:

```purescript
permInput :: PermutationInput Vesta.ScalarField
permInput =
  { w: map _.zeta (Vector.take @7 witnessEvals)
  , sigma: map _.zeta sigmaEvals
  , z: zEvals
  , shifts: ProofFFI.proverIndexShifts ctx.proverIndex
  , alpha: ctx.oracles.alpha      -- expanded
  , beta: ctx.oracles.beta
  , gamma: ctx.oracles.gamma
  , zkPolynomial: zkPoly
  , zetaToNMinus1
  , omegaToMinusZkRows
  , zeta: ctx.oracles.zeta        -- expanded
  }
perm = permScalar permInput
```

### b value

Use `ProofFFI.computeB0` with expanded (endo-mapped) bulletproof challenges from Rust:

```purescript
challengesArray = ProofFFI.proofBulletproofChallenges ctx.proverIndex
  { proof: ctx.proof, publicInput: ctx.publicInputs }
bValue = ProofFFI.computeB0
  { challenges: challengesArray
  , zeta: ctx.oracles.zeta
  , zetaOmega: ctx.oracles.zeta * omega
  , evalscale: ctx.oracles.u
  }
```

## New imports needed

```purescript
import Data.Fin (unsafeFinite)
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.IPA as IPA
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI (evalSelectorPolys, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.PlonkChecks.Permutation (permScalar)
import Pickles.Sponge as Pickles.Sponge
import Snarky.Curves.Class (endoScalar, fromBigInt, pow)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.SizedF (SizedF(..), coerceViaBits, fromField)
import RandomOracle.Sponge as RandomOracle
import Test.Pickles.E2E (computePublicEval, createTestContext) as E2E
```

## Unchanged parts

- `spec` (base case with dummies) — unchanged
- `dummyTestCircuit` — unchanged
- `realTestCircuit` — unchanged
- Type aliases — unchanged
- Test runner structure — unchanged

## Verification

```bash
npx spago build -p pickles
npx spago test -p pickles -- --example "FinalizeOtherProof"
```

Both tests should pass:
1. "skeleton circuit is satisfiable with dummy inputs (base case)" — uses `shouldFinalize = false`
2. "xi_correct passes with real Schnorr proof data" → rename to "all checks pass with real Schnorr proof data" since we now verify all 4 checks
