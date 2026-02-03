# Pickles Architecture Diagrams Index

This document indexes the official Pickles architecture diagrams and maps them to implementation checkpoints.

**Source**: [o1-labs/proof-systems book](https://o1-labs.github.io/proof-systems/) - these diagrams are human-created and may have minor inaccuracies, but represent the best available map of the system.

**Original drawio file**: `vendor/proof-systems/book/src/pickles/pickles_structure.drawio`

---

## Critical Architecture Constraint: Rust FFI as Ground Truth

**All proof generation and cryptographic computation happens in Rust (proof-systems).**

### The Rule

We **NEVER** implement cryptographic primitives from scratch in PureScript. proof-systems is treated as **given by god** - our job is to match whatever it does exactly.

### FORBIDDEN: Re-implementing in FFI

When testing that PureScript matches proof-systems, you must **NEVER** re-implement proof-systems logic in the FFI layer (`crypto-provider/`). This defeats the purpose - you'd just be testing PureScript against your own re-implementation, not against the actual proof-systems behavior.

❌ **WRONG**: Write new Rust code in `crypto-provider/` that re-implements the algorithm
❌ **WRONG**: Copy-paste logic from proof-systems into FFI wrapper
❌ **WRONG**: "Simplify" or "extract" the algorithm into standalone FFI function

### CORRECT: Modify vendored proof-systems to expose internals

Because `vendor/proof-systems/` is a locally vendored dependency, you **CAN and SHOULD** modify it to expose values or methods that aren't currently public.

✅ **RIGHT**: Add `pub` to an existing private field/method
✅ **RIGHT**: Add a new method that returns internal state (like `checkpoint()`)
✅ **RIGHT**: Make a private struct field public for testing access

### Example: Sponge State Checkpoint

To test that PureScript sponge matches Rust sponge state, we modified `vendor/proof-systems/poseidon/src/sponge.rs`:

```rust
// Added to FqSponge trait:
fn checkpoint(&self) -> SpongeCheckpoint<Fq>;

// New struct to expose internal state:
pub struct SpongeCheckpoint<F> {
    pub state: Vec<F>,
    pub sponge_state: SpongeState,
    pub last_squeezed: Vec<u64>,
}
```

Now the FFI calls `sponge.checkpoint()` to get the **actual** internal state - no re-implementation needed.

### Why This Matters

- proof-systems is the audited, battle-tested implementation
- It sets the "ground truth" for exact data formats
- Re-implementing risks subtle bugs that make tests pass but diverge from reality
- Exposing internals guarantees you're testing against the real thing

### What This Means for Implementation

1. **Prover-side computations** (left side of diagrams) → Expose from Rust via vendored lib modifications, call via FFI
2. **In-circuit verification** (right side of diagrams) → PureScript circuits that *verify* Rust-computed values
3. **Testing** → Rust exposes ground truth (modify vendor if needed), PureScript must match exactly

### Existing FFI: `Test.Pickles.ProofFFI`

Located at `packages/pickles/test/Test/Pickles/ProofFFI.purs`, this module exposes:

```purescript
class ProofFFI f g | f -> g where
  createProof :: { proverIndex, witness } -> Proof g f
  proofOracles :: ProverIndex -> { proof, publicInput } -> OraclesResult f
  proofWitnessEvals :: Proof -> Vector 15 (PointEval f)
  proofZEvals :: Proof -> PointEval f
  proofSigmaEvals :: Proof -> Vector 6 (PointEval f)
  proofCoefficientEvals :: Proof -> Vector 15 (PointEval f)
  proofBulletproofChallenges :: ProverIndex -> { proof, publicInput } -> Array f
  computeB0 :: { challenges, zeta, zetaOmega, evalscale } -> f
  verifyOpeningProof :: ProverIndex -> { proof, publicInput } -> Boolean
  permutationVanishingPolynomial :: { domainLog2, zkRows, pt } -> f
  domainGenerator :: Int -> f
  proverIndexShifts :: ProverIndex -> Vector 7 f
  proofIpaRounds :: Proof -> Int
```

**OraclesResult** (Fiat-Shamir derived values):
```purescript
type OraclesResult f =
  { alpha, beta, gamma, zeta :: f      -- challenges
  , v :: f                              -- polyscale (xi in diagrams)
  , u :: f                              -- evalscale (r in diagrams)
  , combinedInnerProduct :: f
  , ftEval0, ftEval1 :: f
  , publicEvalZeta, publicEvalZetaOmega :: f
  }
```

### Mapping Diagram Values to FFI

| Diagram Value | FFI Source |
|---------------|------------|
| `zeta` | `proofOracles.zeta` |
| `zetaw` | `proofOracles.zeta * domainGenerator(log2)` |
| `xi` (polyscale) | `proofOracles.v` |
| `r` (evalscale) | `proofOracles.u` |
| `b` | `computeB0` |
| `combined_inner_product` | `proofOracles.combinedInnerProduct` |
| `bulletproof_challenges` | `proofBulletproofChallenges` |
| `plonk0` / `ft_eval0` | `proofOracles.ftEval0` |
| witness evals | `proofWitnessEvals` |
| z evals | `proofZEvals` |
| sigma evals | `proofSigmaEvals` |

### Testing Pattern

```
1. Create circuit + prover index (PureScript circuit definition, Rust compilation)
2. Generate proof via Rust FFI (createProof)
3. Extract oracles/evals/challenges via FFI (ground truth)
4. Feed values into PureScript circuit as witness
5. Assert circuit:
   - Accepts valid proof data
   - Rejects tampered data (negative tests)
```

---

## Diagram Legend

From the official docs:
- **Black boxes**: Data structures (names match implementation)
- **Blue boxes**: Computations
- **Blue arrows**: Data movement (little/no transformation)
- **Light blue arrows**: Witness queries via `handler` mechanism
- **Chicken foot connector**: Accessing one field in an array (inside a loop)
- **MFNStep/MFNWrap**: Abbreviations for `MessagesForNextStep`/`MessagesForNextWrap`

**Color coding for data origin**:
- Pink/Magenta: Current computation inputs
- Green: Computed outputs
- Colors indicate "how many steps ago this data was created"

---

## Diagram 1: Wrap Computation

**Local**: [pickles-diagrams/wrap.svg](./pickles-diagrams/wrap.svg)
**Remote**: https://o1-labs.github.io/proof-systems/assets/files/pickles_structure_wrap-a9060c0d6aac8b7cec74d308b91f3f1b.svg

**OCaml files**:
- Left side (prover): `wrap.ml`
- Right side (circuit): `wrap_main.ml`, `wrap_verifier.ml`

### What it shows

The Wrap circuit **verifies a Step proof** (Tick→Tock direction).

#### Left Side: Prover Work (wrap.ml)

```
Input: prev_statement: StepStatement
         ↓
    StepProofState
         ↓
       MFNStep ──→ challenge_poly_commitment, old_bulletproof_challenges
         ↓
    StepStatementWithHashes (hashes statement for circuit)
         ↓
      ProverProof ──→ commitments, evals, prev_challenges, ft_eval1
         ↓
     OpeningProof ──→ sg, lr, delta, z1, z2
         ↓
       AllEvals (packages evaluations for circuit input)
```

#### Right Side: Circuit Work (wrap_main.ml, wrap_verifier.ml)

```
Input: WrapStatement (the new statement being proven)
         ↓
    WrapProofState ──→ sponge_digest_before_evaluations
         ↓
    WrapDeferredValues ──→ xi, plonk, combined_inner_product,
                          bulletproof_challenges, branch_data
         ↓
       MFNWrap ──→ challenge_poly_commitment (computed in-circuit)
         ↓
       Prove (verification logic)
         ↓
      WrapProof (output)
```

### Key Data Structures

| Structure | Contents | Role |
|-----------|----------|------|
| `StepProofState` | Unfinalized proof data | Input from step |
| `MFNStep` | `challenge_poly_commitment`, `old_bulletproof_challenges` | Messages passed to wrap |
| `WrapDeferredValues` | `xi`, `plonk`, `combined_inner_product`, `bulletproof_challenges`, `branch_data` | Expensive values computed outside, verified inside |
| `OpeningProof` | `sg`, `lr`, `delta`, `z1`, `z2` | IPA opening proof components |
| `AllEvals` | Polynomial evaluations at `zeta`, `zeta*omega` | Circuit inputs |

---

## Diagram 2: Wrap Deferred Values Computation

**Local**: [pickles-diagrams/wrap-deferred-values.svg](./pickles-diagrams/wrap-deferred-values.svg)
**Remote**: https://o1-labs.github.io/proof-systems/assets/files/pickles_structure_wrap_deferred_values-327d1d8f136e278946506014880e2653.svg

**OCaml file**: `wrap.ml` (the blue box in the middle of Diagram 1's left pane)

### What it shows

How `WrapDeferredValues` are computed by the prover.

#### Inputs (Pink boxes)

- `sgs` - Structured reference string
- `actual_feature_flags` - Feature configuration
- `prev_challenges` - Previous recursive challenges
- `step_vk` - Step circuit verification key
- `public_input` - Public input data
- `proof` - The step proof being wrapped
- `actual_proof_verified` - Verification status
- `proof.with_public_evals` - Proof with public evaluations

#### Computation Flow

```
Inputs ──→ O.create_with_public_evals (oracle creation)
              ↓
         Pow_2_roots_of_unity (domain setup)
              ↓
         scalars_env (static config):
           - endo, mds, zk_rows, field_of_hex
           - tick_plonk_minimal, tick_combined_evals
           - domain
              ↓
         Combined Inner Product computation:
           - plonk0 (initial PLONK evaluation)
           - r = o.u, xi = o.v (challenge values)
           - zeta = o.zeta (evaluation point)
           - zetaw = zeta * w (shifted point)
           - new_bulletproof_challenges (IPA folding)
           - b = challenge_poly(zeta) + r * challenge_poly(zetaw)
           - p_eval_1, p_eval_2
           - x_hat (combined inner product)
```

#### Output: WrapDeferredValues

- `x_hat_evals` - Evaluation results
- `digest` - Sponge digest
- `proofs_verified` - Verification flags
- `domain_log2` - Domain size

### Key Insight

The `b` value formula is critical:
```
b = challenge_poly(zeta) + r * challenge_poly(zetaw)
```
This connects the IPA challenge polynomial to the deferred values.

---

## Diagram 3: Step Computation

**Local**: [pickles-diagrams/step.svg](./pickles-diagrams/step.svg)
**Remote**: https://o1-labs.github.io/proof-systems/assets/files/pickles_structure_step-0388a70aaf48067e7906836e3ff5df5a.svg

**OCaml files**:
- Left side (prover): `step.ml`
- Right side (circuit): `step_main.ml`

### What it shows

The Step circuit **verifies Wrap proof(s)** (Tock→Tick direction) AND runs application logic.

#### Left Side: Prover Work (step.ml)

```
Input: branch_data containing:
         - index, proofs_verified, rule, requests
         - lte, main, feature_flags, domains
              ↓
         expand_proof function:
           - Unpacks previous wrap proof
           - Recomputes deferred values
           - Creates oracle from (dlog_vk, challenge_commitments,
                                  prev_challenges, public_input, proof)
           - Derives new_bulletproof_challenges and b
           - Generates witness data
           - Computes combined inner product
              ↓
         Outputs to circuit:
           - challenge_polynomial_commitments
           - unfinalized_proofs (Vec<PerProof>)
           - statement_with_hashes
           - witnesses, x_hats
```

#### Right Side: Circuit Work (step_main.ml)

```
    StepProofState ──→ unfinalized_proofs, deferred_values
         ↓
    StepDeferredValues:
      - xi, plonk, combined_inner_product, b
      - bulletproof_challenges
      - sponge_digest_before_evaluations
         ↓
       MFNStep ──→ challenge_poly_commitment, deferred_values
         ↓
      StepProof (output):
        - index, statement, proof, prev_evaluations
```

### Key Function: expand_proof

This is the heart of step.ml. It:
1. Takes a previous wrap proof
2. Partially re-runs verification to extract data
3. Generates witness for the step circuit

---

## The Complete Recursive Cycle

```
                    ┌────────────────────────────────────────┐
                    │                                        │
                    ▼                                        │
WrapProof(s) ──expand_proof──► StepCircuit ──prove──► StepProof
   (Tock)           │              (Tick)                (Tick)
                    │                                        │
                    │    deferred_values                     │
                    │         ↓                              │
                    │    WrapCircuit ◄───────────────────────┘
                    │       (Tock)
                    │         │
                    │         ▼
                    └──── WrapProof
                          (Tock)
```

**Step** (Tick/Pallas curve, Fq field):
- Verifies previous wrap proof(s)
- Runs application logic
- Outputs step proof

**Wrap** (Tock/Vesta curve, Fp field):
- Verifies previous step proof
- No application logic (just accumulation)
- Outputs wrap proof

**Deferred values** bridge the gap:
- Expensive to compute in-circuit
- Computed by prover, verified by circuit
- `b`, `combined_inner_product`, `bulletproof_challenges` carry IPA state

---

## Implementation Checkpoint Mapping

Based on the diagrams, here are the atomic units we need:

### Data Structures (from diagrams)

| Checkpoint | Structure | Diagram | Notes |
|------------|-----------|---------|-------|
| DS-1 | `StepStatement` / `WrapStatement` | All | Public statement types |
| DS-2 | `StepProofState` / `WrapProofState` | Step/Wrap | Aggregated proof state |
| DS-3 | `StepDeferredValues` / `WrapDeferredValues` | Step/Wrap | The bridge values |
| DS-4 | `MFNStep` / `MFNWrap` | Step/Wrap | Messages for next proof |
| DS-5 | `OpeningProof` | Wrap | IPA opening: sg, lr, delta, z1, z2 |
| DS-6 | `AllEvals` | Wrap DV | Packaged evaluations |
| DS-7 | `PerProof` / `unfinalized_proofs` | Step | Per-proof data in batch |

### Computations (blue boxes in diagrams)

| Checkpoint | Computation | Diagram | OCaml Location |
|------------|-------------|---------|----------------|
| C-1 | Oracle creation (`O.create_with_public_evals`) | Wrap DV | wrap.ml |
| C-2 | Domain setup (`Pow_2_roots_of_unity`) | Wrap DV | wrap.ml |
| C-3 | `scalars_env` construction | Wrap DV | wrap.ml |
| C-4 | Combined inner product | Wrap DV | wrap.ml |
| C-5 | `challenge_poly` evaluation | Wrap DV | wrap.ml |
| C-6 | `b` computation | Wrap DV, Step | Both |
| C-7 | `expand_proof` | Step | step.ml |
| C-8 | Statement hashing | Wrap, Step | Both |
| C-9 | `Prove` (in-circuit verification) | Wrap, Step | wrap_main.ml, step_main.ml |

### In-Circuit Verifier Components

| Checkpoint | Component | Diagram Side |
|------------|-----------|--------------|
| V-1 | Sponge (absorb/squeeze) | Right (circuit) |
| V-2 | Scalar challenge derivation | Right (circuit) |
| V-3 | PLONK constraint evaluation | Right (circuit) |
| V-4 | Permutation argument | Right (circuit) |
| V-5 | IPA/Bulletproof verification | Right (circuit) |
| V-6 | Deferred values consistency check | Right (circuit) |

---

## Suggested Implementation Order

Based on data dependencies visible in diagrams:

### Phase A: Data Structure Foundation
1. DS-1: Statement types
2. DS-3: Deferred values types
3. DS-4: MFN types
4. DS-5: Opening proof types

### Phase B: Prover-Side Computations (Left side of diagrams)
1. C-1: Oracle creation
2. C-2: Domain utilities
3. C-5: Challenge polynomial
4. C-6: `b` computation
5. C-4: Combined inner product
6. C-3: scalars_env
7. C-7: expand_proof (composes above)

### Phase C: In-Circuit Verifier (Right side of diagrams)
1. V-1, V-2: Sponge + challenges (DONE per existing plan)
2. V-3, V-4: PLONK checks (IN PROGRESS per existing plan)
3. V-5: IPA verification (BulletproofVerifier.purs exists)
4. V-6: Deferred values check
5. C-9: Full Prove composition

### Phase D: Integration
1. C-8: Statement hashing
2. Wrap circuit assembly
3. Step circuit assembly
4. End-to-end recursive proof

---

## Cross-Reference: Existing PureScript Implementation

### In-Circuit Components (packages/pickles/src/)

| Module | Checkpoint | What It Provides | Status |
|--------|------------|------------------|--------|
| `Pickles/Sponge.purs` | V-1 | StateT wrapper around Poseidon sponge (circuit + pure versions) | ✓ Done |
| `Pickles/ScalarChallenge.purs` | V-2 | Challenge types (alpha, beta, gamma, zeta), squeeze functions, 128-bit extraction | ✓ Done |
| `Pickles/PlonkChecks/GateConstraints.purs` | V-3 | Gate constraint verification circuit using linearization AST | ✓ Done |
| `Pickles/PlonkChecks/Permutation.purs` | V-4 | Permutation argument contribution to ft_eval0 | ✓ Done |
| `Pickles/BulletproofVerifier.purs` | V-5 | IPA verification circuits (from step_verifier.ml check_bulletproof) | Partial |
| `Pickles/Commitments.purs` | C-4, C-5, C-6 | `bPoly`, `computeB`, `combinedInnerProduct` (circuit + pure) | ✓ Done |

### Linearization Support (packages/pickles/src/Pickles/Linearization/)

| Module | Purpose |
|--------|---------|
| `Types.purs` | `GateType`, `Column`, `PolishToken`, `ChallengeTerm`, `ConstantTerm` |
| `Env.purs` | Environment record for evaluating constraint polynomials |
| `Interpreter.purs` | Stack-based interpreter for Polish notation AST |
| `FFI.purs` | Rust bindings for linearization evaluation (ground truth) |
| `Pallas.purs`, `Vesta.purs` | Curve-specific linearization data (generated) |

### Test Infrastructure (packages/pickles/test/)

| Module | Purpose |
|--------|---------|
| `Test/Pickles/ProofFFI.purs` | Rust FFI for proof creation, oracle extraction, evaluation extraction |
| `Test/Pickles/Linearization.purs` | Tests comparing PS interpreter vs Rust evaluator |
| `Test/Pickles/Permutation.purs` | Permutation argument tests |
| `Test/Pickles/BulletproofVerifier.purs` | IPA verification tests |
| `Test/Pickles/Commitments.purs` | Commitment computation tests |

### What's Missing (Not Yet Implemented)

| Category | Missing Items |
|----------|---------------|
| Data Structures | `StepStatement`, `WrapStatement`, `MFNStep`, `MFNWrap`, `StepProofState`, `WrapProofState`, `StepDeferredValues`, `WrapDeferredValues` |
| Prover-Side | `expand_proof`, oracle creation, statement hashing |
| Verifier Composition | Full `ft_eval0` check (combining gate + permutation + boundary), `finalize_other_proof` |
| Circuit Assembly | `StepVerifier`, `WrapVerifier`, `step_main`, `wrap_main` |
| Integration | End-to-end recursive proof cycle |

### Note on Linearization

The Linearization module evaluates the Kimchi constraint polynomial (a large AST in Polish notation). This is **definitely useful** for the full PLONK verification - it computes the `constant_term` that appears in the `ft_eval0 = perm_contribution - constant_term + boundary_quotient = 0` equation.

---

## What Needs Exposing from proof-systems

As we implement checkpoints, we'll likely need to expose additional functionality from the vendored `vendor/proof-systems/`. Track needed exposures here:

| Needed | proof-systems Location | For Checkpoint | Status |
|--------|----------------------|----------------|--------|
| (placeholder) | (to be determined) | (to be determined) | Not started |

**Process**: When a checkpoint requires data/computation not yet exposed:
1. Find where it lives in proof-systems (Rust)
2. Add a public function/method if needed
3. Create napi-rs binding in crypto-provider
4. Add PureScript FFI binding

---

## Open Questions (from diagrams)

1. **"shift_value (?)"** in Wrap DV diagram - what is this transformation?
2. **Color semantics** - need to trace data origin more carefully
3. **Handler mechanism** (light blue arrows) - how does witness query work?
4. **MFN padding** - how are messages padded for variable proof counts?

---

## TODO List

| # | Task | Status | Checkpoint |
|---|------|--------|------------|
| 1 | Validate `computeB` against Rust FFI `computeB0` | ✓ Done | C-6 |
| 2 | Validate bulletproof challenge extraction against Rust FFI | ✓ Done | C-5 |

---

## TODO Details

### TODO 1: Validate `computeB` against Rust FFI `computeB0`

**Goal**: Verify that our PureScript `Commitments.computeB` produces the same result as Rust's `computeB0` when given real proof data.

**Why this is the smallest testable unit**:
- All FFI pieces already exist (`computeB0`, `proofBulletproofChallenges`, `proofOracles`)
- PureScript implementation exists (`Commitments.computeB`, `Commitments.bPoly`)
- Current tests only compare circuit vs pure PureScript, NOT against Rust ground truth
- This validates the critical `b` formula from the diagrams

#### Source File Mapping

| Layer | File | Function/Location |
|-------|------|-------------------|
| **Rust** | `vendor/proof-systems/poly-commitment/src/commitment.rs:370-380` | `b_poly<F>(chals, x)` |
| **Rust** | `vendor/proof-systems/poly-commitment/src/commitment.rs:382-394` | `b_poly_coefficients<F>(chals)` |
| **OCaml** | `mina/src/lib/pickles/wrap_verifier.ml:16-38` | `G.challenge_polynomial` |
| **OCaml** | `mina/src/lib/pickles/wrap_deferred_values.ml:183-188` | `b_actual` computation |
| **PureScript** | `packages/pickles/src/Pickles/Commitments.purs` | `bPoly`, `computeB` |
| **FFI** | `packages/pickles/test/Test/Pickles/ProofFFI.purs` | `computeB0` |

#### The Formula

```
b_poly(chals, x) = ∏_i (1 + chals[i] * x^{2^{k-1-i}})

b = b_poly(chals, zeta) + r * b_poly(chals, zetaOmega)
```

Where:
- `chals` = bulletproof challenges (from `proofBulletproofChallenges`)
- `zeta` = evaluation point (from `proofOracles.zeta`)
- `zetaOmega` = shifted evaluation point (`zeta * domainGenerator`)
- `r` = evalscale (from `proofOracles.u`)

#### Implementation Plan

1. **Create test in `Test/Pickles/Commitments.purs`** (or new file `Test/Pickles/CommitmentsFFI.purs`):
   ```purescript
   it "computeB matches Rust computeB0" do
     -- 1. Create a simple circuit and prover index
     -- 2. Generate a proof via createProof
     -- 3. Extract challenges via proofBulletproofChallenges
     -- 4. Extract zeta, u (evalscale) from proofOracles
     -- 5. Compute zetaOmega = zeta * domainGenerator(domainLog2)
     -- 6. Call PureScript computeB
     -- 7. Call Rust computeB0
     -- 8. Assert equal
   ```

2. **Test data flow**:
   ```
   ProverIndex ──createProof──► Proof
        │                          │
        │                          ├── proofBulletproofChallenges ──► challenges
        │                          │
        └── proofOracles ──────────┴──► { zeta, u (evalscale) }
                                            │
                                            ▼
                              zetaOmega = zeta * domainGenerator
                                            │
                                            ▼
                         ┌──────────────────┴──────────────────┐
                         │                                     │
                    computeB (PS)                        computeB0 (Rust)
                         │                                     │
                         └─────────── assert equal ────────────┘
   ```

3. **Potential issues to watch**:
   - Challenge ordering (Rust vs OCaml vs our PureScript)
   - Number of IPA rounds / challenge count
   - Domain generator computation

4. **Success criteria**:
   - Test passes for both Pallas and Vesta curves
   - Multiple proof instances (QuickCheck or at least 3-5 hardcoded)

---

### TODO 2: Validate bulletproof challenge extraction against Rust FFI

**Goal**: Verify that PureScript sponge absorb/squeeze produces the same bulletproof challenges as Rust when processing IPA opening proof `lr` pairs.

**Generic**: Curve-agnostic. Same algorithm for Step (Pallas) and Wrap (Vesta) - parameterized by field type.

#### What's Already Tested

`Test.Pickles.BulletproofVerifier.bulletReduceSpec` validates:
```
bulletReduceCircuit  ==  PureScript pure reference
```
This passes ✓. But it only proves circuit matches PureScript - **not** that PureScript matches Rust.

#### What This TODO Adds

```
PureScript pure reference  ==  Rust FFI ground truth
```

Specifically: `squeezeScalarChallengePure` + `toEndoMapped` == `proofBulletproofChallenges`

#### Challenge Representation (Important!)

Challenges undergo 128-bit truncation + endo expansion:

1. **Squeeze** → full field element (~255 bits)
2. **Truncate** → 128 bits (`SizedF 128`) - fits in both Pallas and Vesta fields
3. **Endo expand** → `a * endo + b` gives full field scalar

Evidence from Rust (`vendor/proof-systems/poseidon/src/sponge.rs`):
```rust
pub const CHALLENGE_LENGTH_IN_LIMBS: usize = 2;  // 128 bits

pub fn to_field(&self, endo_coeff: &F) -> F {
    let length_in_bits = 64 * CHALLENGE_LENGTH_IN_LIMBS;  // = 128
    self.to_field_with_length(length_in_bits, endo_coeff)
}
```

**Critical**: `proofBulletproofChallenges` returns endo-mapped full field values. Our `squeezeScalarChallengePure` returns raw 128-bit. Test must apply `toEndoMapped` before comparing.

#### Implementation Plan

1. **Expose `lr` pairs from vendored proof-systems** (NOT re-implement in crypto-provider):

   The `OpeningProof` struct in `vendor/proof-systems/poly-commitment/src/ipa.rs` has:
   ```rust
   pub struct OpeningProof<G: AffineRepr> {
       pub lr: Vec<(G, G)>,  // Already public!
       pub delta: G,
       pub z1: G::ScalarField,
       pub z2: G::ScalarField,
       pub sg: G,
   }
   ```

   The `lr` field is already public. FFI just needs to access `proof.opening.lr` directly.

2. **Add thin FFI wrapper** in `crypto-provider/` and `ProofFFI.purs`:
   ```purescript
   proofOpeningLR :: Proof g f -> Array { l :: AffinePoint f, r :: AffinePoint f }
   ```
   This wrapper just reads existing fields - no algorithm re-implementation.

3. **Create test**:
   ```purescript
   it "PS challenge extraction matches Rust proofBulletproofChallenges" do
     -- 1. Get lr pairs via proofOpeningLR FFI
     -- 2. Run PS: absorb each (L,R), squeeze 128-bit, apply toEndoMapped
     -- 3. Get Rust challenges via proofBulletproofChallenges
     -- 4. Assert PS challenges == Rust challenges (element-wise)
   ```

4. **Run for both curves** (like existing tests)

#### Potential Issues
- Sponge initial state (must match Rust - check if CIP is absorbed first)
- Point coordinate ordering in absorb
- The endo coefficient must match between PS and Rust

#### Success Criteria
- All challenges match exactly for both Pallas and Vesta curves

---

## Completion Notes

### TODO 1: Validate `computeB` against Rust FFI `computeB0`

**Completed**: 2026-02-01

**Findings**: The test was already implemented in `packages/pickles/test/Test/Pickles/E2E.purs` as `computeBTest` (lines 391-423).

**Implementation location**: `Test.Pickles.E2E.computeBTest`

**What the test does**:
1. Uses the shared `TestContext` created by `beforeAll createTestContext`, which:
   - Generates a valid Schnorr signature
   - Builds and compiles a Schnorr verification circuit (Vesta field)
   - Creates a prover index and generates a proof via `ProofFFI.createProof`
   - Extracts oracles via `ProofFFI.proofOracles`

2. Extracts bulletproof challenges via `ProofFFI.proofBulletproofChallenges`

3. Converts challenges to a type-safe `Vector 16` (16 = IPA rounds for SRS size)

4. Computes `zetaOmega = zeta * domainGenerator(domainLog2)`

5. Calls PureScript `computeB challenges { zeta, zetaOmega, evalscale: oracles.u }`

6. Calls Rust FFI `computeB0 { challenges, zeta, zetaOmega, evalscale }`

7. Asserts equality: `psResult `shouldEqual` rustResult`

**Test execution**:
```
$ npx spago test -p pickles -- --example "computeB"
E2E Schnorr Circuit
  ✓ PS computeB matches Rust computeB0
```

**Coverage notes**:
- Currently tests Vesta field only (via Schnorr circuit which uses `Vesta.ScalarField = Pallas.BaseField`)
- Uses real proof data from a valid Schnorr signature verification circuit
- Validates the critical `b` formula: `b = b_poly(zeta) + r * b_poly(zetaOmega)`

**Potential future enhancements** (not required for completion):
- Add Pallas field test (would require a circuit over `Pallas.ScalarField = Vesta.BaseField`)
- Run multiple proof instances via QuickCheck (currently uses single random signature per test run)

### TODO 2: Validate bulletproof challenge extraction against Rust FFI

**Completed**: 2026-02-03

**PR**: https://github.com/l-adic/snarky/pull/90

**Findings**: The implementation correctly exposes sponge checkpoint state from vendored `proof-systems` (following the architecture constraint) rather than re-implementing in the FFI layer.

**Key changes**:

1. **Vendored proof-systems modification** (`vendor/proof-systems/poseidon/src/sponge.rs`):
   - Added `checkpoint()` method to `FqSponge` trait
   - Exposed `SpongeCheckpoint<F>` struct with `state`, `sponge_state`, `last_squeezed`

2. **Rust FFI** (`packages/crypto-provider/src/kimchi/circuit.rs`):
   - `bulletproof_challenge_data`: Core helper that captures sponge state before L/R processing
   - `pallas_sponge_checkpoint` / `vesta_sponge_checkpoint`: Returns checkpoint with accessors
   - `pallas_proof_opening_lr` / `vesta_proof_opening_lr`: Returns L/R pairs from opening proof

3. **New PureScript module** (`packages/pickles/src/Pickles/IPA.purs`):
   - `LrPair`, `BPolyInput`, `ComputeBInput`, `BCorrectInput` types
   - `bPoly` / `bPolyCircuit`: Challenge polynomial evaluation
   - `computeB` / `computeBCircuit`: Combined b evaluation at zeta and zeta*omega
   - `extractScalarChallenges`: In-circuit challenge extraction from L/R pairs
   - `bCorrect` / `bCorrectCircuit`: Verification that b matches expected value

4. **PureScript FFI** (`packages/pickles/test/Test/Pickles/ProofFFI.purs`):
   - `SpongeCheckpoint` type with `state`, `spongeMode`, `modeCount`
   - `pallasSpongeCheckpointBeforeChallenges` / `vestaSpongeCheckpointBeforeChallenges`
   - `pallasProofOpeningLr` / `vestaProofOpeningLr`

5. **Tests** (`packages/pickles/test/Test/Pickles/E2E.purs`):
   - `bCorrectCircuitTest`: Validates `bCorrectCircuit` with Rust-provided values
   - `extractChallengesCircuitTest`: Validates challenge extraction circuit matches pure sponge and Rust FFI

**Test execution**:
```
$ npx spago test -p pickles -- --example "extractScalarChallenges"
E2E Schnorr Circuit
  ✓ extractScalarChallenges circuit matches pure and Rust
```

**Architecture compliance**:
- ✓ Modified vendored proof-systems to expose `SpongeCheckpoint` (correct approach)
- ✓ FFI accesses existing fields (`proof.lr`, `sponge.checkpoint()`) - no re-implementation
- ✓ Tests validate: pure sponge matches circuit, endo-mapped challenges match Rust

**Code organization**:
- IPA-related code consolidated from `Commitments.purs` into new `IPA.purs` module
- Clean separation: `IPA.purs` handles challenge polynomial and verification, `Commitments.purs` handles polynomial commitment batching
