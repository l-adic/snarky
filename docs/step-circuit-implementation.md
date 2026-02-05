# Step Circuit Implementation Guide

## Overview

The Step circuit is a combinator that takes an application circuit (e.g., Schnorr verification) and combines it with Wrap proof verification ("merge"). The result is a uniform circuit that handles both the base case (no previous proofs) and recursive cases (verifying previous Wrap proofs).

**Key insight**: The application circuit doesn't directly verify previous proofs. It returns *which* previous proofs should be verified via `must_verify` flags. The Pickles framework handles actual verification.

## Architecture

```
Step Circuit (on Vesta.ScalarField)
├── Application logic (Schnorr, state transition, etc.)
└── Merge: Verify/finalize N previous Wrap proofs

Wrap Circuit (on Pallas.ScalarField)
└── Verify Step proof (IPA check, challenge derivation)
```

The curve cycling enables native field arithmetic on commitment curve points:
- Step (Vesta scalar field) can do native arithmetic on Pallas points
- Wrap (Pallas scalar field) can do native arithmetic on Vesta points

## Core Types

### Inductive Rule (Application Circuit Interface)

**OCaml**: `mina/src/lib/pickles/pickles_intf.mli:168-246`

```ocaml
(* What the application circuit receives *)
type 'public_input main_input =
  { public_input : 'public_input }

(* What the application circuit returns *)
type ('prev_vars, 'widths, 'public_output, 'auxiliary_output) main_return =
  { previous_proof_statements : ('prev_vars, 'widths) H2.T(Previous_proof_statement).t
  ; public_output : 'public_output
  ; auxiliary_output : 'auxiliary_output  (* private data for prover *)
  }

(* A previous proof statement *)
type ('prev_var, 'width) Previous_proof_statement.t =
  { public_input : 'prev_var
  ; proof : 'width Proof.t
  ; proof_must_verify : B.t  (* KEY: controls whether to actually verify *)
  }
```

**PureScript equivalent**:
```purescript
type StepReturn prevInputs output aux =
  { previousProofStatements :: prevInputs  -- with mustVerify flags
  , publicOutput :: output
  , auxiliaryOutput :: aux
  }

type AppCircuit input prevInputs output aux f c t m =
  input -> Snarky c t m (StepReturn prevInputs output aux)
```

### Step Statement (Output)

**OCaml**: `mina/src/lib/pickles/step_main.ml:587-594`

```ocaml
{ Types.Step.Statement.proof_state =
    { unfinalized_proofs       (* Vector of deferred values *)
    ; messages_for_next_step_proof  (* hash digest *)
    }
; messages_for_next_wrap_proof     (* Vector of hash digests *)
}
```

**PureScript equivalent**:
```purescript
type StepStatement n f =
  { proofState ::
      { unfinalizedProofs :: Vector n (UnfinalizedProof f)
      , messagesForNextStepProof :: f
      }
  , messagesForNextWrapProof :: Vector n f
  }
```

### Unfinalized Proof (Deferred Values)

**OCaml**: `mina/src/lib/pickles/unfinalized.ml:95-104`

```ocaml
{ deferred_values =
    { plonk = { alpha; beta; gamma; zeta; ... }
    ; combined_inner_product = Shifted_value (...)
    ; xi = Scalar_challenge.create one_chal
    ; bulletproof_challenges = ...
    ; b = Shifted_value (...)
    }
; should_finalize = false  (* KEY: false for dummy/base case *)
; sponge_digest_before_evaluations = ...
}
```

**PureScript equivalent**:
```purescript
type UnfinalizedProof f sf =
  { deferredValues ::
      { plonk :: PlonkValues f
      , combinedInnerProduct :: sf
      , xi :: SizedF 128 f
      , bulletproofChallenges :: Vector 16 (SizedF 128 f)
      , b :: sf
      }
  , shouldFinalize :: Boolean
  , spongeDigestBeforeEvaluations :: f
  }
```

## Bootstrapping (Base Case)

**Key mechanism**: `should_finalize` flag + dummy proofs

**OCaml**: `mina/src/lib/pickles/unfinalized.ml:25-104` (dummy creation)
**OCaml**: `mina/src/lib/pickles/wrap_main.ml:431` (conditional assertion)

```ocaml
(* The critical assertion - allows dummies to "pass" *)
Boolean.(Assert.any [ finalized; not should_finalize ])
```

**How it works**:
1. Circuit is parameterized for `max_proofs_verified` slots
2. Dummy proofs have `should_finalize = false`
3. Real proofs have `should_finalize = true`
4. Assertion: `finalized || not should_finalize`
   - Dummies: `not should_finalize = true`, passes regardless of `finalized`
   - Real proofs: must have `finalized = true`

**For base case (Step0)**:
- All slots filled with dummies
- Same circuit structure as recursive case
- Verification runs but results ignored due to `should_finalize = false`

## Key OCaml Modules

### step_main.ml
- `verify_one` (lines 23-112): Verifies a single previous Wrap proof
- `main` (lines 274-594): The main Step circuit logic
- Line 34: `Boolean.Assert.( = ) unfinalized.should_finalize must_verify`
- Line 109: `~is_base_case:(Boolean.not must_verify)`
- Line 585: Padding with `Unfinalized.dummy ()`

### step_verifier.ml
- `finalize_other_proof` (lines ~823-1086): Finalizes deferred values from a Wrap proof
- Checks: `xi_correct`, `b_correct`, `combined_inner_product_correct`, `plonk_checks_passed`
- Line 1056-1082: The `b_correct` check using challenge polynomial

### wrap_main.ml
- Line 424-429: Calls `Wrap_verifier.finalize_other_proof` on previous proofs
- Line 431: `Boolean.(Assert.any [ finalized; not should_finalize ])`
- Line 496-509: Calls `incrementally_verify_proof` with `advice:{ b; combined_inner_product }`

### wrap_verifier.ml
- `check_bulletproof` (lines 564-616): IPA equation check, takes `b` as input
- `finalize_other_proof` (lines 1450-1683): Verifies deferred values
- `bullet_reduce` (line 174): Computes lr_prod from L/R pairs
- `compute_challenges` (line 1381): Converts 128-bit challenges to full field

### unfinalized.ml
- `Constant.dummy` (lines 25-104): Creates dummy unfinalized proof
- Key: `should_finalize = false` (line 102)

### dummy.ml
- Random dummy values for bootstrapping
- `Ipa.Wrap.challenges`, `Ipa.Step.challenges` (lines 29-58)

## Verification Flow

### In Wrap (verifying a Step proof):

1. **`check_bulletproof`** - IPA equation: `c*Q + delta = z1*(sg + b*u) + z2*H`
   - Takes `b` as input (implicitly verified by equation)
   - Derives challenges from L/R pairs
   - Returns challenges for deferred values

2. **`finalize_other_proof`** - For PREVIOUS Wrap proofs' deferred values
   - Verifies `b_correct`, `xi_correct`, `combined_inner_product_correct`
   - Uses `should_finalize` flag to skip dummies

### In Step (verifying previous Wrap proofs):

1. Run application circuit, get `previous_proof_statements`
2. For each previous proof with `must_verify = true`:
   - Call `finalize_other_proof` (step_verifier.ml)
   - Collect resulting challenges
3. Hash everything into `messages_for_next_step_proof`
4. Produce `StepStatement` for Wrap to verify

## PureScript Implementation Sketch

```purescript
-- | The Step combinator
stepCircuit
  :: forall n input output f c t m
   . CircuitM f c t m
  => AppCircuit input (Vector n PrevProofStatement) output Unit f c t m
  -> { appInput :: input
     , prevWrapProofs :: Vector n (WrapProof f)
     }
  -> Snarky c t m (StepStatement n f)
stepCircuit appCircuit input = do
  -- 1. Run application circuit
  { previousProofStatements, publicOutput } <- appCircuit input.appInput

  -- 2. Verify/finalize each previous Wrap proof
  results <- forWithIndex (Vector.zip previousProofStatements input.prevWrapProofs)
    \i (stmt, proof) -> do
      { finalized, challenges } <- finalizeOtherProof proof
      -- Key assertion: finalized || not mustVerify
      assert_ =<< or_ finalized (not_ stmt.mustVerify)
      pure challenges

  -- 3. Pad with dummy unfinalized proofs
  let unfinalizedProofs = map toUnfinalizedProof results

  -- 4. Hash for next step
  messagesForNextStep <- hashMessages { publicOutput, challenges: results }

  pure
    { proofState: { unfinalizedProofs, messagesForNextStepProof: messagesForNextStep }
    , messagesForNextWrapProof: map computeDigest results
    }

-- | Dummy for base case
dummyUnfinalizedProof :: forall f sf. Ring f => Ring sf => UnfinalizedProof f sf
dummyUnfinalizedProof =
  { deferredValues: { ... zero values ... }
  , shouldFinalize: false  -- Key: dummies don't need to finalize
  , spongeDigestBeforeEvaluations: zero
  }
```

## Open Questions

1. **Exact hashing scheme** for `messages_for_next_step_proof` and `messages_for_next_wrap_proof`
2. **Domain handling** for different proof sizes
3. **Feature flags** for optional circuit features (lookups, etc.)
4. **Public input packing** into field elements

## TODOs

- [x] **Step types and dummy proof generation**: Created `Pickles.Step.Types` with newtypes (`BulletproofChallenges`, `PlonkMinimal`, `DeferredValues`, `UnfinalizedProof`) using proper size encoding (Vector 16, SizedF 128). Created `Pickles.Step.Dummy` with dummy value generators. Tests verify dummy values are zero and `shouldFinalize = false`. Reference: unfinalized.ml:95-104, dummy.ml.

- [x] **Step circuit combinator skeleton**: Created `Pickles.Step.Circuit` with:
  - `PreviousProofStatement`, `StepReturn`, `StepStatement` types
  - `stepCircuit` combinator that:
    1. Runs application circuit to get `previousProofStatements` with `mustVerify` flags
    2. For each previous proof: asserts `shouldFinalize == mustVerify`, calls `finalizeOtherProofStub`, asserts `finalized || not shouldFinalize`
    3. Collects challenges and computes message digests (stubbed)
    4. Returns `StepStatement`
  - Stubs: `finalizeOtherProofStub`, `hashMessagesForNextStepProofStub`, `computeMessageForNextWrapProofStub`
  - Tests verify the bootstrapping assertion `finalized || not shouldFinalize` with all 4 boolean combinations

- [ ] **`finalizeOtherProof` for Step**: Implement the actual finalization logic (step_verifier.ml:823-1086). Takes deferred values + evaluations, returns `(finalized :: BoolVar, challenges :: Vector 16 f)`. Checks: xi_correct, b_correct, combined_inner_product_correct, plonk_checks_passed. Much of this is already implemented in `Pickles.PlonkChecks` - integrate with Step circuit.

- [ ] **`hashMessagesForNextStepProof`**: Hash app state + challenges into digest (step_verifier.ml:1099+). Uses Poseidon sponge.

- [ ] **`WrapProofWitness` type**: Define the witness data needed from a Wrap proof for Step to verify it. Includes evaluations, commitments, and sponge state.

- [ ] **Integration test**: Run Step combinator with Schnorr circuit + real (non-stubbed) verification, verify circuit is satisfiable.
