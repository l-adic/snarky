# Revised Plan: Incremental and Test-Driven Pickles Implementation

The new approach is to identify the smallest, most atomic components of the system, implement them, and test them thoroughly before composing them into larger pieces. We will build the individual "Lego bricks" before we try to build the castle.

**Phase 1: Foundational Tools & Primitives**

**Status: Completed**

These are the smallest, most self-contained building blocks. Each is a perfect candidate for a small PR.

1.  **Unit: Poseidon Sponge.**
    *   **Status: Completed**
    *   **Goal:** Implement the Poseidon sponge function for both the `Tick` and `Tock` fields. This is a pure computational unit.
    *   **Implementation:** `src/lib/pickles/Sponge.purs`
    *   **Test:** `test/lib/pickles/Sponge.purs`. The test will be to assert that for a given sequence of field element inputs, the sponge produces a known, pre-computed output. We can get these "test vectors" from the OCaml source or other Mina repositories.

2.  **Unit: Scalar Challenge Generation.**
    *   **Status: Completed**
    *   **Goal:** Create the `ScalarChallenge` module that uses the sponge to derive the various challenges (`alpha`, `beta`, `gamma`, etc.) from a transcript.
    *   **Implementation:** `src/lib/pickles/ScalarChallenge.purs`
    *   **Test:** `test/lib/pickles/ScalarChallenge.purs`. This test will feed a dummy transcript to the functions and assert that the correct, structured challenges are squeezed out. Depends only on the Sponge unit.

3.  **Unit: Foreign Field Arithmetic Gadgets.**
    *   **Status: Postponed** (Current belief is that this is not needed for the initial implementation).
    *   **Goal:** Implement the basic in-circuit gadgets for emulated "foreign field" addition and multiplication. These are essential for the "Wrap" circuit to reason about the "Step" proof's native field.
    *   **Implementation:** `src/lib/pickles/ForeignField.purs`
    *   **Test:** `test/lib/pickles/ForeignField.purs`. Use `circuitSpec` to create two circuits: one for `add` and one for `mul`. The tests will prove that for public inputs `a` and `b`, the circuit correctly computes `c = a + b` (or `c = a * b`) in the foreign field.

**Phase 2: The Kimchi Verifier In-Circuit**

The core of Pickles is a PLONK verifier implemented as a circuit. We will break down the verifier's checks into individual, testable circuits.

1.  **Unit: Gate Constraint Evaluation Circuit.**
    *   **Status: Completed**
    *   **Goal:** A circuit that takes wire polynomial evaluations (`w`) and gate selectors (`s`) as public input and checks that they satisfy the Kimchi gate equations.
    *   **Strategy:** We leveraged the existing PureScript "linearization" modules (`packages/pickles/src/Pickles/Linearization/`). These modules contain an AST representing the full Kimchi constraint polynomial, translated from the official OCaml implementation. The AST is evaluated within a circuit using a generic interpreter.
    *   **Implementation:** `packages/pickles/src/Pickles/PlonkChecks/GateConstraints.purs`
        *   `checkGateConstraints`: a `Snarky` circuit that evaluates the linearization polynomial AST using in-circuit `FVar` values and asserts the result equals zero.
        *   `evaluateGateConstraints`: evaluates and returns the result without asserting (for composability).
        *   `GateConstraintInput`: uses `PointEval f = { zeta, omegaTimesZeta }` for structured polynomial evaluations at two points, with `Vector 15 (PointEval f)` for witness evals and `Vector 6 (PointEval f)` for selector evals.
    *   **FFI Infrastructure:** `packages/pickles/src/Pickles/Linearization/FFI.purs`
        *   `LinearizationFFI` typeclass with instances for Pallas and Vesta, providing: `evaluateLinearization`, `unnormalizedLagrangeBasis`, `vanishesOnZkAndPreviousRows`, `proverIndexDomainLog2`, `proverIndexWitnessEvaluations`, `proverIndexCoefficientEvaluations`, `proverIndexSelectorEvaluations`.
        *   Rust implementations use generic `<F: PrimeField>` functions with thin `#[napi]` wrappers per curve, eliminating duplication.
    *   **Test:** `packages/pickles/test/Test/Pickles/Linearization.purs`
        *   QuickCheck: PureScript interpreter matches Rust evaluator on arbitrary inputs (100 samples per curve).
        *   Circuit: `circuitSpec` verifies the in-circuit evaluation matches field-level evaluation.
        *   Valid witness: PS matches Rust when given real polynomial evaluations from a Schnorr circuit prover index.

2.  **Unit: Permutation Argument Circuit.**
    *   **Goal:** A circuit that computes the permutation contribution to the full linearization check. This is separate from the gate constraint constant_term — the OCaml implementation (`plonk_checks.ml` lines 349-440) computes it independently.
    *   **Architecture:** The full verification equation is `ft_eval0 = perm_contribution - constant_term + boundary_quotient = 0`. Phase 2.1 handles `constant_term`. This unit handles the permutation terms.
    *   **What it computes:**
        *   The permutation contribution: `∏(beta*sigma_i + w_i + gamma) * z(zeta*omega) * alpha^21 * zkp - ∏(beta*zeta*shift_i + w_i + gamma) * z(zeta) * alpha^21 * zkp`
        *   The `perm` scalar (coefficient for z(x) in the full linearization): `-(z(zeta*omega) * beta * alpha^21 * zkp * ∏(gamma + beta*sigma_i + w_i))`
        *   The boundary quotient: `L_1(zeta) * (z(zeta) - 1)` contribution
    *   **New inputs needed (beyond GateConstraintInput):**
        *   `z(zeta)`, `z(zeta*omega)` — permutation polynomial evaluations (PointEval)
        *   `sigma_i(zeta)` for 7 permutation columns — permutation polynomial evaluations
        *   Column shift constants (derived from domain generator)
        *   `perm_alpha0 = 21` — the alpha power offset for permutation terms
    *   **OCaml reference:** `mina/src/lib/pickles/plonk_checks/plonk_checks.ml` (`ft_eval0` and `derive_plonk` functions)
    *   **Implementation:** `packages/pickles/src/Pickles/PlonkChecks/Permutation.purs`
    *   **Test:** `circuitSpec` with valid permutation polynomial evaluations from a prover index (same pattern as gate constraint tests).

3.  **Unit: Polynomial Commitment Verification Circuit.**
    *   **Goal:** A circuit that verifies the batch-opening proof for the polynomial commitments (IPA inner product argument). This checks that claimed polynomial evaluations are consistent with their commitments.
    *   **Implementation:** `packages/pickles/src/Pickles/PlonkChecks/Commitments.purs`
    *   **Test:** `circuitSpec` with a known-valid opening proof.

4.  **Unit: Composed `ft_eval0` Check (Full Linearization).**
    *   **Goal:** Combine gate constraints (constant_term), permutation contribution, and boundary quotient into the full `ft_eval0 = 0` check. This is the core PLONK verification equation.
    *   **Architecture:** `ft_eval0 = perm_contribution - constant_term + boundary_quotient`. Each piece is computed by its respective unit; this composes them and asserts the sum equals zero.
    *   **Implementation:** `packages/pickles/src/Pickles/PlonkChecks/FtEval.purs`
    *   **Test:** End-to-end test with a real proof's evaluations showing `ft_eval0 = 0`.

5.  **Unit: Composed Kimchi Verifier Circuit.**
    *   **Goal:** Combine the `ft_eval0` check with polynomial commitment verification into a unified `verifyKimchi` circuit.
    *   **Implementation:** `packages/pickles/src/Pickles/PlonkChecks/Verifier.purs`
    *   **Test:** Test that this composite circuit can verify a known-valid Kimchi proof.

**Phase 3: Assembling the Step & Wrap Circuits**

Now we compose our tested units into the main Pickles components.

1.  **Unit: The "Wrap" Circuit.**
    *   **Goal:** The Wrap circuit *is* the `verifyKimchi` circuit from Phase 2, but adapted to use the Foreign Field gadgets for its computations.
    *   **Implementation:** `src/lib/pickles/Wrap.purs`
    *   **Test:** `test/lib/pickles/Wrap.purs`. The test is to show that we can satisfy this circuit with a witness derived from a `Step` proof. This proves the composition of the verifier and the foreign field gadgets is correct.

2.  **Unit: The "Step" Circuit.**
    *   **Goal:** A circuit that composes the `verifyKimchi` circuit (this time *without* foreign field math) with the user's application logic.
    *   **Implementation:** `src/lib/pickles/Step.purs`
    *   **Test:** `test/lib/pickles/Step.purs`. The `circuitSpec` will define a simple app (e.g., a counter) and prove that the Step circuit is satisfied when a valid transition is made *and* a valid previous `Wrap` proof is provided.

**Phase 4: Top-Level API and End-to-End Tests**

With all the circuit logic in place and tested, we write the off-circuit code to drive them.

1.  **Unit: Prover Logic.**
    *   **Goal:** Write the off-circuit PureScript functions that take application data, prepare the witnesses for the `Step` and `Wrap` circuits, and call the underlying `snarky-ps` prover.
    *   **Implementation:** `src/lib/pickles/Prover.purs`
    *   **Test:** `test/lib/pickles/E2E.purs`. An end-to-end test that calls the prover functions to generate a sequence of two proofs (a base case and one recursive step) and asserts that the proofs are created successfully.

2.  **Unit: Verifier Logic.**
    *   **Goal:** Write the final off-circuit `verify` function.
    *   **Implementation:** `src/lib/pickles/Verifier.purs`
    *   **Test:** Extend `test/lib/pickles/E2E.purs` to take the proofs generated in the previous test and have the `verify` function approve them.
