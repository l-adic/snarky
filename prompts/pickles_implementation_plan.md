# Revised Plan: Incremental and Test-Driven Pickles Implementation

The new approach is to identify the smallest, most atomic components of the system, implement them, and test them thoroughly before composing them into larger pieces. We will build the individual "Lego bricks" before we try to build the castle.

**Phase 1: Foundational Tools & Primitives**

These are the smallest, most self-contained building blocks. Each is a perfect candidate for a small PR.

1.  **Unit: Poseidon Sponge.**
    *   **Goal:** Implement the Poseidon sponge function for both the `Tick` and `Tock` fields. This is a pure computational unit.
    *   **Implementation:** `src/lib/pickles/Sponge.purs`
    *   **Test:** `test/lib/pickles/Sponge.purs`. The test will be to assert that for a given sequence of field element inputs, the sponge produces a known, pre-computed output. We can get these "test vectors" from the OCaml source or other Mina repositories.

2.  **Unit: Scalar Challenge Generation.**
    *   **Goal:** Create the `ScalarChallenge` module that uses the sponge to derive the various challenges (`alpha`, `beta`, `gamma`, etc.) from a transcript.
    *   **Implementation:** `src/lib/pickles/ScalarChallenge.purs`
    *   **Test:** `test/lib/pickles/ScalarChallenge.purs`. This test will feed a dummy transcript to the functions and assert that the correct, structured challenges are squeezed out. Depends only on the Sponge unit.

3.  **Unit: Foreign Field Arithmetic Gadgets.**
    *   **Goal:** Implement the basic in-circuit gadgets for emulated "foreign field" addition and multiplication. These are essential for the "Wrap" circuit to reason about the "Step" proof's native field.
    *   **Implementation:** `src/lib/pickles/ForeignField.purs`
    *   **Test:** `test/lib/pickles/ForeignField.purs`. Use `circuitSpec` to create two circuits: one for `add` and one for `mul`. The tests will prove that for public inputs `a` and `b`, the circuit correctly computes `c = a + b` (or `c = a * b`) in the foreign field.

**Phase 2: The Kimchi Verifier In-Circuit**

The core of Pickles is a PLONK verifier implemented as a circuit. We will break down the verifier's checks into individual, testable circuits.

1.  **Unit: Gate Constraint Evaluation Circuit.**
    *   **Goal:** A circuit that takes wire polynomial evaluations (`w`) and gate selectors (`s`) as public input and checks that they satisfy the Kimchi gate equations (e.g., `s.add * (w[0] + w[1] - w[2]) = 0`).
    *   **Implementation:** `src/lib/pickles/plonk_checks/GateConstraints.purs`
    *   **Test:** `test/lib/pickles/plonk_checks/GateConstraints.purs`. The `circuitSpec` will prove that the circuit passes for inputs that satisfy the equations and fails for those that don't.

2.  **Unit: Permutation Argument Verification Circuit.**
    *   **Goal:** A circuit that verifies the copy constraints (permutation argument) of the PLONK proof.
    *   **Implementation:** `src/lib/pickles/plonk_checks/Permutation.purs`
    *   **Test:** `test/lib/pickles/plonk_checks/Permutation.purs`. `circuitSpec` will test this with a set of evaluations that correctly respect the permutation.

3.  **Unit: Polynomial Commitment Verification Circuit.**
    *   **Goal:** A circuit that verifies the batch-opening proof for the polynomial commitments. This is the `e(P, Q) = ...` check and is the most complex part of the verifier.
    *   **Implementation:** `src/lib/pickles/plonk_checks/Commitments.purs`
    *   **Test:** `test/lib/pickles/plonk_checks/Commitments.purs`. This will be a complex test, but the goal is to use `circuitSpec` to prove the circuit passes for a known-valid opening.

4.  **Unit: Composed Kimchi Verifier Circuit.**
    *   **Goal:** Combine the above three circuits into a single, unified `verifyKimchi` circuit. This circuit's public input will be a full (if minimal) Kimchi proof and verification key.
    *   **Implementation:** `src/lib/pickles/plonk_checks/Verifier.purs`
    *   **Test:** `test/lib/pickles/plonk_checks/Verifier.purs`. Test that this composite circuit can successfully verify a known-valid Kimchi proof.

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
