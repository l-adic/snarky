# Why does this repository exist?

## Background

### The Journey to o1labs
- My prior work involved an Ethereum Foundation grant exploring:
    - zk-DSLs (Domain Specific Languages)
    - Compiling Haskell's GHC-Core to a zk-DSL
    - Integrating with Circom via FFI

### The Catalyst at o1labs
- **The Challenge:** Assigned to "generalize Pickles," I found the existing codebase impossibly complex.
- **The Dead End:** This initial project was eventually moved on from without a successful conclusion.
- **The Mystery:** The emergence of the "Rust node" presented a puzzle: How could it produce blocks? From my OCaml Snarky experience, compiling circuits for Rust seemed infeasible.

## Current State

-   **Core Architecture:** Re-implementation of `snarky` in PureScript (a language similar to Haskell).
-   **Key Advantages:**
    *   **Developer Efficiency:** Leveraged personal expertise in Haskell/PureScript to minimize implementation overhead.
    *   **Architectural Clarity:** Native support for type-level programming simplifies complexities found in the OCaml version of Pickles (Mina's recursive proving).
    *   **Native Integration:** Easy FFI generation for native provers (via `napi-rs`), avoiding past issues with Plonk WASM.
-   **Key Features:**
    *   **Custom Gate Support:** Full support for custom Plonk gates required for Pickles.
    *   **Proof System Flexibility:** Concrete support for multiple proof systems, including Bulletproofs and Groth16.
    *   **Mina-Specific Utilities:** Includes essential tools like Merkle trees and Schnorr signatures.

## Future Work

- **Primary Goal: Deep Understanding**
  - The main objective is to thoroughly understand and document the `snarky`/`pickles` logic, which is one of the most complex and difficult-to-maintain parts of the OCaml codebase.
  - This is critical because modifying the production OCaml circuits is risky and can break the Mina application.

- **Strategic Goal: Enable a Rust Implementation**
  - This clean, isolated PureScript implementation can serve as a clear specification or reference.
  - The ultimate aim is to make it feasible to use an LLM to assist in developing a robust **Rust** version.
  - This approach is based on the experience that LLMs were not effective when applied directly to the original, complex OCaml codebase.
