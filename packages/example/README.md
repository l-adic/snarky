# Example Circuits

This package provides a reference implementation for a simple, Merkle tree-based cryptocurrency ledger. It's intended as a clear, minimal example of how to structure a basic ZK application using this DSL.

## What's Inside

-   **`Types.purs`**: Defines the core data structures: `Account`, `PublicKey`, `TokenAmount`, and `Transaction`.
-   **`Circuits.purs`**: Defines the primary zk-SNARK circuits for the ledger:
    -   `createAccount`: Inserts a new, empty account into the tree.
    -   `getAccount`: Retrieves an account and proves its ownership against a given root.
    -   `transfer`: Executes a transaction by debiting a sender and crediting a receiver, producing a new ledger root.
-   **`test/`**: The test suite demonstrates how to test circuits. It includes property tests for both valid transfers and invalid transfers (i.e., insufficient balance), ensuring the circuit correctly accepts or rejects them.

This is a foundational example. It omits features like robust overflow/underflow checks on balances in favor of demonstrating the core mechanics of state transitions and data authentication in a ZK-DSL.