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

## Snark Worker Pool

The simulation proves a block of transactions (8 base proofs + 7 merges) by farming the snark work to a pool of workers behind a swappable **backend**. The pool (`Snarky.Example.Snark.Pool`) provides reliability for any backend: if a worker doesn't return a result within a timeout it reassigns the job to another worker (first result wins, duplicates dropped); if a worker's thread dies it is terminated, replaced, and the job reassigned.

### Backends

- **`localSnarkBackend`** (in-process) — runs the synchronous prover on the main thread. No real parallelism, but zero infrastructure; used by the test suite and the web app.
- **`nodeSnarkBackend`** (node `worker_threads`) — each worker is an OS thread that builds its own SRS and compiles its own circuit, then proves jobs in parallel. Used by the terminal simulation.

### Running the node simulation

From the repo root:

```bash
make fetch-srs              # once: download the SRS files
tools/run_simulation.sh     # build + run one block to a verified root proof
```

`--split` opens a throwaway tmux view with the sim on top and a live tail of the per-worker log (`snark-worker.log`) below. Each flag sets the matching `SNARK_*` env var:

| Flag | Env var | Meaning |
|------|---------|---------|
| `--pool-size N` | `SNARK_POOL_SIZE` | worker threads (default 4) |
| `--job-timeout S` | `SNARK_JOB_TIMEOUT_S` | per-job timeout before reassigning, seconds (default 120) |
| `--delay-ms MS` | `SNARK_WORKER_DELAY_MS` | fault injection: stall a job this long before proving (default 0 = off) |
| `--delay-pct PCT` | `SNARK_WORKER_DELAY_PCT` | % of jobs to stall (default 50) |
| `--crash-pct PCT` | `SNARK_WORKER_CRASH_PCT` | fault injection: % of jobs that crash the worker (default 0 = off) |

Failure modes (the block still proves to a verified root):

```bash
# timeout + reassignment: stall ~40% of jobs past a 35s timeout
tools/run_simulation.sh --split --job-timeout 35 --delay-ms 45000 --delay-pct 40

# worker death + replacement: crash ~15% of jobs
tools/run_simulation.sh --split --crash-pct 15
```