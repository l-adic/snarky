# Transaction application fixtures

The `example-fixtures` executable compiles the example's existing `baseRule` and
`mergeRule`. It uses a depth-four ledger, the Testnet chain ID and fixed generator
seeds to prove four signed transfers, then `merge(base0, base1)`,
`merge(base2, base3)` and the root merge. Two WorkerBees threads prove each
level in parallel. All seven proofs must pass batch verification.

Run from the repository root after building the backend and generating linearization code:

```sh
PICKLES_DUMP_DIR=/tmp/example-fixtures/dumps \
PICKLES_PROOF_CACHE_DIR=packages/example/bin/fixtures/proof-cache \
  npm exec -- spago run -p example-fixtures
```

Both output-directory variables are required. The executable uses the shared
SRS sizes and the filesystem Lagrange cache (`SNARK_LAGRANGE_CACHE_DIR` when set).
It writes:

- `dumps/ExampleTransaction/shapes/transaction.json`: the application structure,
  checked rule replay, backend keys and protocol environment.
- `dumps/ExampleTransaction/transaction.json`: the independent constraint systems
  for the base step, merge step and shared wrap circuit, together in one file.
- `proof-cache/ExampleTransaction.json`: seven step and seven wrap proofs, their
  predecessor references and the rule witness advice for replay.

Lean uses the explicit `ExampleTransaction` manifest entry. From `formal/`:

```sh
PICKLES_DUMP_DIR=/tmp/example-fixtures/dumps APPLICATION_SHAPES=ExampleTransaction \
  lake exe check-application-shapes
PICKLES_DUMP_DIR=/tmp/example-fixtures/dumps \
PICKLES_PROOF_CACHE_DIR=../packages/example/bin/fixtures/proof-cache \
LINKS=ExampleTransaction lake exe check-tags
```

Each worker writes its own temporary proof cache, seeded from the saved cache.
The host collects each job's step and wrap entries and publishes the combined
cache after verification. Witness advice comes from the original solve.

The first command compares all three constraint systems. The second also checks
fourteen circuit executions and applies twelve verification links and four
handovers in each direction. Reconstruction replays the exported rules; there is no handwritten
transaction rule in Lean.
