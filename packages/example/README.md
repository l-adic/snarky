# Example: a Merkle-ledger cryptocurrency node

A reference application for the DSL: a simple Merkle tree-based cryptocurrency
ledger with a recursive transaction snark (Pickles), a block pipeline, and a
parallel snark-work scheduler — a miniature, Mina-shaped node.

## Layout

- **`Types/`** — the domain types: `Account`, `PublicKey`, `TokenAmount`.
- **`Ledger.purs`** — the ledger: a sparse Merkle tree of accounts plus the
  public-key → address index a node keeps beside it.
- **`Transaction/`** — the transaction semantics:
  - `Checked.purs` — **the single implementation of the transfer logic**
    (`applyTxChecked`), written once as circuit code, plus the two Pickles
    rules (`base` proves one transfer, `merge` composes two proofs) and
    `compileTxCircuit`.
  - `Unchecked.purs` — `applyTx`, the off-circuit ledger arrow. There is no
    hand-written value-level twin: it *interprets* `applyTxChecked` on
    concrete values via `Snarky.Backend.Compile.runAndCheck`, which computes
    every witness and eagerly checks every assertion (signature, ownership,
    nonce, under/overflow). Whatever `applyTx` accepts is therefore provable
    by construction. Also `sign` (building a signed transfer).
  - `Monad.purs` / `MaskMonad.purs` — the advice monads serving the circuit's
    Merkle/account/transaction requests from a full ledger (node-side) or
    from a per-transaction witness mask (prover-side).
- **`Block.purs`** — blocks (a fixed-size vector of transfers) and
  `processBlock`, which applies them and extracts per-transaction snark work.
- **`Snark/`** — the snark-work pipeline: a pure per-block scan state (an
  implicit perfect merge tree), the manager that schedules work over async
  channels, and a dumb worker that proves base/merge items.
- **`Simulation/`** — synthetic traffic: genesis ledger + keystore generation
  and sequentially-valid random blocks.
- **`test/`** — quickcheck specs for the transfer circuit (valid, overdraft,
  wrong nonce, unknown receiver) against a test-local oracle, plus pickled
  end-to-end specs proving and verifying a block's full merge tree.

This is a foundational example: balances are simple 128-bit amounts, there is
no account creation (transfers require both accounts to exist), and a block
holds a handful of transactions. The aim is to demonstrate the core mechanics
of state transitions, data authentication, and recursive proof composition in
a ZK DSL.
