-- | The snark worker's per-job step: prove one `WorkItem` against a compiled
-- | transaction-snark program. The transport and the worker loop live in
-- | `Snarky.Example.Snark.Pool` (which drives this as a worker's `run`); this
-- | module knows nothing of channels, queues, or the producer.
module Snarky.Example.Snark.Worker
  ( proveItem
  , SnarkBackend
  , localSnarkBackend
  ) where

import Effect (Effect)
import Snarky.Example.Env (Env)
import Snarky.Example.Snark.Pool (WorkerBackend, localBackend)
import Snarky.Example.Snark.Work (Proof, WorkItem(..))
import Snarky.Example.Transaction (CompiledTx)

-- | Prove one work item against the compiled program: a `Base` over its witness
-- | mask, a `Merge` over the two child proofs.
proveItem :: forall d. CompiledTx d -> WorkItem d -> Effect Proof
proveItem compiled = case _ of
  Base { tx, mask, statement } -> compiled.baseProver { env: { tx, mask }, statement }
  Merge { proof1, proof2, statement } -> compiled.mergeProver { proof1, proof2, statement }

-- | How the manager obtains a worker backend for snark work: given the host's
-- | `Env` (its compiled program plus the SRSes), produce a `WorkerBackend`. The
-- | in-process `localSnarkBackend` reuses the compiled program directly; a
-- | remote backend (node worker thread / web worker) ignores the compiled
-- | program — proving is just a function, so each worker compiles its own — but
-- | still needs the host's SRSes to decode the proofs workers send back.
type SnarkBackend d = Env d -> WorkerBackend (WorkItem d) Proof

-- | In-process backend: workers run the synchronous prover against the host's
-- | compiled program. No real parallelism, but it exercises the pool plumbing.
localSnarkBackend :: forall d. SnarkBackend d
localSnarkBackend env = localBackend (proveItem env.compiledTx)
