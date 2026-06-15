-- | The snark worker's per-job step: prove one `WorkItem` against a compiled
-- | transaction-snark program. The transport and the worker loop live in
-- | `Snarky.Example.Snark.Pool` (which drives this as a worker's `run`); this
-- | module knows nothing of channels, queues, or the producer.
module Snarky.Example.Snark.Worker
  ( proveItem
  ) where

import Effect (Effect)
import Snarky.Example.Snark.Work (Proof, WorkItem(..))
import Snarky.Example.Transaction (CompiledTx)

-- | Prove one work item against the compiled program: a `Base` over its witness
-- | mask, a `Merge` over the two child proofs.
proveItem :: forall d. CompiledTx d -> WorkItem d -> Effect Proof
proveItem compiled = case _ of
  Base { tx, mask, statement } -> compiled.baseProver { env: { tx, mask }, statement }
  Merge { proof1, proof2, statement } -> compiled.mergeProver { proof1, proof2, statement }
