-- | The snark worker: a consumer of `WorkItem`s that initializes itself from a
-- | compiled transaction-snark program (the output of `compileTxCircuit`,
-- | instantiated at the mask-backed `TransferMaskM`) and proves each item.
-- |
-- | It speaks only the `Snark.Work` protocol + `next`/`post` — it knows nothing of
-- | the producer or how work reaches it. `runWorker` is the loop a backend
-- | (local fiber, thread, remote process) drives.
module Snarky.Example.Snark.Worker
  ( proveItem
  , runWorker
  ) where

import Prelude

import Control.Monad.Rec.Class (forever)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Fmt (fmt)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.Snark.Work (Proof, WorkItem(..))
import Snarky.Example.Transaction (CompiledTx)

service :: String
service = "Snark Worker"

-- | Prove one work item against the compiled program. A `Base` runs over a fresh
-- | `Ref` of its witness mask; a `Merge` over an empty mask (it reads none).
proveItem :: forall d. CompiledTx d -> WorkItem d -> Effect Proof
proveItem compiled = case _ of
  Base { tx, mask, statement } -> do
    let env = { tx, mask }
    compiled.baseProver { env, statement }
  Merge { proof1, proof2, statement } -> do
    compiled.mergeProver { proof1, proof2, statement }

-- | The worker loop: pull the next `(id, work)`, prove it, post back `(id,
-- | proof)`. The id is opaque (the node uses it to route) and the transport is
-- | abstracted behind `next`/`post`, so the worker knows nothing of channels,
-- | queues, blocks, or the producer.
runWorker
  :: forall d id
   . Show id
  => Logger
  -> CompiledTx d
  -> { next :: Aff (Tuple id (WorkItem d))
     , post :: Tuple id Proof -> Aff Unit
     }
  -> Aff Unit
runWorker logger compiled io = forever do
  Tuple workId work <- io.next
  Log.logInfo logger $ fmt @"[{service}] Received snark work request with id:{workId}"
    { service, workId: show workId }
  proof <- liftEffect $ proveItem compiled work
  Log.logInfo logger $ fmt @"[{service}] Completed snark work request with id:{workId}"
    { service, workId: show workId }
  io.post (Tuple workId proof)