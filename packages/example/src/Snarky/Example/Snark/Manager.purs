-- | The main node: it owns a per-block scan state (`Snark.ScanState`), drives a
-- | dumb worker over a pair of buffered channels, and turns completed work into
-- | newly-unlocked work until each block's tree fills.
-- |
-- | Control flow (push/pull): the node PUSHES ready work onto `workQ` (the only
-- | proactive push is a block's base leaves); the worker PULLS it, proves, and
-- | PUSHES the id-tagged result onto `resultQ`; the node's listener PULLS
-- | results and, per completion, records it and PUSHES whatever it unlocked.
-- | Everything after the initial leaves is reactive.
-- |
-- | Work is routed by an opaque `WorkId = { block, slot }`, so results from any
-- | block land in the right scan state — the worker stays oblivious.
module Snarky.Example.Snark.Manager
  ( Manager
  , BlockId
  , OnProgress
  , mkManager
  , submitBlock
  ) where

import Prelude

import Control.Monad.Rec.Class (forever)
import Data.Array as Array
import Data.Foldable (for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff, forkAff)
import Effect.Aff.AVar (AVar)
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Fmt (fmt)
import Pickles (Verifier, toVerifiable, verify)
import Snarky.Example.AsyncQueue (Queue, dequeue, enqueue, newQueue)
import Snarky.Example.Env (Env)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.Snark.Pool (runPool)
import Snarky.Example.Snark.ScanState (ScanState, SlotId)
import Snarky.Example.Snark.ScanState as ScanState
import Snarky.Example.Snark.Work (BaseJob, Proof, WorkItem)
import Snarky.Example.Snark.Worker (SnarkBackend)

type BlockId = Int

-- | The routing key the node hands the worker and gets back verbatim.
type WorkId = { block :: BlockId, slot :: SlotId }

-- | A live block: its scan state and the slot the caller is awaiting the root in.
type BlockEntry d = { scan :: ScanState d, done :: AVar Proof }

-- | An observation hook: called with a block's scan state after every change
-- | (registration and each recorded result). UI-agnostic — a terminal
-- | display plugs in here (see `Snarky.Example.Snark.Progress`).
type OnProgress d = BlockId -> ScanState d -> Effect Unit

newtype Manager d = Manager
  { workQ :: Queue (Tuple WorkId (WorkItem d))
  , blocks :: Ref (Map BlockId (BlockEntry d))
  , verifier :: Verifier
  , logger :: Logger
  , onProgress :: Maybe (OnProgress d)
  }

service :: String
service = "Snark Manager"

-- | Start a node from an already-built `Env` (SRS + compiled program, produced
-- | once via `Snarky.Example.Env.mkEnv`; the manager never compiles): fork the
-- | worker pool and the result listener over a fresh pair of channels.
-- |
-- | The work backend is injected (`Snarky.Example.Snark.Worker.SnarkBackend`),
-- | along with the worker count `poolSize`: `localSnarkBackend` runs the
-- | synchronous prover in-process (so `poolSize` is plumbing-only there), while
-- | a parallel backend (node thread / web worker) makes `poolSize` a real knob.
-- | `jobTimeout` bounds how long the pool waits for a worker before reassigning
-- | a job to another (see `Snarky.Example.Snark.Pool.runPool`).
mkManager
  :: forall d
   . { logger :: Logger
     , onProgress :: Maybe (OnProgress d)
     , poolSize :: Int
     , jobTimeout :: Milliseconds
     , backend :: SnarkBackend d
     }
  -> Env d
  -> Aff (Manager d)
mkManager { logger, onProgress, poolSize, jobTimeout, backend } env = do
  workQ <- newQueue
  resultQ <- newQueue
  blocks <- liftEffect $ Ref.new Map.empty
  let
    node = Manager { workQ, blocks, verifier: env.compiledTx.verifier, logger, onProgress }
  _ <- forkAff $ runPool logger jobTimeout poolSize (backend env)
    { next: dequeue workQ
    , post: enqueue resultQ
    , describe: \workId work -> ScanState.describe workId.slot work
    }
  _ <- forkAff $ listen node resultQ
  pure node

-- | Submit a block: register its scan state, push its base leaves, and block
-- | until the listener fills the root.
submitBlock :: forall d. Manager d -> BlockId -> Array (BaseJob d) -> Aff Proof
submitBlock (Manager n) blockId jobs = do
  let scan = ScanState.buildScanState jobs
  done <- AVar.empty
  liftEffect $ Ref.modify_ (Map.insert blockId { scan, done }) n.blocks
  liftEffect $ for_ n.onProgress \report -> report blockId scan
  for_ (ScanState.initialWork scan) \(Tuple slot work) -> do
    Log.logDebug n.logger $ fmt @"[{service}] block {blockId}: submitting {work}"
      { service, blockId, work: ScanState.describe slot work }
    enqueue n.workQ (Tuple { block: blockId, slot } work)
  AVar.take done

-- | The listener: each result records into its block's scan state, dispatches
-- | whatever that unlocked, and — when the root fills — resolves the waiter and
-- | drops the block.
listen :: forall d. Manager d -> Queue (Tuple WorkId Proof) -> Aff Unit
listen (Manager n) resultQ = forever do
  Tuple workId proof <- dequeue resultQ
  blocks <- liftEffect $ Ref.read n.blocks
  case Map.lookup workId.block blocks of
    Nothing ->
      Log.logWarning n.logger $ fmt @"[{service}] Received unrequested snark work for blockId:{block} slotId:{slot}"
        { block: workId.block, slot: workId.slot, service }
    Just entry ->
      if not (verify n.verifier (toVerifiable proof)) then do
        Log.logWarning n.logger $ fmt @"[{service}] block {block}: slot {slot} proof FAILED verification — resubmitting"
          { service, block: workId.block, slot: workId.slot }
        case ScanState.workFor workId.slot entry.scan of
          Just work -> enqueue n.workQ (Tuple workId work)
          Nothing ->
            Log.logError n.logger $ fmt @"[{service}] block {block}: slot {slot} failed verification but its work could not be rebuilt to resubmit"
              { service, block: workId.block, slot: workId.slot }
      else do
        let { state, unlocked, done } = ScanState.record workId.slot proof entry.scan
        liftEffect $ Ref.modify_ (Map.insert workId.block (entry { scan = state })) n.blocks
        liftEffect $ for_ n.onProgress \report -> report workId.block state
        -- One line per consequence of this result: each unlocked merge, the
        -- root completing, or (at Debug) nothing yet — the sibling is pending.
        for_ unlocked \(Tuple slot work) -> do
          Log.logInfo n.logger $ fmt @"[{service}] block {block}: recorded slot {slot} -> submitting {work}"
            { service, block: workId.block, slot: workId.slot, work: ScanState.describe slot work }
          enqueue n.workQ (Tuple { block: workId.block, slot } work)
        case done of
          Just rootProof -> do
            _ <- AVar.tryPut rootProof entry.done
            Log.logInfo n.logger $ fmt @"[{service}] block {block}: recorded slot {slot} -> block complete"
              { service, block: workId.block, slot: workId.slot }
            liftEffect $ Ref.modify_ (Map.delete workId.block) n.blocks
          Nothing ->
            when (Array.null unlocked)
              $ Log.logDebug n.logger
              $ fmt @"[{service}] block {block}: recorded slot {slot} (sibling pending)"
                  { service, block: workId.block, slot: workId.slot }
