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
  , mkManager
  , submitBlock
  , verifier
  ) where

import Prelude

import Control.Monad.Rec.Class (forever)
import Data.Foldable (for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff, forkAff)
import Effect.Aff.AVar (AVar)
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Mina.ChainId (ChainId)
import Pickles (Verifier)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Example.AsyncQueue (Queue, dequeue, enqueue, newQueue)
import Snarky.Example.Snark.ScanState (ScanState, SlotId)
import Snarky.Example.Snark.ScanState as ScanState
import Snarky.Example.Snark.Work (BaseJob, Proof, WorkItem)
import Snarky.Example.Snark.Worker (runWorker)
import Snarky.Example.Transaction (compileTxCircuit)

type BlockId = Int

-- | The routing key the node hands the worker and gets back verbatim.
type WorkId = { block :: BlockId, slot :: SlotId }

-- | A live block: its scan state and the slot the caller is awaiting the root in.
type BlockEntry d = { scan :: ScanState d, done :: AVar Proof }

newtype Manager d = Manager
  { workQ :: Queue (Tuple WorkId (WorkItem d))
  , blocks :: Ref (Map BlockId (BlockEntry d))
  , verifier :: Verifier
  }

-- | The batch verifier for proofs this node produces.
verifier :: forall d. Manager d -> Verifier
verifier (Manager n) = n.verifier

-- | Start a node: compile the program once (at the mask-backed monad — compile
-- | reads no advice, so an empty mask env suffices), then fork the worker and
-- | the result listener over a fresh pair of channels.
mkManager
  :: forall d
   . Reflectable d Int
  => ChainId
  -> { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }
  -> Aff (Manager d)
mkManager chainId srs = do
  compiled <- liftEffect $ compileTxCircuit chainId srs
  workQ <- newQueue
  resultQ <- newQueue
  blocks <- liftEffect $ Ref.new Map.empty
  let
    node = Manager { workQ, blocks, verifier: compiled.verifier }
  _ <- forkAff $ runWorker compiled { next: dequeue workQ, post: enqueue resultQ }
  _ <- forkAff $ listen node resultQ
  pure node

-- | Submit a block: register its scan state, push its base leaves, and block
-- | until the listener fills the root.
submitBlock :: forall d. Manager d -> BlockId -> Array (BaseJob d) -> Aff Proof
submitBlock (Manager n) blockId jobs = do
  let scan = ScanState.buildScanState jobs
  done <- AVar.empty
  liftEffect $ Ref.modify_ (Map.insert blockId { scan, done }) n.blocks
  for_ (ScanState.initialWork scan) \(Tuple slot work) ->
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
    Nothing -> pure unit
    Just entry -> do
      let { state, unlocked, done } = ScanState.record workId.slot proof entry.scan
      liftEffect $ Ref.modify_ (Map.insert workId.block (entry { scan = state })) n.blocks
      for_ unlocked \(Tuple slot work) ->
        enqueue n.workQ (Tuple { block: workId.block, slot } work)
      case done of
        Just rootProof -> do
          _ <- AVar.tryPut rootProof entry.done
          liftEffect $ Ref.modify_ (Map.delete workId.block) n.blocks
        Nothing -> pure unit
