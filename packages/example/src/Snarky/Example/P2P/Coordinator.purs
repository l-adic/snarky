-- | The coordinator side of the P2P star, generic over the work/result payload.
-- | It builds a `WorkerBackend` (for `Snarky.Example.Snark.Pool.runPool`) whose
-- | workers all arrive through one join queue: each `spawn` `dequeue`s the next
-- | available worker. Two producers feed that queue —
-- |
-- |   * a fresh `Join` over the `Transport` → a remote peer (addressed by its id);
-- |   * the coordinator's OWN prover, supplied as `prepareLocal` and offered once
-- |     it has warmed up (deferred to the first `spawn`, so its compile doesn't
-- |     fight the engine's setup compile and its first job's timeout covers only
-- |     proving). A lone coordinator only ever offers `Self`, so it proves the
-- |     whole block itself.
-- |
-- | One `Transport.onMessage` router fans `Result`/`Reject` to the waiting `run`
-- | by `JobId`, enqueues each fresh `Join` (deduped), and handles `Leave` (rejects
-- | the peer's in-flight job so the pool reassigns it at once). Per-participant
-- | state (idle / proving / completed) is reported through `onPeers` for the UI.
-- |
-- | Results travel as an encoded `Payload`; `mkStarBackend` yields a
-- | `WorkerBackend job Payload`. Callers that want typed results decode with
-- | `mapResult` (e.g. the snark coordinator decodes a `CompiledProof`).
-- |
-- | This module is browser-free (no Web Worker, no DOM), so the whole coordination
-- | layer is testable in Node over an in-memory transport with stub provers.
module Snarky.Example.P2P.Coordinator
  ( PeerView
  , RawWorker
  , CoordinatorConfig
  , mkStarBackend
  , mapResult
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.AVar (AVar)
import Effect.AVar as EffectAVar
import Effect.Aff (Aff, launchAff_, try)
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Exception (message, throw)
import Effect.Ref as Ref
import Fmt (fmt)
import Snarky.Example.AsyncQueue (Queue, dequeue, enqueueEffect, newQueueEffect)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.P2P.Protocol (Msg(..), decodeMsg, encodeMsg)
import Snarky.Example.P2P.Transport (Transport, onMessage, onPeer, onPeerLeave, sendTo)
import Snarky.Example.P2P.Types (JobId(..), Payload, PeerId)
import Snarky.Example.Snark.Pool (Worker, WorkerBackend)

-- | A reply slot for one assigned job: filled by the router with the worker's
-- | encoded proof (`Right`) or a rejection reason (`Left`).
type Reply = AVar (Either String Payload)

-- | A pool participant: the coordinator's own prover, or a remote peer.
data Participant = Self | Remote PeerId

derive instance Eq Participant
derive instance Ord Participant

-- | Render a participant as the external id the pool / UI show.
participantId :: Participant -> String
participantId = case _ of
  Self -> "self"
  Remote p -> show p

-- | What a pooled worker is doing: idle, or proving a job (carrying its label).
data PeerStatus = Idle | Proving String

statusLabel :: PeerStatus -> String
statusLabel = case _ of
  Idle -> "idle"
  Proving label -> label

isBusy :: PeerStatus -> Boolean
isBusy = case _ of
  Idle -> false
  Proving _ -> true

-- | A row of the UI's peer table: a connected worker, what it is doing right now
-- | (`busy` + a label), and how many jobs it has completed. `status`/`busy` are
-- | the wire projection of `PeerStatus` (the UI shows the label, styles on busy).
type PeerView = { id :: String, status :: String, busy :: Boolean, completed :: Int }

type PeerState = { status :: PeerStatus, completed :: Int }

-- | The coordinator's own prover, once warmed up: it proves a job and returns the
-- | encoded result, or throws on failure. (Remote peers are built internally from
-- | the transport.)
type RawWorker job = { run :: job -> Aff Payload, terminate :: Effect Unit }

-- | A worker waiting for a pool slot: the coordinator's own prover, or a remote
-- | peer addressed by its transport id.
data WorkerSpec job = SelfW (RawWorker job) | PeerW PeerId

type CoordinatorConfig job =
  { logger :: Logger
  , transport :: Transport
  -- Serialize a job for an `Assign` to a remote peer.
  , encodeJob :: job -> Payload
  -- A short label for the peer table ("proving base" / "proving merge" / …).
  , jobLabel :: job -> String
  -- Warm up the coordinator's own prover; `Left` (logged) means it is never
  -- offered. Run in the background once the pool starts dispatching.
  , prepareLocal :: Aff (Either String (RawWorker job))
  , onPeers :: Array PeerView -> Effect Unit
  }

-- | Build the coordinator's `WorkerBackend` (results as encoded `Payload`):
-- | install the transport router + shared correlation state once, kick off the
-- | self-prover warm-up, and return the backend the pool drives.
mkStarBackend :: forall job. CoordinatorConfig job -> Effect (WorkerBackend job Payload)
mkStarBackend config = do
  let logger = config.logger
  pending <- Ref.new (Map.empty :: Map JobId Reply)
  counter <- Ref.new 0
  known <- Ref.new (Set.empty :: Set.Set PeerId)
  peers <- Ref.new (Map.empty :: Map Participant PeerState)
  -- A remote peer's in-flight reply slot, keyed by peer id, so a `Leave` can
  -- reject it immediately (the run then throws → the pool reassigns the job).
  peerSlot <- Ref.new (Map.empty :: Map PeerId Reply)
  -- Raised (once) by the first pool `spawn` — i.e. when the pool starts
  -- dispatching. The self-prover warm-up waits on this before it warms up.
  provingStarted <- EffectAVar.empty :: Effect (AVar Unit)
  -- Workers waiting for a pool slot (remote `Join`s + the warmed-up `Self`).
  joinQ <- newQueueEffect :: Effect (Queue (WorkerSpec job))
  let
    report = do
      m <- Ref.read peers
      config.onPeers (map view (Map.toUnfoldable m))
      where
      view (Tuple w s) =
        { id: participantId w, status: statusLabel s.status, busy: isBusy s.status, completed: s.completed }
    addPeer w = do
      Ref.modify_ (Map.insert w { status: Idle, completed: 0 }) peers
      report
    setStatus w status = do
      Ref.modify_ (Map.update (\s -> Just s { status = status }) w) peers
      report
    completed w = do
      Ref.modify_ (Map.update (\s -> Just (s { status = Idle, completed = s.completed + 1 })) w) peers
      report
    removePeer w = do
      Ref.modify_ (Map.delete w) peers
      report
    -- Fill a job's reply slot iff still pending (a late duplicate after the pool
    -- reassigned + delivered is dropped).
    deliver jobId value = do
      m <- Ref.read pending
      case Map.lookup jobId m of
        Just slot -> void $ EffectAVar.put value slot mempty
        Nothing -> pure unit
    -- A peer announced it is leaving. Forget it, and if it had a job in flight,
    -- reject that job's reply now so the pool reassigns it at once.
    peerGone id = do
      Ref.modify_ (Set.delete id) known
      m <- Ref.read peerSlot
      case Map.lookup id m of
        Just slot -> void $ EffectAVar.put (Left "peer left") slot mempty
        Nothing -> removePeer (Remote id)
  -- Warm up the self prover once dispatching starts, then offer it as `Self`.
  launchAff_ do
    _ <- AVar.read provingStarted
    res <- config.prepareLocal
    case res of
      Right rw -> liftEffect $ enqueueEffect joinQ (SelfW rw)
      Left reason -> liftEffect $ Log.logError logger (fmt @"[pool] self prover failed to warm up: {reason}" { reason })
  -- Log every discovered peer (before its Join): the key diagnostic for a worker
  -- that never gets recognized.
  onPeer config.transport \id ->
    Log.logInfo logger (fmt @"[pool] discovered peer {id} (awaiting its Join)" { id: show id })
  -- The transport detected a peer's connection drop (WebRTC). Treat it like a
  -- `Leave`: forget it and reassign its in-flight job at once — no wait for the
  -- cooperative Leave message or the job timeout.
  onPeerLeave config.transport \id -> do
    Log.logInfo logger (fmt @"[pool] peer {id} disconnected" { id: show id })
    peerGone id
  onMessage config.transport \from raw ->
    case decodeMsg raw of
      Right (Join _) -> do
        fresh <- Ref.modify' (\s -> { state: Set.insert from s, value: not (Set.member from s) }) known
        when fresh do
          Log.logInfo logger (fmt @"[pool] peer {peer} joined the pool" { peer: show from })
          addPeer (Remote from)
          enqueueEffect joinQ (PeerW from)
      Right (Result r) -> deliver r.jobId (Right r.proof)
      Right (Reject r) -> deliver r.jobId (Left r.reason)
      Right (Leave l) -> peerGone l.peerId
      Right (Assign _) -> pure unit -- the coordinator assigns; it never receives one
      Left _ -> Log.logDebug logger (fmt @"[pool] undecodable message from {peer}" { peer: show from })
  pure
    { name: "p2p pool"
    , spawn: do
        -- Tell the warm-up the pool is dispatching now (idempotent — only the
        -- first spawn's tryPut lands).
        liftEffect $ void $ EffectAVar.tryPut unit provingStarted
        spec <- dequeue joinQ
        case spec of
          SelfW rw -> do
            liftEffect $ addPeer Self
            pure
              { id: participantId Self
              , run: \job -> do
                  liftEffect $ setStatus Self (Proving (config.jobLabel job))
                  res <- try (rw.run job)
                  case res of
                    Left err -> do
                      liftEffect $ setStatus Self Idle
                      liftEffect $ throw (message err)
                    Right proof -> do
                      liftEffect $ completed Self
                      pure proof
              , terminate: removePeer Self *> rw.terminate
              }
          PeerW peerId ->
            pure
              { id: participantId (Remote peerId)
              , run: \job -> do
                  jobId <- liftEffect $ Ref.modify' (\n -> { state: n + 1, value: JobId ("job-" <> show (n + 1)) }) counter
                  liftEffect $ setStatus (Remote peerId) (Proving (config.jobLabel job))
                  slot <- liftEffect EffectAVar.empty
                  liftEffect $ Ref.modify_ (Map.insert jobId slot) pending
                  liftEffect $ Ref.modify_ (Map.insert peerId slot) peerSlot
                  liftEffect $ sendTo config.transport peerId (encodeMsg (Assign { jobId, work: config.encodeJob job }))
                  res <- AVar.take slot
                  liftEffect do
                    Ref.modify_ (Map.delete jobId) pending
                    Ref.modify_ (Map.delete peerId) peerSlot
                  case res of
                    Left reason -> do
                      liftEffect $ setStatus (Remote peerId) Idle
                      liftEffect $ throw (fmt @"p2p worker {peer} rejected job {job}: {reason}" { peer: show peerId, job: show jobId, reason })
                    Right proof -> do
                      liftEffect $ completed (Remote peerId)
                      pure proof
              , terminate: do
                  Ref.modify_ (Set.delete peerId) known
                  removePeer (Remote peerId)
              }
    }

-- | Adapt an encoded-`Payload` backend to typed results by decoding each result
-- | (the decode runs inside the worker's `run`, so a decode failure surfaces as a
-- | failed job). Used by a typed caller, e.g. to decode a `CompiledProof`.
mapResult
  :: forall job result
   . (Payload -> Either String result)
  -> WorkerBackend job Payload
  -> WorkerBackend job result
mapResult decode wb =
  { name: wb.name
  , spawn: wb.spawn <#> \w -> w { run = decoded w }
  }
  where
  decoded :: Worker job Payload -> job -> Aff result
  decoded w job = do
    s <- w.run job
    case decode s of
      Left e -> liftEffect $ throw ("decode failed: " <> e)
      Right r -> pure r
