-- | The coordinator side of the star: a `SnarkBackend` whose workers are remote
-- | peers reached over a `Transport`. It is the twin of the wasm-pool's
-- | `webWorkerSnarkBackend`, but the channel is `Transport.sendTo` (a network
-- | peer) instead of `postMessage` (a local Web Worker), and workers are
-- | discovered dynamically via the `Join` handshake rather than spawned.
-- |
-- | The pool (`Snarky.Example.Snark.Pool.runPool`) drives this over a `Dynamic`
-- | pool: the first worker is the coordinator's OWN in-process prover (so a lone
-- | coordinator proves the whole block itself — the single-machine path), and
-- | every subsequent `spawn` blocks until a peer `Join`s, so the pool grows as
-- | peers arrive. Reliability (timeout → reassign, at-most-once) is the pool's,
-- | so a peer that vanishes mid-job is handled by the job timeout (its `Result`
-- | never arrives → reassign).
-- |
-- | One `Transport.onMessage` router (installed once when the backend is built)
-- | fans `Result`/`Reject` to the waiting `run` by `jobId`, and turns each fresh
-- | `Join` into a queued peer that the next `spawn` claims. The backend also
-- | tracks per-peer state (idle / proving / completed count) and reports a
-- | snapshot through `onPeers` for the UI's peer table.
module Snarky.Example.P2P.Backend
  ( PeerView
  , p2pSnarkBackend
  , runCoordinator
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Time.Duration (Milliseconds(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.AVar (AVar)
import Effect.AVar as EffectAVar
import Effect.Aff (Aff, delay)
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Pickles.Prove.SerializeProof (decodeCompiledProof)
import Snarky.Example.P2P.Protocol (Msg(..), decodeMsg, encodeMsg, fingerprint)
import Snarky.Example.P2P.Transport (Transport, onMessage, sendTo)
import Snarky.Example.Snark.Pool (PoolSize(Dynamic))
import Snarky.Example.Snark.Work (WorkItem(..), encodeWorkItem)
import Snarky.Example.Snark.Worker (SnarkBackend, proveItem)
import Snarky.Example.Web.Engine (Depth, EngineCallbacks, runWith)

-- | A reply slot for one assigned job: filled by the router with the worker's
-- | encoded proof (`Right`) or a rejection reason (`Left`).
type Reply = AVar (Either String String)

-- | A row of the UI's peer table: a connected worker peer, what it is doing
-- | right now, and how many jobs it has completed.
type PeerView = { id :: String, status :: String, completed :: Int }

type PeerState = { status :: String, completed :: Int }

-- | An Effect-pushable, Aff-pullable queue of joined peer ids — the same
-- | single-consumer discipline as `Snarky.Example.AsyncQueue`, but `push` is in
-- | `Effect` so the transport's (Effect) message handler can feed it while a
-- | pool `spawn` (Aff) blocks on `pull`.
type JoinQueue = { push :: String -> Effect Unit, pull :: Aff String }

newJoinQueue :: Effect JoinQueue
newJoinQueue = do
  buf <- Ref.new []
  signal <- EffectAVar.empty
  let
    push x = do
      Ref.modify_ (\xs -> Array.snoc xs x) buf
      void $ EffectAVar.tryPut unit signal
    pull = do
      _ <- AVar.take signal
      xs <- liftEffect $ Ref.read buf
      case Array.uncons xs of
        Nothing -> pull -- spurious wake; retry
        Just { head, tail } -> do
          liftEffect $ Ref.write tail buf
          when (not (Array.null tail)) $ void $ liftEffect $ EffectAVar.tryPut unit signal
          pure head
  pure { push, pull }

-- | Fill a job's reply slot iff it is still pending (a late duplicate after the
-- | pool already reassigned + delivered is dropped).
deliver :: Ref (Map String Reply) -> String -> Either String String -> Effect Unit
deliver pending jobId value = do
  m <- Ref.read pending
  case Map.lookup jobId m of
    Just slot -> void $ EffectAVar.put value slot mempty
    Nothing -> pure unit

-- | Build the coordinator's `SnarkBackend`: install the transport router and the
-- | shared correlation state once, returning the per-`Env` backend the pool
-- | applies. Each remote worker is a peer addressed by its `Join`'s `from` id.
p2pSnarkBackend :: Transport -> (Array PeerView -> Effect Unit) -> Effect (SnarkBackend Depth)
p2pSnarkBackend transport onPeers = do
  pending <- Ref.new (Map.empty :: Map String Reply)
  counter <- Ref.new 0
  known <- Ref.new Set.empty
  peers <- Ref.new (Map.empty :: Map String PeerState)
  selfSpawned <- Ref.new false
  joinQ <- newJoinQueue
  let
    -- Push the current peer table (sorted by id, via `Map`) to the UI.
    report = do
      m <- Ref.read peers
      onPeers (map (\(Tuple id s) -> { id, status: s.status, completed: s.completed }) (Map.toUnfoldable m))
    addPeer id = do
      Ref.modify_ (Map.insert id { status: "idle", completed: 0 }) peers
      report
    setStatus id status = do
      Ref.modify_ (Map.update (\s -> Just s { status = status }) id) peers
      report
    completed id = do
      Ref.modify_ (Map.update (\s -> Just (s { status = "idle", completed = s.completed + 1 })) id) peers
      report
    jobLabel = case _ of
      Base _ -> "proving base"
      Merge _ -> "proving merge"
  onMessage transport \from raw ->
    case decodeMsg raw of
      Right (Join j) | j.fingerprint == fingerprint -> do
        -- Dedup by transport id: a peer re-announces on every discovery.
        fresh <- Ref.modify' (\s -> { state: Set.insert from s, value: not (Set.member from s) }) known
        when fresh do
          addPeer from
          joinQ.push from
      Right (Result r) -> deliver pending r.jobId (Right r.proof)
      Right (Reject r) -> deliver pending r.jobId (Left r.reason)
      _ -> pure unit
  pure \env ->
    { name: "p2p pool"
    -- The FIRST worker is the coordinator's own in-process prover, so a lone
    -- coordinator (no remote peers) proves the whole block itself — the
    -- single-machine path. Each subsequent worker is a remote peer that joined.
    , spawn: do
        isSelf <- liftEffect $ Ref.modify' (\done -> { state: true, value: not done }) selfSpawned
        if isSelf then do
          liftEffect $ addPeer "self"
          pure
            { id: "self"
            , run: \job -> do
                -- Yield to a macrotask before the (synchronous, blocking) local
                -- proof: the pool dispatches over microtasks, so without this the
                -- coordinator would prove back-to-back and never drain its
                -- message queue — the relayed `Join`s from peers would never be
                -- processed and no peer could ever enter the pool. The yield lets
                -- queued joins/results process and the dispatcher hand work to
                -- the peers between local proofs.
                delay (Milliseconds 1.0)
                liftEffect $ setStatus "self" (jobLabel job)
                proof <- liftEffect $ proveItem env.compiledTx job
                liftEffect $ completed "self"
                pure proof
            , terminate: pure unit
            }
        else do
          peerId <- joinQ.pull
          pure
            { id: peerId
            , run: \job -> do
                jobId <- liftEffect $ Ref.modify' (\n -> { state: n + 1, value: "job-" <> show (n + 1) }) counter
                liftEffect $ setStatus peerId (jobLabel job)
                slot <- liftEffect EffectAVar.empty
                liftEffect $ Ref.modify_ (Map.insert jobId slot) pending
                liftEffect $ sendTo transport peerId (encodeMsg (Assign { jobId, work: encodeWorkItem job }))
                res <- AVar.take slot
                liftEffect $ Ref.modify_ (Map.delete jobId) pending
                case res of
                  Left reason -> do
                    liftEffect $ setStatus peerId "idle"
                    liftEffect $ throw ("p2p worker " <> peerId <> " rejected job " <> jobId <> ": " <> reason)
                  Right proofStr -> case decodeCompiledProof env proofStr of
                    Left err -> liftEffect $ throw ("p2p decodeCompiledProof failed: " <> show err)
                    Right proof -> do
                      liftEffect $ completed peerId
                      pure proof
            , terminate: do
                Ref.modify_ (Set.delete peerId) known
                Ref.modify_ (Map.delete peerId) peers
                report
            }
    }

-- | Run the whole one-block pipeline as the coordinator: install the p2p backend
-- | and drive the shared engine over a DYNAMIC pool of remote prover peers — it
-- | starts immediately and each peer that joins the session picks up work, so
-- | there is no peer count to fix up front (the pool is `Dynamic`). A generous
-- | job timeout — remote proving is slow, and a spurious reassignment just hands
-- | the job to another peer.
runCoordinator :: Transport -> (Array PeerView -> Effect Unit) -> EngineCallbacks -> Effect Unit
runCoordinator transport onPeers cb = do
  backend <- p2pSnarkBackend transport onPeers
  runWith backend Dynamic (Milliseconds 600000.0) cb
