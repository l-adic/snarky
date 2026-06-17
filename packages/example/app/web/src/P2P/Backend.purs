-- | The coordinator side of the star: a `SnarkBackend` whose workers are remote
-- | peers reached over a `Transport`. It is the twin of the wasm-pool's
-- | `webWorkerSnarkBackend`, but the channel is `Transport.sendTo` (a network
-- | peer) instead of `postMessage` (a local Web Worker), and workers are
-- | discovered dynamically via the `Join` handshake rather than spawned.
-- |
-- | The pool (`Snarky.Example.Snark.Pool.runPool`) drives this over a `Dynamic`
-- | pool: the first worker is the coordinator's OWN prover — a nested Web Worker
-- | (`prover.js`) so it proves async, off the coordinator's thread (a lone
-- | coordinator thus proves the whole block itself — the single-machine path) —
-- | and every subsequent `spawn` blocks until a peer `Join`s, so the pool grows
-- | as peers arrive. Reliability (timeout → reassign, at-most-once) is the pool's,
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

import Colog (LogAction(..), Msg(..), Severity(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Reflectable (reflectType)
import Data.Set as Set
import Data.Time.Duration (Milliseconds(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.AVar (AVar)
import Effect.AVar as EffectAVar
import Effect.Aff (Aff, forkAff)
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign (unsafeFromForeign)
import Pickles.Prove.SerializeProof (decodeCompiledProof)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.P2P.Protocol (Msg(..), decodeMsg, encodeMsg, fingerprint)
import Snarky.Example.P2P.Transport (Transport, onMessage, onPeer, sendTo)
import Snarky.Example.Snark.Pool (PoolSize(Dynamic))
import Snarky.Example.Snark.Work (WorkItem(..), encodeWorkItem)
import Snarky.Example.Snark.Worker (SnarkBackend)
import Snarky.Example.Web.Engine (Depth, EngineCallbacks, runWith)
import Type.Proxy (Proxy(..))
import Web.Worker.MessageEvent (data_)
import Web.Worker.Worker (Worker)
import Web.Worker.Worker as WW

-- | The coordinator's own prover, a nested Web Worker (`prover.js`); the factory
-- | + thread hint are set on the global scope by `p2p-worker.js`.
foreign import spawnLocalProver :: Effect Worker
foreign import localProverThreads :: Effect Int

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

-- | Relay a nested-prover log line to a colog logger at its reported severity.
relayLog :: Logger -> String -> String -> Effect Unit
relayLog logger text = case _ of
  "debug" -> Log.logDebug logger text
  "warning" -> Log.logWarning logger text
  "error" -> Log.logError logger text
  _ -> Log.logInfo logger text

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
p2pSnarkBackend :: Transport -> Logger -> (Array PeerView -> Effect Unit) -> Effect (SnarkBackend Depth)
p2pSnarkBackend transport logger onPeers = do
  pending <- Ref.new (Map.empty :: Map String Reply)
  counter <- Ref.new 0
  known <- Ref.new Set.empty
  peers <- Ref.new (Map.empty :: Map String PeerState)
  -- A remote peer's in-flight reply slot, keyed by peer id, so a `Leave` can
  -- reject it immediately (the run then throws → the pool reassigns the job).
  peerSlot <- Ref.new (Map.empty :: Map String Reply)
  selfSpawned <- Ref.new false
  -- The coordinator's OWN prover (the nested prover.js worker). Construct the
  -- Worker object now — that is cheap (prover.js boots no wasm until it gets an
  -- `init`) — and wire its message handler. Its COMPILE (`init`) is deferred to
  -- the first pool spawn (see `spawn` below), so it compiles while the engine is
  -- idle (proving phase), not fighting the engine's own setup compile. It signals
  -- `ready` when compiled; the `selfReply` slot carries each job's result back.
  selfWorker <- spawnLocalProver
  selfThreads <- localProverThreads
  selfReply <- EffectAVar.empty :: Effect Reply
  selfReady <- EffectAVar.empty :: Effect (AVar (Either String Unit))
  flip WW.onMessage selfWorker \ev ->
    let
      r =
        unsafeFromForeign (data_ ev)
          :: { tag :: String
             , proof :: String
             , reason :: String
             , value :: { severity :: String, text :: String }
             }
    in
      case r.tag of
        "ready" -> void $ EffectAVar.tryPut (Right unit) selfReady
        "proof" -> void $ EffectAVar.put (Right r.proof) selfReply mempty
        "reject" -> void $ EffectAVar.put (Left r.reason) selfReply mempty
        -- A compile/init failure resolves the ready signal as a failure, so the
        -- self prover is simply never offered to the pool (rather than hanging).
        "error" -> void $ EffectAVar.tryPut (Left r.reason) selfReady
        -- Relay the nested prover's colog (SRS/compile + status) to the
        -- coordinator's own logger → its UI.
        "log" -> relayLog logger ("[self] " <> r.value.text) r.value.severity
        _ -> pure unit
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
    removePeer id = do
      Ref.modify_ (Map.delete id) peers
      report
    jobLabel = case _ of
      Base _ -> "proving base"
      Merge _ -> "proving merge"
    -- A peer announced it is leaving (page unload). Forget it, and if it had a
    -- job in flight, reject that job's reply now so the pool reassigns it at once
    -- (its `run` throws → reclaim terminates it → removed from the table).
    peerGone id = do
      Ref.modify_ (Set.delete id) known
      m <- Ref.read peerSlot
      case Map.lookup id m of
        Just slot -> void $ EffectAVar.put (Left "peer left") slot mempty
        Nothing -> removePeer id
  -- Log every peer the transport discovers, even before it announces: the key
  -- diagnostic for a worker that never gets recognized — if "discovered peer X"
  -- appears but "peer X joined the pool" never does, the link is up but its
  -- Join isn't arriving; if neither appears, the transport never connected them.
  onPeer transport \id ->
    Log.logInfo logger ("[pool] discovered peer " <> id <> " (awaiting its Join)")
  onMessage transport \from raw ->
    case decodeMsg raw of
      Right (Join j)
        | j.fingerprint == fingerprint -> do
            -- Dedup by transport id: a peer re-announces on every discovery.
            fresh <- Ref.modify' (\s -> { state: Set.insert from s, value: not (Set.member from s) }) known
            when fresh do
              Log.logInfo logger ("[pool] peer " <> from <> " joined the pool")
              addPeer from
              joinQ.push from
        | otherwise ->
            Log.logWarning logger
              ( "[pool] ignoring Join from " <> from <> ": fingerprint \"" <> j.fingerprint
                  <> "\" != \""
                  <> fingerprint
                  <> "\" (incompatible build)"
              )
      Right (Result r) -> deliver pending r.jobId (Right r.proof)
      Right (Reject r) -> deliver pending r.jobId (Left r.reason)
      Right (Leave l) -> peerGone l.peerId
      -- The coordinator assigns; it never receives an `Assign`. Ignore it.
      Right (Assign _) -> pure unit
      Left _ -> Log.logDebug logger ("[pool] undecodable message from " <> from)
  pure \env ->
    { name: "p2p pool"
    -- The coordinator's OWN prover and the remote peers are offered through the
    -- SAME join queue: a synthetic "self" id is the nested prover, any other id is
    -- a peer that announced `Join`. So a lone coordinator (no peers) still proves
    -- the whole block itself — its self worker is the only one offered.
    , spawn: do
        -- On the FIRST spawn (the pool is dispatching now, so the engine is past
        -- its own setup compile) kick off the self-prover's compile in the
        -- BACKGROUND and offer it to the join queue once it is `ready`. Forked, so
        -- it never holds up the spawn loop from taking peers that are already
        -- available; deferred to here (not backend construction) so it compiles
        -- while the engine is idle rather than fighting the engine's setup
        -- compile. Gating on `ready` makes its first job's timeout cover only
        -- proving, not the (multi-minute) compile — the fix for the self worker
        -- timing out on its very first job. A self that fails to compile is simply
        -- never offered.
        first <- liftEffect $ Ref.modify' (\done -> { state: true, value: not done }) selfSpawned
        when first $ void $ forkAff do
          liftEffect $ WW.postMessage
            { type: "init", chain: "Testnet", depth: reflectType (Proxy :: Proxy Depth), threads: selfThreads }
            selfWorker
          ready <- AVar.take selfReady
          case ready of
            Right _ -> liftEffect $ joinQ.push "self"
            Left reason -> liftEffect $ Log.logError logger ("[pool] self prover failed to compile: " <> reason)
        peerId <- joinQ.pull
        if peerId == "self" then do
          liftEffect $ addPeer "self"
          pure
            { id: "self"
            , run: \job -> do
                liftEffect $ setStatus "self" (jobLabel job)
                liftEffect $ WW.postMessage { type: "job", work: encodeWorkItem job } selfWorker
                res <- AVar.take selfReply
                case res of
                  Left reason -> do
                    liftEffect $ setStatus "self" "idle"
                    liftEffect $ throw ("self prover: " <> reason)
                  Right proofStr -> case decodeCompiledProof env proofStr of
                    Left err -> liftEffect $ throw ("self decodeCompiledProof failed: " <> show err)
                    Right proof -> do
                      liftEffect $ completed "self"
                      pure proof
            , terminate: do
                removePeer "self"
                WW.terminate selfWorker
            }
        else
          pure
            { id: peerId
            , run: \job -> do
                jobId <- liftEffect $ Ref.modify' (\n -> { state: n + 1, value: "job-" <> show (n + 1) }) counter
                liftEffect $ setStatus peerId (jobLabel job)
                slot <- liftEffect EffectAVar.empty
                liftEffect $ Ref.modify_ (Map.insert jobId slot) pending
                -- Track this peer's in-flight slot so a `Leave` can reject it.
                liftEffect $ Ref.modify_ (Map.insert peerId slot) peerSlot
                liftEffect $ sendTo transport peerId (encodeMsg (Assign { jobId, work: encodeWorkItem job }))
                res <- AVar.take slot
                liftEffect $ Ref.modify_ (Map.delete jobId) pending
                liftEffect $ Ref.modify_ (Map.delete peerId) peerSlot
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
                removePeer peerId
            }
    }

-- | Run the whole one-block pipeline as the coordinator: install the p2p backend
-- | and drive the shared engine over a DYNAMIC pool of remote prover peers — it
-- | starts immediately and each peer that joins the session picks up work, so
-- | there is no peer count to fix up front (the pool is `Dynamic`). The 120 s
-- | job timeout is the BACKSTOP for an ungraceful peer death (a graceful exit
-- | sends `Leave`, reassigning at once); the pool only reassigns on timeout, it
-- | doesn't kill the slow original, so a merely-slow peer can still win.
runCoordinator :: Transport -> (Array PeerView -> Effect Unit) -> EngineCallbacks -> Effect Unit
runCoordinator transport onPeers cb = do
  -- A logger for the transport router (which runs outside the engine, so it has
  -- no `env.logger`): relay through the same `cb.onLog` sink the engine uses, so
  -- pool discovery/Join diagnostics land in the coordinator's UI log.
  let
    logger = LogAction \(Msg { severity, text }) ->
      cb.onLog { severity: severityLabel severity, text }
  backend <- p2pSnarkBackend transport logger onPeers
  runWith backend Dynamic (Milliseconds 120000.0) cb

-- | Colog `Severity` → the string label `EngineCallbacks.onLog` expects.
severityLabel :: Severity -> String
severityLabel = case _ of
  Debug -> "debug"
  Info -> "info"
  Warning -> "warning"
  Error -> "error"
