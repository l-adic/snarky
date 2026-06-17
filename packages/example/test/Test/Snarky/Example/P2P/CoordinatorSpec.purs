-- | Coordination scenario tests for the P2P star, run entirely in Node over the
-- | in-memory bus with STUB provers — no wasm, no browser. They exercise the
-- | generic coordinator (`Snarky.Example.P2P.Coordinator`) + peer
-- | (`Snarky.Example.P2P.Peer`), the exact code the browser instantiates:
-- |
-- |   * late join     — a worker that connects after the pool is already running
-- |     picks up queued work;
-- |   * quit + rejoin — a worker that leaves is dropped from the pool, and is
-- |     re-added (and works again) when it reconnects;
-- |   * quit mid-job  — a worker holding an in-flight job that leaves has that job
-- |     reassigned to another worker AT ONCE (the `Leave` path, not the timeout).
-- |
-- | The coordinator's own self-prover is disabled here (`prepareLocal` returns
-- | `Left`) so the scenarios are purely about remote-peer participation. Jobs are
-- | plain `String`s; results come back as the wire `Payload` (identity codecs).
module Test.Snarky.Example.P2P.CoordinatorSpec
  ( spec
  ) where

import Prelude

import Colog (LogAction(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Time.Duration (Milliseconds(..))
import Data.Tuple (Tuple(..), fst, snd)
import Effect (Effect)
import Effect.Aff (Aff, delay, error, forkAff, killFiber)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Snarky.Example.AsyncQueue (dequeue, enqueue, newQueue)
import Snarky.Example.Log (Logger)
import Snarky.Example.P2P.Coordinator (PeerView, mkStarBackend)
import Snarky.Example.P2P.Peer (runStarPeer)
import Snarky.Example.P2P.Protocol (Msg(..), encodeMsg)
import Snarky.Example.P2P.Transport (Transport, broadcast, myId)
import Snarky.Example.P2P.Types (Payload(..), PeerId(..))
import Snarky.Example.Snark.Pool (PoolSize(Dynamic), runPool)
import Test.Snarky.Example.P2P.InMemoryBus (Bus, connect, disconnect, newBus)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

silentLogger :: Logger
silentLogger = LogAction \_ -> pure unit

-- | A stub prover: returns "proof:<work>" immediately.
stubProve :: Payload -> Effect Payload
stubProve (Payload work) = pure (Payload ("proof:" <> work))

-- | Start a real peer on the bus with the given prover; returns its transport (so
-- | a test can make it `Leave` / disconnect).
startPeer :: Bus -> String -> (Payload -> Effect Payload) -> Effect Transport
startPeer bus pid prove = do
  t <- connect bus pid
  runStarPeer
    { transport: t
    , logger: silentLogger
    , prove
    , describeJob: un Payload
    , onPhase: \_ -> pure unit
    , reannounceMs: 50.0
    , reannounceMax: 20
    }
  pure t

-- | A fake peer that announces availability but NEVER answers an `Assign` — it
-- | models a worker that received a job and then vanished. Returns its transport.
startSilentPeer :: Bus -> String -> Effect Transport
startSilentPeer bus pid = do
  t <- connect bus pid
  broadcast t (encodeMsg (Join { peerId: myId t }))
  pure t

-- | Make a peer quit: announce `Leave`, then go off the bus.
quit :: Bus -> Transport -> String -> Effect Unit
quit bus t pid = do
  broadcast t (encodeMsg (Leave { peerId: PeerId pid }))
  disconnect bus pid

-- | The coordinator under test: its pool (running a `Dynamic` star backend with
-- | no self-prover), a way to submit jobs, and views of the posted results + the
-- | peer table.
type Harness =
  { submit :: String -> Aff Unit
  , results :: Effect (Array (Tuple String Payload))
  , peers :: Effect (Array PeerView)
  , stop :: Aff Unit
  }

mkHarness :: Bus -> Milliseconds -> Aff Harness
mkHarness bus timeout = do
  coordT <- liftEffect (connect bus "coord")
  resultsRef <- liftEffect (Ref.new [])
  peersRef <- liftEffect (Ref.new [])
  backend <- liftEffect $ mkStarBackend
    { logger: silentLogger
    , transport: coordT
    , encodeJob: Payload
    , jobLabel: const "proving"
    , prepareLocal: pure (Left "no self worker in test")
    , onPeers: \ps -> Ref.write ps peersRef
    }
  workQ <- newQueue
  let
    io =
      { next: dequeue workQ
      , post: \(Tuple jid r) -> liftEffect $ Ref.modify_ (\xs -> Array.snoc xs (Tuple jid r)) resultsRef
      , describe: \jid _ -> jid
      }
  fib <- forkAff $ runPool silentLogger timeout Dynamic backend io
  pure
    { submit: \j -> enqueue workQ (Tuple j j)
    , results: Ref.read resultsRef
    , peers: Ref.read peersRef
    , stop: killFiber (error "scenario end") fib
    }

-- | Poll `read` until `done` holds, or a ~5s deadline (then give up so the
-- | assertion fails on the stale value rather than hanging).
awaitUntil :: forall a. Effect a -> (a -> Boolean) -> Aff Unit
awaitUntil read done = go 0
  where
  go :: Int -> Aff Unit
  go i = do
    a <- liftEffect read
    if done a then pure unit
    else if i >= 250 then pure unit
    else delay (Milliseconds 20.0) *> go (i + 1)

hasPeer :: String -> Array PeerView -> Boolean
hasPeer pid = Array.any (\p -> p.id == pid)

peerStatus :: String -> Array PeerView -> Maybe String
peerStatus pid ps = _.status <$> Array.find (\p -> p.id == pid) ps

-- | The proofs posted, as plain strings (unwrapping the wire `Payload`).
proofs :: Array (Tuple String Payload) -> Array String
proofs = map (un Payload <<< snd)

spec :: SpecT Aff Unit Aff Unit
spec = describe "P2P star coordination" do
  it "picks up a worker that joins after the pool has started (late join)" do
    bus <- liftEffect newBus
    h <- mkHarness bus (Milliseconds 2000.0)
    -- two jobs queue with no workers connected
    h.submit "j0"
    h.submit "j1"
    delay (Milliseconds 40.0)
    -- a worker joins LATE and should drain the backlog
    _ <- liftEffect (startPeer bus "p1" stubProve)
    awaitUntil h.results (\r -> Array.length r >= 2)
    res <- liftEffect h.results
    Array.sort (map fst res) `shouldEqual` [ "j0", "j1" ]
    Array.sort (proofs res) `shouldEqual` [ "proof:j0", "proof:j1" ]
    ps <- liftEffect h.peers
    hasPeer "p1" ps `shouldEqual` true
    h.stop

  it "drops a worker that quits and re-adds it when it rejoins" do
    bus <- liftEffect newBus
    h <- mkHarness bus (Milliseconds 2000.0)
    p1 <- liftEffect (startPeer bus "p1" stubProve)
    h.submit "j0"
    awaitUntil h.results (\r -> Array.length r >= 1)
    liftEffect (hasPeer "p1" <$> h.peers) >>= \x -> x `shouldEqual` true
    -- p1 quits gracefully → dropped from the pool
    liftEffect (quit bus p1 "p1")
    awaitUntil h.peers (\ps -> not (hasPeer "p1" ps))
    liftEffect (hasPeer "p1" <$> h.peers) >>= \x -> x `shouldEqual` false
    -- p1 rejoins → re-added and works again
    _ <- liftEffect (startPeer bus "p1" stubProve)
    h.submit "j1"
    awaitUntil h.results (\r -> Array.length r >= 2)
    liftEffect (hasPeer "p1" <$> h.peers) >>= \x -> x `shouldEqual` true
    res <- liftEffect h.results
    Array.sort (map fst res) `shouldEqual` [ "j0", "j1" ]
    h.stop

  it "drops an idle worker whose connection drops, with no Leave message (onPeerLeave)" do
    bus <- liftEffect newBus
    -- long timeout: the only thing that can drop an IDLE peer here is onPeerLeave
    -- (it has no in-flight job for the timeout to catch, and sends no Leave).
    h <- mkHarness bus (Milliseconds 60000.0)
    _ <- liftEffect (startPeer bus "p1" stubProve)
    awaitUntil h.peers (hasPeer "p1")
    liftEffect (hasPeer "p1" <$> h.peers) >>= \x -> x `shouldEqual` true
    -- its connection simply drops — no Leave broadcast, just off the bus
    liftEffect (disconnect bus "p1")
    awaitUntil h.peers (\ps -> not (hasPeer "p1" ps))
    liftEffect (hasPeer "p1" <$> h.peers) >>= \x -> x `shouldEqual` false
    h.stop

  it "reassigns a quitting worker's in-flight job to another worker (Leave path)" do
    bus <- liftEffect newBus
    -- long timeout so we prove the Leave-driven reassign, not the timeout backstop
    h <- mkHarness bus (Milliseconds 60000.0)
    -- a silent worker takes the job but never replies
    s <- liftEffect (startSilentPeer bus "silent")
    h.submit "j0"
    awaitUntil h.peers (\ps -> peerStatus "silent" ps == Just "proving")
    -- a live worker is now available to take the reassignment
    _ <- liftEffect (startPeer bus "p2" stubProve)
    delay (Milliseconds 30.0)
    -- the silent worker quits mid-job → its job is reassigned at once
    liftEffect (quit bus s "silent")
    awaitUntil h.results (\r -> Array.length r >= 1)
    res <- liftEffect h.results
    map fst res `shouldEqual` [ "j0" ]
    proofs res `shouldEqual` [ "proof:j0" ] -- proved by the live worker
    h.stop
