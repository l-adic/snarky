-- | The coordinator side of the star: a `SnarkBackend` whose workers are remote
-- | peers reached over a `Transport`. It is the twin of the wasm-pool's
-- | `webWorkerSnarkBackend`, but the channel is `Transport.sendTo` (a network
-- | peer) instead of `postMessage` (a local Web Worker), and workers are
-- | discovered dynamically via the `Join` handshake rather than spawned.
-- |
-- | The pool (`Snarky.Example.Snark.Pool.runPool`) drives this unchanged: each
-- | `spawn` blocks until a peer `Join`s, so `poolSize` means "wait for N peers,
-- | then start dispatching". Reliability (timeout → reassign, at-most-once) is
-- | the pool's, so a peer that vanishes mid-job is handled by the job timeout
-- | (its `Result` never arrives → reassign).
-- |
-- | One `Transport.onMessage` router (installed once when the backend is built)
-- | fans `Result`/`Reject` to the waiting `run` by `jobId`, and turns each fresh
-- | `Join` into a queued peer that the next `spawn` claims.
module Snarky.Example.P2P.Backend
  ( p2pSnarkBackend
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
import Effect (Effect)
import Effect.AVar (AVar)
import Effect.AVar as EffectAVar
import Effect.Aff (Aff)
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Pickles.Prove.SerializeProof (decodeCompiledProof)
import Snarky.Example.P2P.Protocol (Msg(..), decodeMsg, encodeMsg, fingerprint)
import Snarky.Example.P2P.Transport (Transport, onMessage, sendTo)
import Snarky.Example.Snark.Work (encodeWorkItem)
import Snarky.Example.Snark.Worker (SnarkBackend)
import Snarky.Example.Web.Engine (Depth, EngineCallbacks, runWith)

-- | A reply slot for one assigned job: filled by the router with the worker's
-- | encoded proof (`Right`) or a rejection reason (`Left`).
type Reply = AVar (Either String String)

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
p2pSnarkBackend :: Transport -> Effect (SnarkBackend Depth)
p2pSnarkBackend transport = do
  pending <- Ref.new (Map.empty :: Map String Reply)
  counter <- Ref.new 0
  known <- Ref.new Set.empty
  joinQ <- newJoinQueue
  onMessage transport \from raw ->
    case decodeMsg raw of
      Right (Join j) | j.fingerprint == fingerprint -> do
        -- Dedup by transport id: a peer re-announces on every discovery.
        fresh <- Ref.modify' (\s -> { state: Set.insert from s, value: not (Set.member from s) }) known
        when fresh (joinQ.push from)
      Right (Result r) -> deliver pending r.jobId (Right r.proof)
      Right (Reject r) -> deliver pending r.jobId (Left r.reason)
      _ -> pure unit
  pure \env ->
    { name: "p2p peer"
    , spawn: do
        peerId <- joinQ.pull
        pure
          { id: peerId
          , run: \job -> do
              jobId <- liftEffect $ Ref.modify' (\n -> { state: n + 1, value: "job-" <> show (n + 1) }) counter
              slot <- liftEffect EffectAVar.empty
              liftEffect $ Ref.modify_ (Map.insert jobId slot) pending
              liftEffect $ sendTo transport peerId (encodeMsg (Assign { jobId, work: encodeWorkItem job }))
              res <- AVar.take slot
              liftEffect $ Ref.modify_ (Map.delete jobId) pending
              case res of
                Left reason -> liftEffect $ throw ("p2p worker " <> peerId <> " rejected job " <> jobId <> ": " <> reason)
                Right proofStr -> case decodeCompiledProof env proofStr of
                  Left err -> liftEffect $ throw ("p2p decodeCompiledProof failed: " <> show err)
                  Right proof -> pure proof
          , terminate: Ref.modify_ (Set.delete peerId) known
          }
    }

-- | Run the whole one-block pipeline as the coordinator: install the p2p backend
-- | and drive the shared engine over `poolSize` remote prover peers. A generous
-- | job timeout — remote proving is slow, and a spurious reassignment just hands
-- | the job to another peer.
runCoordinator :: Transport -> Int -> EngineCallbacks -> Effect Unit
runCoordinator transport poolSize cb = do
  backend <- p2pSnarkBackend transport
  runWith backend poolSize (Milliseconds 600000.0) cb
