-- | The browser coordinator: instantiate the generic P2P star coordinator
-- | (`Snarky.Example.P2P.Coordinator`) with the snark payload and the
-- | coordinator's OWN prover — a nested Web Worker (`prover.js`).
-- |
-- | All the coordination (the join queue, the transport router, the peer table,
-- | timeout→reassign via the pool, Leave handling) lives in the generic module
-- | and is Node-testable. This module supplies the two snark/browser specifics:
-- |   * the codecs — `encodeWorkItem` to assign, `decodeCompiledProof` to read a
-- |     result back (via `mapResult` in the per-`Env` projection);
-- |   * `prepareLocal` — warm up the nested Web Worker self-prover and expose it
-- |     as a `RawWorker` (post `init`, wait for `ready`, then post each job and
-- |     await its reply).
module Snarky.Example.P2P.Backend
  ( p2pSnarkBackend
  , runCoordinator
  ) where

import Prelude

import Colog (LogAction(..), Msg(..), Severity(..))
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Newtype (un)
import Data.Reflectable (reflectType)
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.AVar (AVar)
import Effect.AVar as EffectAVar
import Effect.Aff (Aff)
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Foreign (unsafeFromForeign)
import Mina.ChainId (ChainId)
import Pickles.Prove.SerializeProof (decodeCompiledProof)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.P2P.Coordinator (PeerView, RawWorker, mapResult, mkStarBackend)
import Snarky.Example.P2P.Transport (Transport)
import Snarky.Example.P2P.Types (Payload(..))
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

-- | A short peer-table label for a work item.
jobLabel :: WorkItem Depth -> String
jobLabel = case _ of
  Base _ -> "proving base"
  Merge _ -> "proving merge"

-- | Relay a nested-prover log line to a colog logger at its reported severity.
relayLog :: Logger -> String -> String -> Effect Unit
relayLog logger text = case _ of
  "debug" -> Log.logDebug logger text
  "warning" -> Log.logWarning logger text
  "error" -> Log.logError logger text
  _ -> Log.logInfo logger text

-- | Spawn the nested Web Worker self-prover (cheap — it boots no wasm until
-- | `init`), wire its message handler, and return the `prepareLocal` action the
-- | generic coordinator runs once dispatching starts: post `init` (the compile),
-- | wait for `ready`, then expose a `RawWorker` that proves a job per round-trip.
mkLocalProver :: ChainId -> Logger -> Effect (Aff (Either String (RawWorker (WorkItem Depth))))
mkLocalProver chainId logger = do
  selfWorker <- spawnLocalProver
  selfThreads <- localProverThreads
  selfReply <- EffectAVar.empty :: Effect (AVar (Either String Payload))
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
        "proof" -> void $ EffectAVar.put (Right (Payload r.proof)) selfReply mempty
        "reject" -> void $ EffectAVar.put (Left r.reason) selfReply mempty
        -- A compile/init failure resolves ready as a failure → never offered.
        "error" -> void $ EffectAVar.tryPut (Left r.reason) selfReady
        -- Relay the nested prover's colog (SRS/compile + status) to our logger.
        "log" -> relayLog logger ("[self] " <> r.value.text) r.value.severity
        _ -> pure unit
  pure do
    liftEffect $ WW.postMessage
      { type: "init", chain: show chainId, depth: reflectType (Proxy :: Proxy Depth), threads: selfThreads }
      selfWorker
    ready <- AVar.take selfReady
    case ready of
      Left reason -> pure (Left reason)
      Right _ -> pure $ Right
        { run: \job -> do
            liftEffect $ WW.postMessage { type: "job", work: encodeWorkItem job } selfWorker
            res <- AVar.take selfReply
            case res of
              Left reason -> liftEffect $ throw ("self prover: " <> reason)
              Right proof -> pure proof
        , terminate: WW.terminate selfWorker
        }

-- | Build the coordinator's `SnarkBackend`: the generic star backend (raw String
-- | results) projected per `Env` by decoding each result into a `CompiledProof`.
p2pSnarkBackend :: ChainId -> Transport -> Logger -> (Array PeerView -> Effect Unit) -> Effect (SnarkBackend Depth)
p2pSnarkBackend chainId transport logger onPeers = do
  prepareLocal <- mkLocalProver chainId logger
  base <- mkStarBackend
    { logger
    , transport
    , encodeJob: Payload <<< encodeWorkItem
    , jobLabel
    , prepareLocal
    , onPeers
    }
  pure \env -> mapResult (lmap show <<< decodeCompiledProof env <<< un Payload) base

-- | Run the whole one-block pipeline as the coordinator: install the p2p backend
-- | and drive the shared engine over a DYNAMIC pool of remote prover peers. The
-- | 120 s job timeout is the BACKSTOP for an ungraceful peer death (a graceful
-- | exit sends `Leave`, reassigning at once); the pool only reassigns on timeout,
-- | it doesn't kill the slow original, so a merely-slow peer can still win.
runCoordinator :: ChainId -> Transport -> (Array PeerView -> Effect Unit) -> EngineCallbacks -> Effect Unit
runCoordinator chainId transport onPeers cb = do
  -- A logger for the transport router (which runs outside the engine, so it has
  -- no `env.logger`): relay through the same `cb.onLog` sink the engine uses.
  let
    logger = LogAction \(Msg { severity, text }) ->
      cb.onLog { severity: severityLabel severity, text }
  backend <- p2pSnarkBackend chainId transport logger onPeers
  runWith chainId backend Dynamic (Milliseconds 120000.0) cb

-- | Colog `Severity` → the string label `EngineCallbacks.onLog` expects.
severityLabel :: Severity -> String
severityLabel = case _ of
  Debug -> "debug"
  Info -> "info"
  Warning -> "warning"
  Error -> "error"
