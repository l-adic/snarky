-- | The worker side of the star: compile the circuit once, then answer the
-- | coordinator's `Assign` messages — prove the work item and reply with the
-- | encoded proof (`Result`) or the failure reason (`Reject`). Base and merge
-- | jobs are handled identically (`buildProver`'s closure dispatches on the
-- | decoded `WorkItem`), so a worker is a plain full-core prover.
-- |
-- | The transport is supplied by the caller (the worker JS entry constructs it),
-- | so this module is agnostic to BroadcastChannel vs WebRTC. Proving is
-- | synchronous (it blocks the JS thread while the wasm rayon pool works), which
-- | is why a peer runs off any UI thread and takes one `Assign` at a time.
-- |
-- | `WorkerPeerEvents` surfaces what the worker is doing (compile / each job) to
-- | its own UI — without it the operator sees nothing while the worker proves.
-- |
-- | A worker `Join`s by broadcasting; because a single announce can be lost over
-- | WebRTC (it may race the data channel opening, or the coordinator may still be
-- | discovering us), it re-announces periodically (`reannounce`) until it is
-- | assigned its first job — otherwise a worker that joined an already-running
-- | session could sit silently unused.
module Snarky.Example.P2P.WorkerPeer
  ( WorkerPeerEvents
  , runWorkerPeer
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Reflectable (reflectType)
import Effect (Effect)
import Effect.Exception (message, try)
import Effect.Ref as Ref
import Simple.JSON (readJSON)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.P2P.Protocol (Msg(..), decodeMsg, encodeMsg, fingerprint)
import Snarky.Example.P2P.Transport (Transport, broadcast, myId, onMessage, onPeer, sendTo)
import Snarky.Example.Prover (buildProver)
import Snarky.Example.Web.Engine (Depth)
import Type.Proxy (Proxy(..))

-- | Re-run an action every `ms` until the stop predicate holds or `maxTimes`
-- | runs have happened (whichever first). Used to keep re-broadcasting `Join`.
foreign import reannounce :: Int -> Int -> Effect Boolean -> Effect Unit -> Effect Unit

-- | The chain the coordinator's engine compiles against
-- | (`Snarky.Example.Web.Engine` uses `Testnet`). A worker MUST compile the same
-- | circuit or the proofs it returns will not verify under the coordinator's VK.
chainTag :: String
chainTag = "Testnet"

-- | What the worker reports to its own UI: a colog `Logger` for the log stream
-- | (the same vehicle the engine uses — `buildProver`'s SRS/compile logging flows
-- | through it too) and an `onPhase` for the current-status badge.
type WorkerPeerEvents =
  { logger :: Logger
  , onPhase :: String -> Effect Unit
  }

-- | A work item's kind for display, peeked from the encoded `WorkItem`'s tag
-- | (`{ tag: "base" | "merge", … }`) without fully decoding it.
jobLabel :: String -> String
jobLabel work = case readJSON work :: Either _ { tag :: String } of
  Right r -> r.tag
  Left _ -> "job"

runWorkerPeer :: Transport -> WorkerPeerEvents -> Effect Unit
runWorkerPeer transport { logger, onPhase } = do
  onPhase "compiling circuit"
  prove <- buildProver logger { chain: chainTag, depth: reflectType (Proxy :: Proxy Depth) }
  onPhase "ready — awaiting work"
  Log.logInfo logger "waiting for the coordinator to assign work"
  count <- Ref.new 0
  assigned <- Ref.new false
  let
    announce = broadcast transport (encodeMsg (Join { peerId: myId transport, fingerprint }))
  onMessage transport \from raw ->
    case decodeMsg raw of
      Right (Assign a) -> do
        Ref.write true assigned
        n <- Ref.modify (_ + 1) count
        let label = jobLabel a.work
        onPhase ("proving " <> label <> " (#" <> show n <> ")")
        Log.logInfo logger ("assigned " <> label <> " job #" <> show n <> " — proving…")
        result <- try (prove a.work)
        case result of
          Right proof -> do
            sendTo transport from (encodeMsg (Result { jobId: a.jobId, proof }))
            Log.logInfo logger (label <> " job #" <> show n <> " done — proof sent to coordinator")
            onPhase "ready — awaiting work"
          Left err -> do
            sendTo transport from (encodeMsg (Reject { jobId: a.jobId, reason: message err }))
            Log.logError logger (label <> " job #" <> show n <> " failed: " <> message err)
            onPhase "ready — awaiting work"
      _ -> pure unit
  -- (Re)announce availability whenever a peer is discovered, so a worker that
  -- booted before the coordinator is still picked up once the coordinator joins.
  onPeer transport \_ -> announce
  announce
  -- …and keep re-announcing for a while, since a single broadcast can be lost
  -- over WebRTC — until the coordinator assigns the first job (proof it knows us)
  -- or a bounded number of tries elapse (so an empty room isn't spammed forever).
  reannounce 4000 30 (Ref.read assigned) announce
