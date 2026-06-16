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
import Snarky.Example.P2P.Protocol (Msg(..), decodeMsg, encodeMsg, fingerprint)
import Snarky.Example.P2P.Transport (Transport, broadcast, myId, onMessage, onPeer, sendTo)
import Snarky.Example.Prover (buildProver)
import Snarky.Example.Web.Engine (Depth)
import Type.Proxy (Proxy(..))

-- | The chain the coordinator's engine compiles against
-- | (`Snarky.Example.Web.Engine` uses `Testnet`). A worker MUST compile the same
-- | circuit or the proofs it returns will not verify under the coordinator's VK.
chainTag :: String
chainTag = "Testnet"

-- | What the worker reports to its own UI (the worker JS wires these to
-- | `postMessage`, mirroring the engine's callbacks on the coordinator).
type WorkerPeerEvents =
  { onLog :: { severity :: String, text :: String } -> Effect Unit
  , onPhase :: String -> Effect Unit
  }

-- | A work item's kind for display, peeked from the encoded `WorkItem`'s tag
-- | (`{ tag: "base" | "merge", … }`) without fully decoding it.
jobLabel :: String -> String
jobLabel work = case readJSON work :: Either _ { tag :: String } of
  Right r -> r.tag
  Left _ -> "job"

runWorkerPeer :: Transport -> WorkerPeerEvents -> Effect Unit
runWorkerPeer transport ev = do
  ev.onPhase "compiling circuit"
  prove <- buildProver { chain: chainTag, depth: reflectType (Proxy :: Proxy Depth) }
  ev.onPhase "ready — awaiting work"
  ev.onLog { severity: "info", text: "circuit compiled; waiting for the coordinator to assign work" }
  count <- Ref.new 0
  let
    announce = broadcast transport (encodeMsg (Join { peerId: myId transport, fingerprint }))
  onMessage transport \from raw ->
    case decodeMsg raw of
      Right (Assign a) -> do
        n <- Ref.modify (_ + 1) count
        let label = jobLabel a.work
        ev.onPhase ("proving " <> label <> " (#" <> show n <> ")")
        ev.onLog { severity: "info", text: "assigned " <> label <> " job #" <> show n <> " — proving…" }
        result <- try (prove a.work)
        case result of
          Right proof -> do
            sendTo transport from (encodeMsg (Result { jobId: a.jobId, proof }))
            ev.onLog { severity: "info", text: label <> " job #" <> show n <> " done — proof sent to coordinator" }
            ev.onPhase "ready — awaiting work"
          Left err -> do
            sendTo transport from (encodeMsg (Reject { jobId: a.jobId, reason: message err }))
            ev.onLog { severity: "error", text: label <> " job #" <> show n <> " failed: " <> message err }
            ev.onPhase "ready — awaiting work"
      _ -> pure unit
  -- (Re)announce availability whenever a peer is discovered, so a worker that
  -- booted before the coordinator is still picked up once the coordinator joins.
  onPeer transport \_ -> announce
  announce
