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
module Snarky.Example.P2P.WorkerPeer
  ( runWorkerPeer
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Reflectable (reflectType)
import Effect (Effect)
import Effect.Exception (message, try)
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

runWorkerPeer :: Transport -> Effect Unit
runWorkerPeer transport = do
  prove <- buildProver { chain: chainTag, depth: reflectType (Proxy :: Proxy Depth) }
  let
    announce = broadcast transport (encodeMsg (Join { peerId: myId transport, fingerprint }))
  onMessage transport \from raw ->
    case decodeMsg raw of
      Right (Assign a) -> do
        result <- try (prove a.work)
        case result of
          Right proof -> sendTo transport from (encodeMsg (Result { jobId: a.jobId, proof }))
          Left err -> sendTo transport from (encodeMsg (Reject { jobId: a.jobId, reason: message err }))
      _ -> pure unit
  -- (Re)announce availability whenever a peer is discovered, so a worker that
  -- booted before the coordinator is still picked up once the coordinator joins.
  onPeer transport \_ -> announce
  announce
