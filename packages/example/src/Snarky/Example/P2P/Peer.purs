-- | The worker side of the P2P star, generic over the work payload (which travels
-- | as an encoded `Payload`). A peer announces availability (`Join`), then answers
-- | the coordinator's `Assign` messages: prove the work via the injected `prove`,
-- | and reply with the encoded result (`Result`) or the failure reason (`Reject`).
-- |
-- | Because a single announce can be lost over WebRTC (it may race the data
-- | channel opening, or the coordinator may still be discovering us), the peer
-- | re-announces: targeted to each peer the instant it is discovered (`onPeer`),
-- | and on a bounded timer loop until it is assigned its first job — so a worker
-- | that joined an already-running session isn't left silently unused.
-- |
-- | Browser-free: `prove` and `describeJob` are injected, so the same loop runs in
-- | a browser worker (real wasm prover) or in a Node test (stub prover).
module Snarky.Example.P2P.Peer
  ( PeerConfig
  , runStarPeer
  ) where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRecM)
import Control.Parallel (parOneOf)
import Data.Either (Either(..))
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.AVar (AVar)
import Effect.AVar as EffectAVar
import Effect.Aff (delay, launchAff_)
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Exception (message, try)
import Effect.Ref as Ref
import Fmt (fmt)
import Snarky.Example.Log (Logger)
import Snarky.Example.Log as Log
import Snarky.Example.P2P.Protocol (Msg(..), decodeMsg, encodeMsg)
import Snarky.Example.P2P.Transport (Transport, broadcast, myId, onMessage, onPeer, sendTo)
import Snarky.Example.P2P.Types (Payload)

type PeerConfig =
  { transport :: Transport
  , logger :: Logger
  -- Prove an assigned (encoded) work item, returning the encoded result.
  , prove :: Payload -> Effect Payload
  -- A human label for the encoded work item (UI / logs).
  , describeJob :: Payload -> String
  -- Report the current status to the peer's own UI.
  , onPhase :: String -> Effect Unit
  -- Re-announce cadence: every `reannounceMs`, up to `reannounceMax` tries.
  , reannounceMs :: Number
  , reannounceMax :: Int
  }

-- | Run the peer loop. Assumes the prover is already built (the caller does any
-- | compile first); this just announces and answers `Assign`s.
runStarPeer :: PeerConfig -> Effect Unit
runStarPeer cfg = do
  cfg.onPhase "ready — awaiting work"
  Log.logInfo cfg.logger "waiting for the coordinator to assign work"
  count <- Ref.new 0
  -- One-shot signal raised when the first job is assigned, stopping the
  -- re-announce loop (proof the coordinator knows us).
  stop <- EffectAVar.empty :: Effect (AVar Unit)
  let
    joinMsg = encodeMsg (Join { peerId: myId cfg.transport })
    announce = broadcast cfg.transport joinMsg
  onMessage cfg.transport \from raw ->
    case decodeMsg raw of
      Right (Assign a) -> do
        void $ EffectAVar.tryPut unit stop
        n <- Ref.modify (_ + 1) count
        let desc = cfg.describeJob a.work
        cfg.onPhase (fmt @"proving #{n} · {desc}" { n, desc })
        Log.logInfo cfg.logger (fmt @"assigned job #{n} ({desc}) — proving…" { n, desc })
        result <- try (cfg.prove a.work)
        case result of
          Right proof -> do
            sendTo cfg.transport from (encodeMsg (Result { jobId: a.jobId, proof }))
            Log.logInfo cfg.logger (fmt @"job #{n} done — proof sent to coordinator" { n })
            cfg.onPhase "ready — awaiting work"
          Left err -> do
            sendTo cfg.transport from (encodeMsg (Reject { jobId: a.jobId, reason: message err }))
            Log.logError cfg.logger (fmt @"job #{n} failed: {err}" { n, err: message err })
            cfg.onPhase "ready — awaiting work"
      _ -> pure unit
  -- Announce to each peer the instant it is discovered: a targeted `sendTo` (the
  -- channel is open exactly then), plus a broadcast fallback for peers we had.
  onPeer cfg.transport \id -> do
    Log.logInfo cfg.logger (fmt @"discovered peer {id} — announcing" { id: show id })
    sendTo cfg.transport id joinMsg
    announce
  announce
  -- …and keep re-announcing until the first job is assigned (raises `stop`) or the
  -- try budget runs out. Each round races a timer against the stop signal
  -- (`AVar.read`, non-consuming so every round sees it once raised).
  launchAff_ $ flip tailRecM 0 \n ->
    if n >= cfg.reannounceMax then pure (Done unit)
    else do
      stopped <- parOneOf [ delay (Milliseconds cfg.reannounceMs) $> false, AVar.read stop $> true ]
      if stopped then pure (Done unit)
      else liftEffect announce $> Loop (n + 1)
