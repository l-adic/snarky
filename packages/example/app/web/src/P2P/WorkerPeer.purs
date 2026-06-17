-- | The browser worker peer: compile the snark circuit once (`buildProver`), then
-- | hand the generic peer loop (`Snarky.Example.P2P.Peer.runStarPeer`) the real
-- | prover and a snark-specific `describeJob`. Everything transport-related —
-- | announce, re-announce, answer `Assign` — lives in the generic loop; this
-- | module is just the snark instantiation (the WorkItem JSON peek + the wasm
-- | prover) plus the one-time compile.
module Snarky.Example.P2P.WorkerPeer
  ( WorkerPeerEvents
  , runWorkerPeer
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Reflectable (reflectType)
import Data.String as String
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Simple.JSON (readJSON)
import Snarky.Example.Log (Logger)
import Snarky.Example.P2P.Peer (runStarPeer)
import Snarky.Example.P2P.Transport (Transport)
import Snarky.Example.Prover (buildProver)
import Snarky.Example.Web.Engine (Depth)
import Snarky.Example.Web.SrsCache (openSrsCache)
import Type.Proxy (Proxy(..))

-- | Render a little-endian field hex (how an amount/digest serializes) as a
-- | decimal string. In JS so it can use BigInt regardless of the value's size.
foreign import leHexToDec :: String -> String

-- | The chain the coordinator's engine compiles against
-- | (`Snarky.Example.Web.Engine` uses `Testnet`). A worker MUST compile the same
-- | circuit or the proofs it returns will not verify under the coordinator's VK.
chainTag :: String
chainTag = "Testnet"

-- | What the worker reports to its own UI: a colog `Logger` for the log stream
-- | (`buildProver`'s SRS/compile logging flows through it too) and an `onPhase`
-- | for the current-status badge.
type WorkerPeerEvents =
  { logger :: Logger
  , onPhase :: String -> Effect Unit
  }

-- | The public statement both job kinds prove: the ledger Merkle-root transition
-- | (`source → target`). Serialized as two little-endian field hex strings.
type StmtPeek = { source :: String, target :: String }

-- | A short fingerprint of a 32-byte field hex (for display only).
shortHex :: String -> String
shortHex h = String.take 8 h <> "…"

-- | `source → target`, both shortened.
transition :: StmtPeek -> String
transition s = shortHex s.source <> " → " <> shortHex s.target

-- | A human description of a work item, peeked from its JSON WITHOUT the SRS — so
-- | it covers exactly the public parts: every job's statement (the ledger
-- | transition it proves) and, for a base job, the transaction itself (the
-- | transfer's amount + recipient). A merge's child proofs stay opaque (decoding
-- | them needs the SRS), so only its merged statement is shown.
describeJob :: String -> String
describeJob work = case readJSON work :: Either _ { tag :: String } of
  Right { tag: "base" } ->
    case
      readJSON work
        :: Either _
             { base ::
                 { statement :: StmtPeek
                 , tx :: { transaction :: { transfer :: { to :: { x :: String }, amount :: String } } }
                 }
             }
      of
      Right { base: b } ->
        let
          t = b.tx.transaction.transfer
        in
          "base · transfer " <> leHexToDec t.amount <> " → " <> shortHex t.to.x
            <> " · ledger "
            <> transition b.statement
      Left _ -> "base"
  Right { tag: "merge" } ->
    case readJSON work :: Either _ { merge :: String } of
      Right { merge } -> case readJSON merge :: Either _ { statement :: StmtPeek } of
        Right { statement } -> "merge · ledger " <> transition statement
        Left _ -> "merge"
      Left _ -> "merge"
  _ -> "job"

-- | Compile the circuit (through this peer's own machine-local SRS cache), then
-- | run the generic peer loop with the real prover.
runWorkerPeer :: Transport -> WorkerPeerEvents -> Effect Unit
runWorkerPeer transport { logger, onPhase } = launchAff_ do
  liftEffect $ onPhase "compiling circuit"
  cache <- openSrsCache logger
  prove <- buildProver cache logger { chain: chainTag, depth: reflectType (Proxy :: Proxy Depth) }
  liftEffect $ runStarPeer
    { transport
    , logger
    , prove
    , describeJob
    , onPhase
    , reannounceMs: 4000.0
    , reannounceMax: 30
    }
