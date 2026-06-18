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
import Fmt (fmt)
import JS.BigInt as BigInt
import Mina.ChainId (ChainId)
import Simple.JSON (readJSON)
import Snarky.Curves.Class (fromHexLe, toBigInt)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Log (Logger)
import Snarky.Example.P2P.Peer (PeerPhase(Compiling), runStarPeer)
import Snarky.Example.P2P.Transport (Transport)
import Snarky.Example.P2P.Types (Payload(..))
import Snarky.Example.Prover (buildProver)
import Snarky.Example.Web.Engine (Depth)
import Snarky.Example.Web.SrsCache (openSrsCache)
import Type.Proxy (Proxy(..))

-- | Render a work-item field (a little-endian hex, how the WorkItem's
-- | `Vesta.ScalarField` values serialize) as a decimal string.
fieldToDec :: String -> String
fieldToDec hex = BigInt.toString (toBigInt (fromHexLe hex :: Vesta.ScalarField))

-- | What the worker reports to its own UI: a colog `Logger` for the log stream
-- | (`buildProver`'s SRS/compile logging flows through it too) and an `onPhase`
-- | for the current-status badge.
type WorkerPeerEvents =
  { logger :: Logger
  , onPhase :: PeerPhase -> Effect Unit
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

-- | A summary of a work item, peeked from its JSON WITHOUT the SRS — so it covers
-- | exactly the public parts: every job's statement (the ledger transition it
-- | proves) and, for a base job, the transaction itself (transfer amount +
-- | recipient). A merge's child proofs stay opaque (decoding them needs the SRS),
-- | so this is a deliberately shallow projection, NOT the full `WorkItem`.
-- | `Other` carries the raw tag for jobs we can't peek into.
data JobSummary
  = BaseJob { transition :: StmtPeek, amount :: String, to :: String }
  | MergeJob StmtPeek
  | OtherJob String

-- | Decode a job's public summary from its encoded payload (lossy by design).
jobSummary :: Payload -> JobSummary
jobSummary (Payload work) = case readJSON work :: Either _ { tag :: String } of
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
        BaseJob { transition: b.statement, amount: b.tx.transaction.transfer.amount, to: b.tx.transaction.transfer.to.x }
      Left _ -> OtherJob "base"
  Right { tag: "merge" } ->
    case readJSON work :: Either _ { merge :: String } of
      Right { merge } -> case readJSON merge :: Either _ { statement :: StmtPeek } of
        Right { statement } -> MergeJob statement
        Left _ -> OtherJob "merge"
      Left _ -> OtherJob "merge"
  _ -> OtherJob "job"

-- | A one-line human label for a job (UI / logs).
describeJob :: Payload -> String
describeJob p = case jobSummary p of
  BaseJob b -> fmt @"base · transfer {amount} → {to} · ledger {transition}"
    { amount: fieldToDec b.amount, to: shortHex b.to, transition: transition b.transition }
  MergeJob s -> fmt @"merge · ledger {transition}" { transition: transition s }
  OtherJob tag -> tag

-- | Compile the circuit (through this peer's own machine-local SRS cache), then
-- | run the generic peer loop with the real prover.
runWorkerPeer :: ChainId -> Transport -> WorkerPeerEvents -> Effect Unit
runWorkerPeer chainId transport { logger, onPhase } = launchAff_ do
  liftEffect $ onPhase Compiling
  cache <- openSrsCache logger
  prove <- buildProver cache logger { chain: show chainId, depth: reflectType (Proxy :: Proxy Depth) }
  liftEffect $ runStarPeer
    { transport
    , logger
    , prove
    , describeJob
    , onPhase
    , reannounceMs: 4000.0
    , reannounceMax: 30
    }
