-- | The browser worker peer: compile the snark circuit once (`buildProver`), then
-- | hand the generic peer loop (`Snarky.Example.P2P.Peer.runStarPeer`) the real
-- | prover and a snark-specific `describeJob`. Everything transport-related —
-- | announce, re-announce, answer `Assign` — lives in the generic loop; this
-- | module is just the snark instantiation (the wasm prover + the job label) plus
-- | the one-time compile.
module Snarky.Example.P2P.WorkerPeer
  ( WorkerPeerEvents
  , runWorkerPeer
  ) where

import Prelude

import Data.Newtype (un)
import Data.Reflectable (reflectType)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Mina.ChainId (ChainId)
import Snarky.Example.Log (Logger)
import Snarky.Example.P2P.Peer (PeerPhase(Compiling), runStarPeer)
import Snarky.Example.P2P.Transport (Transport)
import Snarky.Example.P2P.Types (Payload(..))
import Snarky.Example.Prover (buildProver)
import Snarky.Example.Snark.JobSummary as JobSummary
import Snarky.Example.Web.Engine (Depth)
import Snarky.Example.Web.SrsCache (idbSrsCache)
import Type.Proxy (Proxy(..))

-- | What the worker reports to its own UI: a colog `Logger` for the log stream
-- | (`buildProver`'s SRS/compile logging flows through it too) and an `onPhase`
-- | for the current-status badge.
type WorkerPeerEvents =
  { logger :: Logger
  , onPhase :: PeerPhase -> Effect Unit
  }

-- | Compile the circuit (through this peer's own machine-local SRS cache), then
-- | run the generic peer loop with the real prover. The job label comes from the
-- | pure `Snarky.Example.Snark.JobSummary` (unit-tested in Node).
runWorkerPeer :: ChainId -> Transport -> WorkerPeerEvents -> Effect Unit
runWorkerPeer chainId transport { logger, onPhase } = launchAff_ do
  liftEffect $ onPhase Compiling
  cache <- idbSrsCache logger
  prove <- buildProver cache logger { chain: show chainId, depth: reflectType (Proxy :: Proxy Depth) }
  liftEffect $ runStarPeer
    { transport
    , logger
    , prove
    , describeJob: JobSummary.describeJob <<< un Payload
    , onPhase
    , reannounceMs: 4000.0
    , reannounceMax: 30
    }
