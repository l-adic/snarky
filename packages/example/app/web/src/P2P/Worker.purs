-- | The prover worker's PureScript entry (`main :: Effect Unit`). The worker JS
-- | (`p2p-worker.js`) must boot the wasm backend and build the bridged transport
-- | in JS *before* importing this module (importing it pulls in the snarky-kimchi
-- | FFI, which `require`s kimchi at load — so it has to come after
-- | `initThreadPool`). Once booted, the JS does only `main()`.
-- |
-- | `main` reads its role and the (already-connected) bridged transport from the
-- | JS boot via `foreign import`s, builds the engine callbacks as `WorkerMsg`-
-- | posting closures (`Snarky.Example.P2P.WorkerMsg`, the typed wire protocol the
-- | main thread decodes), and runs the coordinator or worker-peer.
module Snarky.Example.Web.P2P.Worker
  ( main
  ) where

import Prelude

import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Mina.ChainId (chainIdFromTag)
import Snarky.Example.P2P.Backend (runCoordinator)
import Snarky.Example.P2P.Peer (peerPhaseLabel)
import Snarky.Example.P2P.Transport (Transport)
import Snarky.Example.P2P.WorkerMsg (WorkerMsg(..), encodeWorkerMsg)
import Snarky.Example.P2P.WorkerPeer (runWorkerPeer)
import Snarky.Example.Web.P2P.Post (post)
import Snarky.Example.Web.P2P.WorkerLog (mkPostLogger)

-- | The role, chain, and the ready bridged transport, stashed by p2p-worker.js
-- | after boot (the chain flows from the main-thread app's config).
foreign import bootRole :: Effect String
foreign import bootChain :: Effect String
foreign import bootTransport :: Effect Transport

postMsg :: WorkerMsg -> Effect Unit
postMsg = post <<< encodeWorkerMsg

-- | Backstop timeout for an ungraceful peer death (a graceful `Leave` reassigns
-- | at once); 120 s comfortably covers one base/merge proof on a slow wasm worker.
coordinatorJobTimeout :: Milliseconds
coordinatorJobTimeout = Milliseconds 120000.0

main :: Effect Unit
main = do
  role <- bootRole
  chainId <- chainIdFromTag <$> bootChain
  transport <- bootTransport
  case role of
    "coordinator" ->
      runCoordinator chainId coordinatorJobTimeout transport
        (\peers -> postMsg (WPeers peers))
        { onLog: \v -> postMsg (WLog v)
        , onPhase: \v -> postMsg (WPhase v)
        , onTxs: \v -> postMsg (WTxs v)
        , onScan: \v -> postMsg (WScan v)
        , onVerified: \v -> postMsg (WVerified v)
        }
    _ -> do
      logger <- mkPostLogger
      runWorkerPeer chainId transport
        { logger
        , onPhase: \p -> postMsg (WPhase (peerPhaseLabel p))
        }
