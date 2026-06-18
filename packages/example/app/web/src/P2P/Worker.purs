-- | The prover worker's PureScript entry (`main :: Effect Unit`). The worker JS
-- | (`p2p-worker.js`) must boot the wasm backend and build the bridged transport
-- | in JS *before* importing this module (importing it pulls in the snarky-kimchi
-- | FFI, which `require`s kimchi at load — so it has to come after
-- | `initThreadPool`). Once booted, the JS does only `main()`.
-- |
-- | `main` reads its role and the (already-connected) bridged transport from the
-- | JS boot via `foreign import`s, builds the engine callbacks as
-- | `postToMain`-posting closures (so JS isn't handed PureScript-shaped
-- | callbacks), and runs the coordinator or worker-peer.
module Snarky.Example.Web.P2P.Worker
  ( main
  ) where

import Prelude

import Effect (Effect)
import Foreign (Foreign, unsafeToForeign)
import Mina.ChainId (ChainId(..))
import Snarky.Example.P2P.Backend (runCoordinator)
import Snarky.Example.P2P.Transport (Transport)
import Snarky.Example.P2P.WorkerPeer (runWorkerPeer)
import Snarky.Example.Web.P2P.WorkerLog (mkPostLogger)

-- | The role, chain, and the ready bridged transport, stashed by p2p-worker.js
-- | after boot (the chain flows from the main-thread app's config).
foreign import bootRole :: Effect String
foreign import bootChain :: Effect String
foreign import bootTransport :: Effect Transport

-- | Inverse of `show :: ChainId -> String` (anything but mainnet is testnet).
chainIdFromTag :: String -> ChainId
chainIdFromTag = case _ of
  "Mainnet" -> Mainnet
  _ -> Testnet

-- | Post a tagged event to the main thread (`self.postMessage({ tag, value })`);
-- | the main-thread app (`P2P.Main`) folds it into UI state.
foreign import postToMain :: String -> Foreign -> Effect Unit

main :: Effect Unit
main = do
  role <- bootRole
  chainId <- chainIdFromTag <$> bootChain
  transport <- bootTransport
  case role of
    "coordinator" ->
      runCoordinator chainId transport
        (\peers -> postToMain "peers" (unsafeToForeign peers))
        { onLog: \v -> postToMain "log" (unsafeToForeign v)
        , onPhase: \v -> postToMain "phase" (unsafeToForeign v)
        , onTxs: \v -> postToMain "txs" (unsafeToForeign v)
        , onScan: \v -> postToMain "scan" (unsafeToForeign v)
        , onVerified: \v -> postToMain "verified" (unsafeToForeign v)
        }
    _ -> do
      logger <- mkPostLogger
      runWorkerPeer chainId transport
        { logger
        , onPhase: \v -> postToMain "phase" (unsafeToForeign v)
        }
