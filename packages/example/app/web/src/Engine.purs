-- | The browser entry to the engine: the thin setup shell around the pure
-- | `Snarky.Example.Engine` pipeline. It opens the same-origin SRS cache and
-- | compiles the program (the "setup" phase), then runs the one-block engine
-- | (`runEngine`) over an injected `SnarkBackend`. Runs inside a Web Worker over
-- | the wasm kimchi backend (proving is synchronous, so it must never live on the
-- | UI thread). Everything below the cache + compile is browser-free and lives in
-- | the lib (`Snarky.Example.Engine`), so it is Node-testable.
module Snarky.Example.Web.Engine
  ( Depth
  , runWith
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds)
import Effect (Effect)
import Effect.Aff (runAff_)
import Effect.Class (liftEffect)
import Effect.Exception (message)
import Mina.ChainId (ChainId)
import Snarky.Example.Engine (EngineCallbacks, engineLogger, engineOnProgress, runEngine)
import Snarky.Example.Simulation (mkSimulation)
import Snarky.Example.Snark.Pool (PoolSize)
import Snarky.Example.Snark.Worker (SnarkBackend)
import Snarky.Example.Web.SrsCache (openSrsCache)

-- | Ledger tree depth, matching the terminal entry.
type Depth = 4

-- | The engine parameterized by its snark backend (plus pool size / job timeout):
-- | the P2P coordinator drives the one-block pipeline over a `Dynamic` pool whose
-- | first worker is its own in-process prover and the rest are remote peers
-- | (`Snarky.Example.P2P.Backend.p2pSnarkBackend`). This is the setup shell —
-- | build the SRS cache + compile (the "setup" phase), then `runEngine`.
runWith :: ChainId -> SnarkBackend Depth -> PoolSize -> Milliseconds -> EngineCallbacks -> Effect Unit
runWith chainId backend poolSize jobTimeout cb = runAff_ onDone do
  let logger = engineLogger cb
  liftEffect $ cb.onPhase "setup"
  -- The shared same-origin SRS cache (with hit/miss logging): the engine warms it;
  -- the nested self-prover reads it instead of re-running the FFTs.
  cache <- openSrsCache logger
  sim <- mkSimulation @Depth
    { chainId
    , numAccounts: 10
    , logger
    , onProgress: Just (engineOnProgress cb)
    , poolSize
    , jobTimeout
    , backend
    , cache
    }
  runEngine sim cb
  where
  -- Surface an otherwise-swallowed Aff failure (e.g. an SRS cache error) to the UI.
  onDone = case _ of
    Left err -> cb.onLog { severity: "error", text: "[engine] FAILED: " <> message err }
    Right _ -> pure unit
