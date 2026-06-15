-- | UI-thread handle to the simulation Web Worker, typed via
-- | purescript-web-workers. The worker itself is constructed in
-- | web/main.js (where vite statically sees `new Worker(new URL(...))`)
-- | and injected into the PS entry point; this module subscribes the
-- | UI callbacks to its {tag, value} event protocol (produced by
-- | web/worker-entry.js) and starts the run.
module Snarky.Example.Web.Worker
  ( EngineEvents
  , startEngine
  ) where

import Prelude

import Effect (Effect)
import Foreign (Foreign, unsafeFromForeign)
import Snarky.Example.Engine (TxView)
import Snarky.Example.Snark.Progress (ScanView)
import Web.Worker.MessageEvent (data_)
import Web.Worker.Worker (Worker, onError, onMessage, postMessage)

-- | The UI-side mirror of `EngineCallbacks` (same payloads, delivered
-- | over postMessage / structured clone).
type EngineEvents =
  { onLog :: { severity :: String, text :: String } -> Effect Unit
  , onPhase :: String -> Effect Unit
  , onTxs :: Array TxView -> Effect Unit
  , onScan :: ScanView -> Effect Unit
  , onVerified :: Boolean -> Effect Unit
  }

-- | Subscribe and kick off the run. The payload coercions are safe by
-- | the worker protocol: every message is one of the tagged shapes
-- | below, produced by worker-entry.js from `EngineCallbacks` calls.
startEngine :: Worker -> EngineEvents -> Effect Unit
startEngine worker cbs = do
  worker # onMessage \ev -> do
    let m = unsafeFromForeign (data_ ev) :: { tag :: String, value :: Foreign }
    case m.tag of
      "log" -> cbs.onLog (unsafeFromForeign m.value)
      "phase" -> cbs.onPhase (unsafeFromForeign m.value)
      "txs" -> cbs.onTxs (unsafeFromForeign m.value)
      "scan" -> cbs.onScan (unsafeFromForeign m.value)
      "verified" -> cbs.onVerified (unsafeFromForeign m.value)
      _ -> pure unit
  worker # onError \_ ->
    cbs.onLog { severity: "error", text: "[worker] crashed — see the browser console for the underlying error" }
  worker # postMessage "start"
