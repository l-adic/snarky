-- | UI-thread handle to the privacy-split base-prover Web Worker. The
-- | worker (web/private-worker.js) runs `Snarky.Example.WebBase`, which
-- | proves the per-transaction BASE proofs locally (private inputs stay
-- | on-device) and POSTs only proofs + public statements to the server's
-- | /merge endpoint. This module subscribes the UI callbacks to the
-- | worker's `{ type, … }` event protocol and starts the run.
module Snarky.Example.Web.Private.Worker
  ( BaseEvents
  , startBase
  ) where

import Prelude

import Effect (Effect)
import Foreign (Foreign, unsafeFromForeign)
import Web.Worker.MessageEvent (data_)
import Web.Worker.Worker (Worker, onError, onMessage, postMessage)

-- | The UI-side mirror of the WebBase worker's messages (delivered over
-- | postMessage / structured clone, produced by web/private-worker.js).
type BaseEvents =
  { onLeaf :: { total :: Int, slot :: Int } -> Effect Unit
  , onStatus :: String -> Effect Unit
  , onLog :: { severity :: String, text :: String } -> Effect Unit
  , onError :: String -> Effect Unit
  }

-- | Subscribe and kick off the run. Every message is one of the tagged
-- | shapes below, so the payload coercions are safe by the worker protocol.
startBase :: Worker -> BaseEvents -> Effect Unit
startBase worker cbs = do
  worker # onMessage \ev -> do
    let m = unsafeFromForeign (data_ ev) :: { type :: String, value :: Foreign }
    case m.type of
      "leaf" -> cbs.onLeaf (unsafeFromForeign m.value)
      "status" -> cbs.onStatus (unsafeFromForeign m.value)
      "log" -> cbs.onLog (unsafeFromForeign m.value)
      "error" -> cbs.onError (unsafeFromForeign m.value)
      _ -> pure unit
  worker # onError \_ ->
    cbs.onError "[worker] crashed — see the browser console for the underlying error"
  worker # postMessage "run"
