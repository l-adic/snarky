-- | The P2P proving UI, in react-basic — the same stack as the single-app
-- | frontend (`Snarky.Example.Web.Main`), reusing its `logPanel` / `scanStatePanel`
-- | components. Minimal controls: a channel name and two buttons —
-- |
-- |   Start experiment   be the coordinator (block producer): generate a block,
-- |                      farm every base + merge job to the workers, verify root
-- |   Join as worker     be a full-core prover answering assignments
-- |
-- | Everything else is implicit: the coordinator's pool is `Dynamic` (no worker
-- | count), and the transport defaults to Trystero (overridable via the URL hash
-- | for the headless tests).
-- |
-- | The irreducibly-JS bits are injected as `Boot` by the thin `p2p-main.js`
-- | entry: `spawnWorker` (vite needs the literal `new Worker(new URL(...))`) and
-- | `connectTransport` (the transport factory modules, async for Trystero). The
-- | rest — the transport↔worker relay and the UI — is here.
module Snarky.Example.Web.P2P.Main
  ( Boot
  , runP2pApp
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Nullable (Nullable, toMaybe)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Uncurried (EffectFn1, EffectFn3, mkEffectFn1, runEffectFn3)
import Foreign (Foreign, unsafeFromForeign, unsafeToForeign)
import React.Basic.DOM as R
import React.Basic.DOM.Client (createRoot, renderRoot)
import React.Basic.DOM.Events (targetValue)
import React.Basic.Events (handler, handler_)
import React.Basic.Hooks (Component, component, useEffectOnce, useState, useState')
import React.Basic.Hooks as React
import Snarky.Example.P2P.Transport (Transport)
import Snarky.Example.P2P.Transport as T
import Snarky.Example.Web.Component.Log (LogEntry, logPanel)
import Snarky.Example.Web.Component.ScanState (scanStatePanel)
import Snarky.Example.Web.Engine (ScanView)
import Web.DOM.NonElementParentNode (getElementById)
import Web.HTML (window)
import Web.HTML.HTMLDocument (toNonElementParentNode)
import Web.HTML.Window (document)
import Web.Worker.MessageEvent (data_)
import Web.Worker.Worker (Worker)
import Web.Worker.Worker as WW

-- | The JS-only dependencies, supplied by `p2p-main.js`.
-- |   * `spawnWorker` — construct the prover worker (`new Worker(new URL(...))`).
-- |   * `connectTransport kind channel cont` — build the real transport on the
-- |     main thread (async for Trystero) and hand it back via `cont`.
-- |   * `channel`/`transport` — initial values (from the URL hash, else defaults).
-- |   * `autoRole` — set by the headless harness to auto-start a role on mount.
-- |   * `threads` — optional rayon-thread override (headless test; shares a CPU).
type Boot =
  { spawnWorker :: Effect Worker
  , connectTransport :: EffectFn3 String String (EffectFn1 Transport Unit) Unit
  , channel :: String
  , transport :: String
  , autoRole :: Nullable String
  , threads :: Nullable Int
  }

-- | A worker → main message: either transport-relay plumbing (`_t`) or a UI event
-- | (`tag`). Decoded structurally (the worker produces exactly these shapes).
type WMsg =
  { "_t" :: Nullable String
  , tag :: Nullable String
  , value :: Foreign
  , msg :: Nullable String
  , peer :: Nullable String
  }

foreign import setWindowProp :: String -> Foreign -> Effect Unit

phaseLabel :: String -> String
phaseLabel = case _ of
  "idle" -> "idle"
  "setup" -> "building SRS + compiling circuit"
  "block" -> "generating block"
  "proving" -> "proving (base + merge)"
  p -> p

mkApp :: Boot -> Component Unit
mkApp boot = component "P2PApp" \_ -> React.do
  logs /\ setLogs <- useState ([] :: Array LogEntry)
  scan /\ setScan <- useState' (Nothing :: Maybe ScanView)
  phase /\ setPhase <- useState' "idle"
  role /\ setRole <- useState' ""
  started /\ setStarted <- useState' false
  channel /\ setChannel <- useState' boot.channel

  let
    pushLog l = setLogs \ls -> Array.take 400 (Array.cons l ls)

    -- phase/verified mirror to `window` so the headless harness can poll them.
    setPhaseH p = do
      setPhase p
      setWindowProp "__p2pPhase" (unsafeToForeign p)
    setVerifiedH ok = do
      pushLog
        { severity: if ok then "info" else "error"
        , text: if ok then "block root proof verified ✓" else "block root proof FAILED verification"
        }
      setPhaseH (if ok then "done" else "failed")
      setWindowProp "__p2pVerified" (unsafeToForeign ok)

    -- Worker → main: relay transport ops back onto the (main-thread) transport,
    -- and fold UI events into state.
    handleWorkerMsg transport ev = do
      let m = unsafeFromForeign (data_ ev) :: WMsg
      case toMaybe m."_t" of
        Just "broadcast" -> for_ (toMaybe m.msg) (T.broadcast transport)
        Just "send" -> case toMaybe m.peer, toMaybe m.msg of
          Just peer, Just msg -> T.sendTo transport peer msg
          _, _ -> pure unit
        _ -> case toMaybe m.tag of
          Just "log" -> pushLog (unsafeFromForeign m.value)
          Just "phase" -> setPhaseH (unsafeFromForeign m.value)
          Just "scan" -> setScan (Just (unsafeFromForeign m.value))
          Just "verified" -> setVerifiedH (unsafeFromForeign m.value)
          _ -> pure unit

    -- Once the transport is up: spawn the worker, wire the relay both ways
    -- (transport → worker, worker → transport/UI), hand it our id, and start.
    afterConnect r transport = do
      worker <- boot.spawnWorker
      WW.onMessage (handleWorkerMsg transport) worker
      WW.onError (\_ -> pushLog { severity: "error", text: "[worker] crashed — see the browser console" }) worker
      T.onMessage transport \from raw -> WW.postMessage { "_t": "msg", from, raw } worker
      T.onPeer transport \id -> WW.postMessage { "_t": "peer", id } worker
      WW.postMessage { "_t": "myId", id: T.myId transport } worker
      WW.postMessage { type: "start", role: r, threads: boot.threads } worker

    begin r = do
      setStarted true
      setRole r
      setPhaseH "connecting…"
      runEffectFn3 boot.connectTransport boot.transport channel (mkEffectFn1 (afterConnect r))

  useEffectOnce do
    for_ (toMaybe boot.autoRole) begin
    pure (pure unit)

  pure $ R.div
    { className: "app"
    , children:
        [ R.div
            { className: "header"
            , children:
                [ R.h1 { className: "title", children: [ R.text "snarky · P2P proving" ] }
                , R.span { className: "phase-badge", children: [ R.text (phaseLabel phase) ] }
                , if role == "" then mempty
                  else R.span { className: "phase-badge", children: [ R.text role ] }
                , R.label
                    { className: "field"
                    , children:
                        [ R.text "channel "
                        , R.input
                            { className: "channel-input"
                            , value: channel
                            , disabled: started
                            , onChange: handler targetValue (\mv -> for_ mv setChannel)
                            }
                        ]
                    }
                , R.button
                    { className: "run-btn"
                    , disabled: started
                    , onClick: handler_ (unless started (begin "coordinator"))
                    , children: [ R.text "Start experiment" ]
                    }
                , R.button
                    { className: "run-btn"
                    , disabled: started
                    , onClick: handler_ (unless started (begin "peer"))
                    , children: [ R.text "Join as worker" ]
                    }
                ]
            }
        , R.div { className: "grid", children: [ scanStatePanel scan, logPanel logs ] }
        , R.p
            { className: "footnote"
            , children:
                [ R.text
                    "On one machine click Start experiment (the coordinator: generates a block, farms every base and merge proof to the workers, verifies the root); on the others click Join as worker. The coordinator's pool is dynamic — it starts immediately and uses whatever workers join the same channel."
                ]
            }
        ]
    }

-- | Entry point: the JS-only factories are constructed in `p2p-main.js` (where
-- | vite sees the worker URL and the transport modules) and injected here.
runP2pApp :: Boot -> Effect Unit
runP2pApp boot = do
  doc <- document =<< window
  mRoot <- getElementById "app" (toNonElementParentNode doc)
  case mRoot of
    Nothing -> throw "no #app element"
    Just el -> do
      app <- mkApp boot
      root <- createRoot el
      renderRoot root (app unit)
