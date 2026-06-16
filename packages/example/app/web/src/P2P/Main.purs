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
-- | This module is the entry (`main :: Effect Unit`) — `p2p-main.js` only does
-- | `main()`. The irreducibly-JS dependencies are `foreign import`s (their JS in
-- | `Main.js`, signatures dictated here):
-- |   * `spawnWorker` — construct the prover worker (`new Worker(new URL(...))`,
-- |     which must resolve relative to `app/web/`, so it lives in `p2p-spawn.js`).
-- |   * `connectTransport` — build the real transport on the main thread (async
-- |     for Trystero) and hand it back via the continuation.
-- |   * `readHashParam` — read a URL-hash parameter (browser API).
-- | The transport factory / WebRTC modules stay internal JS; the FFI calls them.
module Snarky.Example.Web.P2P.Main
  ( main
  ) where

import Prelude

import Data.Array as Array
import Data.Either (either)
import Data.Foldable (for_)
import Data.Int as Int
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Nullable (Nullable, toMaybe, toNullable)
import Data.String as String
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Uncurried (EffectFn1, EffectFn3, mkEffectFn1, runEffectFn3)
import Foreign (Foreign, unsafeFromForeign, unsafeToForeign)
import React.Basic (JSX)
import React.Basic.DOM as R
import React.Basic.DOM.Client (createRoot, renderRoot)
import React.Basic.DOM.Events (targetValue)
import React.Basic.Events (handler, handler_)
import React.Basic.Hooks (Component, component, useEffectOnce, useState, useState')
import React.Basic.Hooks as React
import Routing (match)
import Routing.Hash (getHash)
import Routing.Match (params)
import Snarky.Example.P2P.Backend (PeerView)
import Snarky.Example.P2P.Protocol (Msg(Leave), encodeMsg)
import Snarky.Example.P2P.Transport (Transport)
import Snarky.Example.P2P.Transport as T
import Snarky.Example.Web.Component.Log (LogEntry, logPanel)
import Snarky.Example.Web.Component.Panel (emptyHint, panel)
import Snarky.Example.Web.Component.ScanState (scanStatePanel)
import Snarky.Example.Web.Engine (ScanView)
import Web.DOM.NonElementParentNode (getElementById)
import Web.HTML (window)
import Web.HTML.HTMLDocument (toNonElementParentNode)
import Web.HTML.Window (document)
import Web.Worker.MessageEvent (data_)
import Web.Worker.Worker (Worker)
import Web.Worker.Worker as WW

foreign import spawnWorker :: Effect Worker
foreign import connectTransport :: EffectFn3 String String (EffectFn1 Transport Unit) Unit
foreign import setWindowProp :: String -> Foreign -> Effect Unit

-- | Run an action when the page is being unloaded (the `pagehide` event).
foreign import onPageHide :: Effect Unit -> Effect Unit

-- | Boot options read from the URL hash: the initial channel + transport, an
-- | auto-start role (headless harness), and an optional rayon-thread override.
type Opts =
  { channel :: String
  , transport :: String
  , autoRole :: Maybe String
  , threads :: Maybe Int
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

phaseLabel :: String -> String
phaseLabel = case _ of
  "idle" -> "idle"
  "setup" -> "building SRS + compiling circuit"
  "block" -> "generating block"
  "proving" -> "proving (base + merge)"
  p -> p

-- | The coordinator's pool, one row per connected worker peer: a short id, what
-- | it is doing now, and how many jobs it has completed.
peerTable :: Array PeerView -> JSX
peerTable peers =
  panel ("peers (" <> show (Array.length peers) <> ")") $
    if Array.null peers then [ emptyHint ]
    else
      [ R.table
          { className: "peer-table"
          , children:
              [ R.thead { children: [ R.tr { children: [ th "peer", th "status", th "done" ] } ] }
              , R.tbody { children: map row peers }
              ]
          }
      ]
  where
  th t = R.th { children: [ R.text t ] }
  row p = R.tr
    { children:
        [ R.td { children: [ R.text (String.take 8 p.id) ] }
        , R.td
            { className: if String.take 7 p.status == "proving" then "peer-busy" else "peer-idle"
            , children: [ R.text p.status ]
            }
        , R.td { children: [ R.text (show p.completed) ] }
        ]
    }

mkApp :: Opts -> Component Unit
mkApp opts = component "P2PApp" \_ -> React.do
  logs /\ setLogs <- useState ([] :: Array LogEntry)
  scan /\ setScan <- useState' (Nothing :: Maybe ScanView)
  phase /\ setPhase <- useState' "idle"
  role /\ setRole <- useState' ""
  started /\ setStarted <- useState' false
  channel /\ setChannel <- useState' opts.channel
  peers /\ setPeers <- useState' ([] :: Array PeerView)

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
          Just "peers" -> do
            setPeers (unsafeFromForeign m.value)
            setWindowProp "__p2pPeers" m.value
          _ -> pure unit

    -- Once the transport is up: spawn the worker, wire the relay both ways
    -- (transport → worker, worker → transport/UI), hand it our id, and start.
    afterConnect r transport = do
      worker <- spawnWorker
      WW.onMessage (handleWorkerMsg transport) worker
      WW.onError (\_ -> pushLog { severity: "error", text: "[worker] crashed — see the browser console" }) worker
      T.onMessage transport \from raw -> WW.postMessage { "_t": "msg", from, raw } worker
      T.onPeer transport \id -> WW.postMessage { "_t": "peer", id } worker
      WW.postMessage { "_t": "myId", id: T.myId transport } worker
      WW.postMessage { type: "start", role: r, threads: toNullable opts.threads } worker
      -- A worker that closes its tab announces it, so the coordinator drops it
      -- and reassigns its in-flight job at once (rather than waiting the timeout).
      when (r == "peer")
        $ onPageHide
        $ T.broadcast transport (encodeMsg (Leave { peerId: T.myId transport }))

    begin r = do
      setStarted true
      setRole r
      setPhaseH "connecting…"
      runEffectFn3 connectTransport opts.transport channel (mkEffectFn1 (afterConnect r))

  useEffectOnce do
    for_ opts.autoRole begin
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
                , R.div
                    { className: "actions"
                    , children:
                        [ R.button
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
                ]
            }
        , R.div
            { className: "grid"
            , children:
                [ R.div
                    { className: "col"
                    , children:
                        -- The peer table is the coordinator's view of its pool;
                        -- a worker has no pool, so it shows only the scan tree.
                        (if role == "coordinator" then [ peerTable peers ] else [])
                          <> [ scanStatePanel scan ]
                    }
                , logPanel logs
                ]
            }
        , R.p
            { className: "footnote"
            , children:
                [ R.text
                    "On one machine click Start experiment (the coordinator: generates a block, farms every base and merge proof to the workers, verifies the root); on the others click Join as worker. The coordinator's pool is dynamic — it starts immediately and uses whatever workers join the same channel."
                ]
            }
        ]
    }

-- | Read the boot options from the URL-hash query params (`#k=v&k=v`) via
-- | `routing`. The hash carries no path, so it is parsed as a query (the parser
-- | exposes query params only after a `?`, hence the prefix); a hash with no
-- | params yields the defaults.
readOpts :: Effect Opts
readOpts = do
  hash <- getHash
  let
    m :: Map String String
    m = either (const Map.empty) identity (match params ("?" <> hash))
    look k = Map.lookup k m
    -- Auto-start (headless harness / launchers): an explicit role, or `auto`
    -- (defaulting to coordinator).
    autoRole = case look "role" of
      Just "peer" -> Just "peer"
      Just _ -> Just "coordinator"
      Nothing -> if isJust (look "auto") then Just "coordinator" else Nothing
  pure
    { channel: fromMaybe "snarky-p2p" (look "session")
    , transport: fromMaybe "trystero" (look "t")
    , autoRole
    , threads: look "threads" >>= Int.fromString
    }

-- | Entry point — `p2p-main.js` is just `main()`. Reads the URL-hash options and
-- | mounts the app; the JS-only dependencies are the `foreign import`s above.
main :: Effect Unit
main = do
  opts <- readOpts
  doc <- document =<< window
  mRoot <- getElementById "app" (toNonElementParentNode doc)
  case mRoot of
    Nothing -> throw "no #app element"
    Just el -> do
      app <- mkApp opts
      root <- createRoot el
      renderRoot root (app unit)
