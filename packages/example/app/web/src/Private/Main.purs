-- | Browser frontend for the PRIVACY split: the client proves the
-- | per-transaction BASE proofs locally (private transaction witnesses
-- | never leave the device), then ships only the proofs + public ledger
-- | statements to the server's /merge endpoint, which reduces them to a
-- | verified block root. The inverse trust split from the full in-browser
-- | pipeline (`Snarky.Example.Web.Main`): here the server only ever sees
-- | public data.
-- |
-- | The base-prover runs in a Web Worker over the wasm kimchi backend
-- | (web/private-worker.js -> Snarky.Example.WebBase); this module holds
-- | the UI state and renders the same scan-state work tree the full app
-- | uses — leaves (base proofs) fill in as the client proves them; the
-- | internal merge nodes complete when the server returns the verified
-- | root (the merges run server-side, so they land together at the end).
module Snarky.Example.Web.Private.Main
  ( runApp
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Exception (throw)
import React.Basic.DOM as R
import React.Basic.DOM.Client (createRoot, renderRoot)
import React.Basic.Events (handler_)
import React.Basic.Hooks (Component, component, useState, useState')
import React.Basic.Hooks as React
import Snarky.Example.Web.Component.Log (LogEntry, logPanel)
import Snarky.Example.Web.Component.ScanState (scanStatePanel)
import Snarky.Example.Web.Engine (ScanView)
import Snarky.Example.Web.Private.Worker (startBase)
import Web.DOM.NonElementParentNode (getElementById)
import Web.HTML (window)
import Web.HTML.HTMLDocument (toNonElementParentNode)
import Web.HTML.Window (document)
import Web.Worker.Worker (Worker)

-- | Synthesize the scan-state view from the privacy-split progress. Leaves
-- | are heap slots `n .. 2n-1`, proved in order (so `done` proved means the
-- | first `done` leaf slots are complete); internal slots `1 .. n-1` are the
-- | server-side merges, all complete once `serverDone`. Status vocabulary
-- | matches `Snarky.Example.Snark.Progress.slotStatus`.
mkScanView :: Int -> Int -> Boolean -> Maybe ScanView
mkScanView n done serverDone
  | n <= 0 = Nothing
  | otherwise = Just
      { blockId: 0
      , leaves: n
      , statuses: map (\slot -> { slot, status: statusOf slot }) (Array.range 1 (2 * n - 1))
      }
  where
  proved s = s >= n && (s - n) < done
  statusOf slot
    | serverDone = "complete"
    | proved slot = "complete"
    | slot >= n = "pending"
    | proved (2 * slot) && proved (2 * slot + 1) = "pending"
    | otherwise = "locked"

mkApp :: Worker -> Component Unit
mkApp worker = component "PrivateApp" \_ -> React.do
  logs /\ setLogs <- useState ([] :: Array LogEntry)
  status /\ setStatus <- useState' "idle"
  total /\ setTotal <- useState' 0
  done /\ setDone <- useState 0
  serverDone /\ setServerDone <- useState' false
  started /\ setStarted <- useState' false

  let
    start = do
      setStarted true
      setStatus "starting…"
      startBase worker
        { onLeaf: \{ total: t } -> do
            setTotal t
            setDone (_ + 1)
        , onStatus: \s -> do
            setStatus s
            when (String.contains (String.Pattern "verified root") s) (setServerDone true)
        , onLog: \l -> setLogs \ls -> Array.take 400 (Array.cons l ls)
        , onError: \err -> do
            setStatus "failed"
            setLogs \ls -> Array.take 400 (Array.cons { severity: "error", text: err } ls)
        }

  pure $ R.div
    { className: "app"
    , children:
        [ R.div
            { className: "header"
            , children:
                [ R.h1 { className: "title", children: [ R.text "snarky · client base-prover (private inputs)" ] }
                , R.span { className: "phase-badge", children: [ R.text status ] }
                , R.button
                    { className: "run-btn"
                    , disabled: started
                    , onClick: handler_ start
                    , children: [ R.text (if started then "running…" else "prove locally + merge on server") ]
                    }
                ]
            }
        , R.div
            { className: "grid"
            , children:
                [ scanStatePanel (mkScanView total done serverDone)
                , logPanel logs
                ]
            }
        , R.p
            { className: "footnote"
            , children:
                [ R.text
                    "the leaves (base proofs) are computed in this browser over a wasm32-wasip1-threads build of kimchi — the private transaction witnesses never leave the device; only the proofs and public ledger roots are POSTed to the server, which computes the internal merge nodes and returns the verified block root"
                ]
            }
        ]
    }

-- | Entry point. The worker is constructed in web/private.js (where vite
-- | statically sees `new Worker(new URL(...))`) and injected here.
runApp :: Effect Worker -> Effect Unit
runApp mkWorker = do
  worker <- mkWorker
  doc <- document =<< window
  mRoot <- getElementById "app" (toNonElementParentNode doc)
  case mRoot of
    Nothing -> throw "no #app element"
    Just el -> do
      app <- mkApp worker
      root <- createRoot el
      renderRoot root (app unit)
