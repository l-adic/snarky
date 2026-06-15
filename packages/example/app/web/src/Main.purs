-- | Browser frontend for the example simulation: the same one-block
-- | pipeline as the terminal TUI, rendered with react-basic. The
-- | simulation runs in a Web Worker over the wasm kimchi backend
-- | (web/worker-entry.js -> Snarky.Example.Engine); this module
-- | holds the UI state, subscribes to the worker's event stream, and
-- | composes the section components —
-- |
-- |   Header        phase badge / verdict / run button
-- |   Transactions  the block's random transfers
-- |   ScanState     the work-tree SVG
-- |   Log           the simulation's colog stream
-- |
-- | Each component is presentational (in Snarky.Example.Web.Component.*);
-- | styling is in web/styles.css.
module Snarky.Example.Web.Main
  ( runApp
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Exception (throw)
import React.Basic.DOM as R
import React.Basic.DOM.Client (createRoot, renderRoot)
import React.Basic.Hooks (Component, component, useState, useState')
import React.Basic.Hooks as React
import Snarky.Example.Engine (TxView)
import Snarky.Example.Snark.Progress (ScanView)
import Snarky.Example.Web.Component.Header (header)
import Snarky.Example.Web.Component.Log (LogEntry, logPanel)
import Snarky.Example.Web.Component.ScanState (scanStatePanel)
import Snarky.Example.Web.Component.Transactions (transactionsPanel)
import Snarky.Example.Web.Worker (startEngine)
import Web.DOM.NonElementParentNode (getElementById)
import Web.HTML (window)
import Web.HTML.HTMLDocument (toNonElementParentNode)
import Web.HTML.Window (document)
import Web.Worker.Worker (Worker)

mkApp :: Worker -> Component Unit
mkApp worker = component "App" \_ -> React.do
  logs /\ setLogs <- useState ([] :: Array LogEntry)
  txs /\ setTxs <- useState' ([] :: Array TxView)
  scan /\ setScan <- useState' (Nothing :: Maybe ScanView)
  phase /\ setPhase <- useState' "idle"
  verified /\ setVerified <- useState' (Nothing :: Maybe Boolean)
  started /\ setStarted <- useState' false
  -- which transaction row is expanded (accordion; one at a time).
  -- `useState` (functional setter) so the toggle reads the live value.
  selectedTx /\ setSelectedTx <- useState (Nothing :: Maybe Int)

  let
    start = do
      setStarted true
      startEngine worker
        { onLog: \l -> setLogs \ls -> Array.take 400 (Array.cons l ls)
        , onPhase: setPhase
        , onTxs: setTxs
        , onScan: setScan <<< Just
        , onVerified: setVerified <<< Just
        }

    -- toggle: clicking the open row closes it
    toggleTx i = setSelectedTx \cur -> if cur == Just i then Nothing else Just i

  pure $ R.div
    { className: "app"
    , children:
        [ header { phase, verified, started, onRun: start }
        , R.div
            { className: "grid"
            , children:
                -- scan state ABOVE transactions: the accordion grows
                -- downward into empty space instead of shoving the tree.
                [ R.div
                    { className: "col"
                    , children:
                        [ scanStatePanel scan
                        , transactionsPanel { txs, selected: selectedTx, onSelect: toggleTx }
                        ]
                    }
                , logPanel logs
                ]
            }
        , R.p
            { className: "footnote"
            , children:
                [ R.text
                    "proving runs in a Web Worker over a wasm32-wasip1-threads build of kimchi — rayon on SharedArrayBuffer-backed web workers; the tree is rendered from the same scan-state code as the terminal display"
                ]
            }
        ]
    }

-- | Entry point. The worker is constructed in web/main.js (where vite
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
