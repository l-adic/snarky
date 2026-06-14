-- | The "log" panel: the simulation's colog stream (newest first),
-- | colored by severity. `LogEntry` is the shape the engine's `onLog`
-- | callback delivers.
module Snarky.Example.Web.Component.Log
  ( LogEntry
  , logPanel
  ) where

import Prelude

import Data.Array as Array
import React.Basic (JSX)
import React.Basic.DOM as R
import Snarky.Example.Web.Component.Panel (emptyHint, panel)

type LogEntry = { severity :: String, text :: String }

logPanel :: Array LogEntry -> JSX
logPanel logs =
  panel "log" $
    if Array.null logs then [ emptyHint ]
    else [ R.div { className: "log-scroll", children: map logLine logs } ]

logLine :: LogEntry -> JSX
logLine l = R.div
  { className: "log-line"
  , children:
      [ R.span { className: "log-sev " <> l.severity, children: [ R.text ("[" <> l.severity <> "]") ] }
      , R.span { className: "log-text", children: [ R.text l.text ] }
      ]
  }
