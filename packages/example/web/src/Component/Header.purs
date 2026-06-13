-- | The app header: title, live phase badge, the verify verdict (once
-- | the run finishes), and the run button. Purely presentational — it
-- | receives the relevant state slice and the run callback from Main.
module Snarky.Example.Web.Component.Header
  ( HeaderProps
  , header
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import React.Basic (JSX)
import React.Basic.DOM as R
import React.Basic.Events (handler_)

type HeaderProps =
  { phase :: String
  , verified :: Maybe Boolean
  , started :: Boolean
  , onRun :: Effect Unit
  }

phaseLabel :: String -> String
phaseLabel = case _ of
  "idle" -> "idle"
  "setup" -> "building SRS + compiling circuits"
  "block" -> "generating block"
  "proving" -> "proving (base + merge)"
  "done" -> "done"
  p -> p

header :: HeaderProps -> JSX
header props = R.div
  { className: "header"
  , children:
      [ R.h1 { className: "title", children: [ R.text "snarky · in-browser block pipeline" ] }
      , phaseBadge
      ]
        <> verdict
        <> [ runButton ]
  }
  where
  phaseBadge = R.span
    { className: "phase-badge" <> (if props.phase == "done" then " done" else "")
    , children: [ R.text (phaseLabel props.phase) ]
    }

  verdict = case props.verified of
    Nothing -> []
    Just ok ->
      [ R.span
          { className: "verdict " <> (if ok then "ok" else "fail")
          , children:
              [ R.text
                  if ok then "✓ root proof verified — block accepted"
                  else "✗ root proof FAILED to verify"
              ]
          }
      ]

  runButton = R.button
    { className: "run-btn"
    , disabled: props.started
    , onClick: handler_ (unless props.started props.onRun)
    , children: [ R.text (if props.started then "running…" else "run simulation") ]
    }
