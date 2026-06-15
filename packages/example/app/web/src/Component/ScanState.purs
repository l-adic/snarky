-- | The "scan state" panel: an SVG of the block's work tree, drawn from
-- | the heap indexing (slots 1..2n-1, leaves at n..2n-1), each node
-- | colored by job status. The status logic is the same the terminal
-- | display uses (`Snarky.Example.Snark.Progress.scanStateView`).
-- |
-- | Geometry and fill/stroke are computed here rather than in CSS:
-- | react-basic's SVG exposes no className, and the colors track
-- | runtime job status.
module Snarky.Example.Web.Component.ScanState
  ( scanStatePanel
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import React.Basic (JSX)
import React.Basic.DOM as R
import React.Basic.DOM.SVG as SVG
import Snarky.Example.Snark.Progress (ScanView)
import Snarky.Example.Web.Component.Panel (emptyHint, panel)

scanStatePanel :: Maybe ScanView -> JSX
scanStatePanel scan =
  panel "scan state" case scan of
    Nothing -> [ emptyHint ]
    Just v -> [ tree v ]

-- node fill when not yet complete
nodeBg :: String
nodeBg = "#1e293b"

-- "complete" | "pending" | "locked" -> node fill/stroke color.
statusColor :: String -> String
statusColor = case _ of
  "complete" -> "#22c55e"
  "pending" -> "#f59e0b"
  _ -> "#475569"

depthOf :: Int -> Int
depthOf slot = if slot <= 1 then 0 else 1 + depthOf (slot / 2)

pow2 :: Int -> Int
pow2 k = if k <= 0 then 1 else 2 * pow2 (k - 1)

tree :: ScanView -> JSX
tree { leaves: n, statuses } =
  let
    colW = 130
    rowH = 92
    width = n * colW
    maxDepth = depthOf n
    height = (maxDepth + 1) * rowH + 30

    posOf :: Int -> { x :: Int, y :: Int }
    posOf slot =
      let
        d = depthOf slot
        idx = slot - pow2 d
        levelW = width / pow2 d
      in
        { x: idx * levelW + levelW / 2, y: d * rowH + 46 }

    statusOf slot = fromMaybe "locked" (_.status <$> Array.find (\s -> s.slot == slot) statuses)

    edge slot =
      if slot <= 1 then []
      else
        let
          c = posOf slot
          p = posOf (slot / 2)
        in
          [ SVG.line
              { x1: show p.x
              , y1: show (p.y + 18)
              , x2: show c.x
              , y2: show (c.y - 18)
              , stroke: "#334155"
              , strokeWidth: "1.5"
              }
          ]

    node slot =
      let
        { x, y } = posOf slot
        st = statusOf slot
        isLeaf = slot >= n
        title = if isLeaf then "tx " <> show (slot - n) else "merge"
      in
        [ SVG.circle
            { cx: show x
            , cy: show y
            , r: "16"
            , fill: if st == "complete" then statusColor st else nodeBg
            , stroke: statusColor st
            , strokeWidth: "2.5"
            }
        , SVG.text
            { x: show x
            , y: show (y + 36)
            , textAnchor: "middle"
            , fill: "#94a3b8"
            , fontSize: "11"
            , children: [ R.text (title <> " · s" <> show slot) ]
            }
        ]

    slots = if n == 0 then [] else Array.range 1 (2 * n - 1)
  in
    SVG.svg
      { width: show width
      , height: show height
      , children: Array.concatMap edge slots <> Array.concatMap node slots
      }
