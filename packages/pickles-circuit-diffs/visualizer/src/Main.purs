module Main where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import React.Basic.DOM as R
import React.Basic.DOM.Client (createRoot, renderRoot)
import React.Basic.Hooks (Component, component)
import Web.DOM.NonElementParentNode (getElementById)
import Web.HTML (window)
import Web.HTML.HTMLDocument (toNonElementParentNode)
import Web.HTML.Window (document)

mkApp :: Component Unit
mkApp = component "App" \_ -> React.do
  pure $ R.div_
    [ R.h1_ [ R.text "Pickles Circuit Diffs" ]
    , R.p_ [ R.text "Visualizer is working." ]
    ]

main :: Effect Unit
main = do
  doc <- document =<< window
  root <- getElementById "root" $ toNonElementParentNode doc
  case root of
    Nothing -> pure unit
    Just container -> do
      reactRoot <- createRoot container
      app <- mkApp
      renderRoot reactRoot (app unit)
