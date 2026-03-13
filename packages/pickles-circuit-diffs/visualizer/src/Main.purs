module Main where

import Prelude

import Affjax.ResponseFormat as ResponseFormat
import Affjax.Web as AX
import CircuitDiffTable (_mkCircuitDiffTable)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Pickles.CircuitDiffs.Types (CircuitComparison)
import React.Basic (element)
import React.Basic.DOM as R
import React.Basic.DOM.Client (createRoot, renderRoot)
import React.Basic.Hooks (Component, component, useEffect, useState, (/\))
import React.Basic.Hooks as React
import Simple.JSON (readJSON)
import Web.DOM.NonElementParentNode (getElementById)
import Web.HTML (window)
import Web.HTML.HTMLDocument (toNonElementParentNode)
import Web.HTML.Window (document)

mkApp :: Component Unit
mkApp = component "App" \_ -> React.do
  comparison /\ setComparison <- useState (Nothing :: Maybe CircuitComparison)
  error /\ setError <- useState (Nothing :: Maybe String)

  useEffect unit do
    launchAff_ do
      result <- AX.get ResponseFormat.string "/results/xhat_step_circuit.json"
      liftEffect case result of
        Left err -> setError (const (Just ("Fetch error: " <> AX.printError err)))
        Right response -> case readJSON response.body of
          Left e -> setError (const (Just ("Parse error: " <> show e)))
          Right (c :: CircuitComparison) -> setComparison (const (Just c))
    pure (pure unit)

  pure case error of
    Just e -> R.div_ [ R.h1_ [ R.text "Error" ], R.p_ [ R.text e ] ]
    Nothing -> case comparison of
      Nothing -> R.div_ [ R.p_ [ R.text "Loading..." ] ]
      Just c -> R.div_
        [ R.h1_ [ R.text c.name ]
        , R.p_ [ R.text ("Status: " <> c.status) ]
        , element _mkCircuitDiffTable { comparison: c }
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
