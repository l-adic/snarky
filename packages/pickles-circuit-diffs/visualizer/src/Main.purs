module Main where

import Prelude

import Affjax.ResponseFormat as ResponseFormat
import Affjax.Web as AX
import CircuitDiffTable (mkCircuitDiffTable)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Pickles.CircuitDiffs.Types (CircuitComparison)
import React.Basic (JSX)
import React.Basic.DOM as R
import React.Basic.DOM.Client (createRoot, renderRoot)
import React.Basic.Events (handler_)
import React.Basic.Hooks (Component, component, useEffect, useState, (/\))
import React.Basic.Hooks as React
import Simple.JSON (readJSON)
import Styles (appStyles_)
import Web.DOM.NonElementParentNode (getElementById)
import Web.HTML (window)
import Web.HTML.HTMLDocument (toNonElementParentNode)
import Web.HTML.Window (document)

css :: _
css = appStyles_

type ManifestEntry = { name :: String, status :: String }

parseManifest :: String -> Array ManifestEntry
parseManifest input =
  let
    lines = Array.filter (not <<< String.null) $ String.split (String.Pattern "\n") input

    parseLine :: String -> Maybe ManifestEntry
    parseLine line = case readJSON line of
      Right (e :: ManifestEntry) -> Just e
      Left _ -> Nothing
  in
    Array.mapMaybe parseLine lines

mkApp :: ({ comparison :: CircuitComparison } -> JSX) -> Component Unit
mkApp circuitDiffTable = component "App" \_ -> React.do
  manifest /\ setManifest <- useState ([] :: Array ManifestEntry)
  selected /\ setSelected <- useState (Nothing :: Maybe String)
  comparison /\ setComparison <- useState (Nothing :: Maybe CircuitComparison)
  loading /\ setLoading <- useState false
  error /\ setError <- useState (Nothing :: Maybe String)

  -- Load manifest on mount
  useEffect unit do
    launchAff_ do
      result <- AX.get ResponseFormat.string "results/manifest.jsonl"
      liftEffect case result of
        Left _ -> pure unit
        Right response -> setManifest (const (parseManifest response.body))
    pure (pure unit)

  -- Load circuit when selected changes
  useEffect selected do
    case selected of
      Nothing -> pure unit
      Just name -> launchAff_ do
        liftEffect do
          setLoading (const true)
          setError (const Nothing)
        result <- AX.get ResponseFormat.string ("results/" <> name <> ".json")
        liftEffect case result of
          Left err -> do
            setError (const (Just (AX.printError err)))
            setLoading (const false)
          Right response -> case readJSON response.body of
            Left e -> do
              setError (const (Just (show e)))
              setLoading (const false)
            Right (c :: CircuitComparison) -> do
              setComparison (const (Just c))
              setLoading (const false)
    pure (pure unit)

  let
    matches = Array.filter (\e -> e.status == "match") manifest
    mismatches = Array.filter (\e -> e.status /= "match") manifest

    statusDot :: String -> JSX
    statusDot status =
      R.span
        { className: css.statusDot <> " " <> if status == "match" then css.statusMatch else css.statusMismatch
        }

    navItem :: ManifestEntry -> JSX
    navItem entry =
      R.div
        { className: css.navItem <> if selected == Just entry.name then " " <> css.navItemSelected else ""
        , onClick: handler_ (setSelected (const (Just entry.name)))
        , children:
            [ statusDot entry.status
            , R.text entry.name
            ]
        }

    navSection :: String -> Array ManifestEntry -> JSX
    navSection title entries =
      R.div_
        [ R.div
            { className: css.navSectionHeader
            , children:
                [ R.text (title <> " (" <> show (Array.length entries) <> ")") ]
            }
        , R.div_ (map navItem entries)
        ]

    sidebar :: JSX
    sidebar =
      R.div
        { className: css.sidebar
        , children:
            [ R.div
                { className: css.sidebarTitle
                , children: [ R.text "Circuit Diffs" ]
                }
            , if Array.length mismatches > 0 then navSection "Mismatches" mismatches
              else R.text ""
            , navSection "Matches" matches
            ]
        }

    content :: JSX
    content = case error of
      Just e -> R.div_ [ R.p_ [ R.text ("Error: " <> e) ] ]
      Nothing
        | loading -> R.div { className: css.loading, children: [ R.text "Loading..." ] }
        | otherwise -> case comparison of
            Nothing -> R.div
              { className: css.placeholder
              , children: [ R.text "Select a circuit from the sidebar" ]
              }
            Just c -> R.div
              { className: css.content
              , children:
                  [ R.h2
                      { className: css.contentTitle
                      , children: [ R.text c.name ]
                      }
                  , circuitDiffTable { comparison: c }
                  ]
              }

  pure $ R.div
    { className: css.root
    , children: [ sidebar, content ]
    }

main :: Effect Unit
main = do
  doc <- document =<< window
  root <- getElementById "root" $ toNonElementParentNode doc
  case root of
    Nothing -> pure unit
    Just container -> do
      reactRoot <- createRoot container
      circuitDiffTable <- mkCircuitDiffTable
      app <- mkApp circuitDiffTable
      renderRoot reactRoot (app unit)
