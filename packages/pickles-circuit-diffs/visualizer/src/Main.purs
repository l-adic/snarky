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
import Effect.Ref as Ref
import Pickles.CircuitDiffs.Types (CircuitComparison)
import React.Basic (JSX)
import React.Basic.DOM as R
import React.Basic.DOM.Client (createRoot, renderRoot)
import React.Basic.Events (handler_)
import React.Basic.Hooks (Component, component, useEffect, useState, (/\))
import React.Basic.Hooks as React
import Simple.JSON (readJSON)
import Styles (AppStyles, appStyles_)
import Web.DOM.NonElementParentNode (getElementById)
import Web.Event.Event (EventType(..))
import Web.Event.EventTarget (addEventListener, eventListener, removeEventListener)
import Web.HTML (window)
import Web.HTML.HTMLDocument (toNonElementParentNode)
import Web.HTML.Location as Location
import Web.HTML.Window (document, location, toEventTarget)
import Web.UIEvent.MouseEvent as MouseEvent

css :: AppStyles
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

minSidebarWidth :: Int
minSidebarWidth = 120

maxSidebarWidth :: Int
maxSidebarWidth = 800

defaultSidebarWidth :: Int
defaultSidebarWidth = 220

clampWidth :: Int -> Int
clampWidth w = max minSidebarWidth (min maxSidebarWidth w)

-- Attach window-level mousemove/mouseup listeners that drive the sidebar
-- resize. The mouseup handler unregisters both listeners (and itself, via a
-- Ref since the listener closure has to reference its own `EventListener`).
startResize :: (Int -> Effect Unit) -> Effect Unit -> Effect Unit
startResize onMove onEnd = do
  target <- toEventTarget <$> window
  let mousemove = EventType "mousemove"
  let mouseup = EventType "mouseup"

  moveListener <- eventListener \ev ->
    case MouseEvent.fromEvent ev of
      Nothing -> pure unit
      Just me -> onMove (MouseEvent.clientX me)

  upRef <- Ref.new Nothing
  upListener <- eventListener \_ -> do
    removeEventListener mousemove moveListener false target
    Ref.read upRef >>= case _ of
      Just l -> removeEventListener mouseup l false target
      Nothing -> pure unit
    onEnd
  Ref.write (Just upListener) upRef

  addEventListener mousemove moveListener false target
  addEventListener mouseup upListener false target

-- Read the current URL hash, returning the part after "#" if non-empty.
readHashSelection :: Effect (Maybe String)
readHashSelection = do
  loc <- location =<< window
  h <- Location.hash loc
  pure case String.stripPrefix (String.Pattern "#") h of
    Just n | not (String.null n) -> Just n
    _ -> Nothing

mkApp :: ({ comparison :: CircuitComparison } -> JSX) -> Component Unit
mkApp circuitDiffTable = component "App" \_ -> React.do
  manifest /\ setManifest <- useState ([] :: Array ManifestEntry)
  selected /\ setSelected <- useState (Nothing :: Maybe String)
  comparison /\ setComparison <- useState (Nothing :: Maybe CircuitComparison)
  loading /\ setLoading <- useState false
  error /\ setError <- useState (Nothing :: Maybe String)
  sidebarWidth /\ setSidebarWidth <- useState defaultSidebarWidth
  resizing /\ setResizing <- useState false

  -- Load manifest on mount
  useEffect unit do
    launchAff_ do
      result <- AX.get ResponseFormat.string "results/manifest.jsonl"
      liftEffect case result of
        Left err -> setError (const (Just ("Failed to load manifest: " <> AX.printError err)))
        Right response -> setManifest (const (parseManifest response.body))
    pure (pure unit)

  -- Sync `selected` with URL hash: pick up the initial hash on mount, then
  -- listen for `hashchange` so back/forward navigation and clicks on the
  -- nav-bar links update the selection without a full reload.
  useEffect unit do
    initial <- readHashSelection
    case initial of
      Just n -> setSelected (const (Just n))
      Nothing -> pure unit
    target <- toEventTarget <$> window
    let hashchange = EventType "hashchange"
    listener <- eventListener \_ -> do
      next <- readHashSelection
      setSelected (const next)
    addEventListener hashchange listener false target
    pure (removeEventListener hashchange listener false target)

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
    matches = Array.sortWith _.name $ Array.filter (\e -> e.status == "match") manifest
    mismatches = Array.sortWith _.name $ Array.filter (\e -> e.status /= "match") manifest

    statusDot :: String -> JSX
    statusDot status =
      R.span
        { className: css.statusDot <> " " <> if status == "match" then css.statusMatch else css.statusMismatch
        }

    navItem :: ManifestEntry -> JSX
    navItem entry =
      R.a
        { className: css.navItem <> if selected == Just entry.name then " " <> css.navItemSelected else ""
        , href: "#" <> entry.name
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
        , style: R.css { width: show sidebarWidth <> "px" }
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

    resizer :: JSX
    resizer =
      R.div
        { className: css.resizer <> if resizing then " " <> css.resizerActive else ""
        , onMouseDown: handler_ do
            setResizing (const true)
            startResize
              (\x -> setSidebarWidth (const (clampWidth x)))
              (setResizing (const false))
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
    , style: R.css { userSelect: if resizing then "none" else "auto" }
    , children: [ sidebar, resizer, content ]
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
