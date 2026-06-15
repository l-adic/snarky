-- | A live terminal view pinned to the bottom of the terminal with logs
-- | scrolling above it. `paint` takes an already-rendered frame (the caller
-- | draws it — `renderScanState` for a live state, `renderScanView` for a
-- | serialized one), so this is agnostic to what's shown; the only JS is
-- | `log-update` (in-place repaint).
-- |
-- | `mkProgressDisplay` also solves the "logs vs sticky block" conflict:
-- | wrap the app `Logger` with `wrapLogger`, and every log line clears
-- | the block, prints above it, and repaints.
module Snarky.Example.Terminal.ProgressDisplay
  ( ProgressDisplay
  , mkProgressDisplay
  ) where

import Prelude

import Colog (LogAction(..))
import Effect (Effect)
import Effect.Ref as Ref
import Snarky.Example.Log (Logger)

type ProgressDisplay =
  { paint :: String -> Effect Unit
  , wrapLogger :: Logger -> Logger
  , done :: Effect Unit
  }

-- | Build a display: `paint` repaints the pinned frame (feed it a rendered
-- | tree), `wrapLogger` makes a logger that coexists with that frame, and
-- | `done` persists the final frame (call once at the end of the run).
mkProgressDisplay :: Effect ProgressDisplay
mkProgressDisplay = do
  current <- Ref.new ""
  let
    repaint = Ref.read current >>= \s -> when (s /= "") (repaintImpl s)
    paint s = do
      Ref.write s current
      repaintImpl s
    wrapLogger (LogAction act) = LogAction \msg -> do
      clearImpl
      act msg
      repaint
  pure { paint, wrapLogger, done: doneImpl }

foreign import repaintImpl :: String -> Effect Unit
foreign import clearImpl :: Effect Unit
foreign import doneImpl :: Effect Unit
