-- | A live terminal view of a block's scan-state, pinned to the bottom
-- | of the terminal with logs scrolling above it. The tree itself is
-- | rendered by the shared pure `renderScanState`; the only JS is
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
import Snarky.Example.Snark.Manager (BlockId)
import Snarky.Example.Snark.Progress (renderScanState)
import Snarky.Example.Snark.ScanState (ScanState)

type ProgressDisplay d =
  { reporter :: BlockId -> ScanState d -> Effect Unit
  , wrapLogger :: Logger -> Logger
  , done :: Effect Unit
  }

-- | Build a display: `reporter` plugs into the manager's `onProgress` hook,
-- | `wrapLogger` makes a logger that coexists with the pinned block, and
-- | `done` persists the final frame (call once at the end of the run).
mkProgressDisplay :: forall d. Effect (ProgressDisplay d)
mkProgressDisplay = do
  current <- Ref.new ""
  let
    repaint = Ref.read current >>= \s -> when (s /= "") (repaintImpl s)
    reporter blockId st = do
      let s = renderScanState blockId st
      Ref.write s current
      repaintImpl s
    wrapLogger (LogAction act) = LogAction \msg -> do
      clearImpl
      act msg
      repaint
  pure { reporter, wrapLogger, done: doneImpl }

foreign import repaintImpl :: String -> Effect Unit
foreign import clearImpl :: Effect Unit
foreign import doneImpl :: Effect Unit
