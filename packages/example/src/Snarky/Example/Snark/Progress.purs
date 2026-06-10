-- | A live terminal view of a block's scan-state: the full work tree, with
-- | each job's status derived from the proofs recorded so far —
-- |
-- |   * `✓` complete — the slot's proof is recorded
-- |   * `▦` pending  — submitted but unproven (every leaf starts pending; a
-- |                    merge becomes pending the moment both children complete)
-- |   * `○` locked   — a merge whose work doesn't exist yet (children pending)
-- |
-- | The tree itself is rendered in PureScript (it is just the scan state's
-- | heap indexing, drawn sideways); the only JS is `log-update`, which
-- | repaints the block in place at the bottom of the terminal.
-- |
-- | `mkProgressDisplay` also solves the "logs vs sticky block" conflict: wrap
-- | the app `Logger` with `wrapLogger`, and every log line clears the block,
-- | prints above it, and repaints — scrolling logs above a pinned tree.
module Snarky.Example.Snark.Progress
  ( ProgressDisplay
  , mkProgressDisplay
  , renderScanState
  ) where

import Prelude

import Colog (LogAction(..))
import Data.Array as Array
import Data.Map as Map
import Effect (Effect)
import Effect.Ref as Ref
import Snarky.Example.Log (Logger)
import Snarky.Example.Snark.Manager (BlockId)
import Snarky.Example.Snark.ScanState (ScanState, SlotId)

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

-- | Draw the scan-state tree sideways from the root (slot 1), each node's
-- | status read off the proofs map via the heap indexing.
renderScanState :: forall d. BlockId -> ScanState d -> String
renderScanState blockId st =
  Array.intercalate "\n"
    $ [ "scan state - block " <> show blockId <> "   (✓ complete  ▦ pending  ○ locked)" ]
        <> go "" true 1
  where
  n = Array.length st.leaves

  proven :: SlotId -> Boolean
  proven slot = Map.member slot st.proofs

  status :: SlotId -> String
  status slot
    | proven slot = "✓"
    | slot >= n = "▦"
    | proven (2 * slot) && proven (2 * slot + 1) = "▦"
    | otherwise = "○"

  label :: SlotId -> String
  label slot
    | slot >= n = "base  (slot " <> show slot <> ", tx " <> show (slot - n) <> ")"
    | otherwise = "merge (slot " <> show slot <> ")"

  go :: String -> Boolean -> SlotId -> Array String
  go indent isLast slot =
    let
      branch = if isLast then "└─ " else "├─ "
      childIndent = indent <> (if isLast then "   " else "│  ")
      self = indent <> branch <> status slot <> " " <> label slot
    in
      if slot >= n then [ self ]
      else [ self ] <> go childIndent false (2 * slot) <> go childIndent true (2 * slot + 1)

foreign import repaintImpl :: String -> Effect Unit
foreign import clearImpl :: Effect Unit
foreign import doneImpl :: Effect Unit
