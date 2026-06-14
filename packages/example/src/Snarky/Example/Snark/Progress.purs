-- | Pure scan-state views: each slot's status derived from the proofs
-- | recorded so far —
-- |
-- |   * complete — the slot's proof is recorded
-- |   * pending  — submitted but unproven (every leaf starts pending; a
-- |                merge becomes pending the moment both children complete)
-- |   * locked   — a merge whose work doesn't exist yet (children pending)
-- |
-- | Renderers live with their frontends: the terminal's log-update
-- | display in the terminal package (ProgressDisplay), the browser's
-- | SVG tree in the web package. Both consume the functions here, so
-- | every frontend draws from the same status logic.
module Snarky.Example.Snark.Progress
  ( renderScanState
  , scanStateView
  , slotStatus
  ) where

import Prelude

import Data.Array as Array
import Data.Map as Map
import Snarky.Example.Snark.Manager (BlockId)
import Snarky.Example.Snark.ScanState (ScanState, SlotId)

-- | A slot's status, read off the proofs map via the heap indexing —
-- | the single source of truth shared by the terminal renderer and the
-- | browser's structured view.
slotStatus :: forall d. ScanState d -> SlotId -> String
slotStatus st slot
  | Map.member slot st.proofs = "complete"
  | slot >= Array.length st.leaves = "pending"
  | Map.member (2 * slot) st.proofs && Map.member (2 * slot + 1) st.proofs = "pending"
  | otherwise = "locked"

-- | Structured per-slot view of a scan state for non-terminal renderers
-- | (the browser tree). Slots are heap-indexed 1..2n-1 with leaves at
-- | n..2n-1; statuses are "complete" | "pending" | "locked".
scanStateView
  :: forall d
   . ScanState d
  -> { leaves :: Int, statuses :: Array { slot :: Int, status :: String } }
scanStateView st =
  let
    n = Array.length st.leaves
    slots = if n == 0 then [] else Array.range 1 (2 * n - 1)
  in
    { leaves: n
    , statuses: map (\slot -> { slot, status: slotStatus st slot }) slots
    }

-- | Draw the scan-state tree sideways from the root (slot 1), each node's
-- | status read off the proofs map via the heap indexing.
renderScanState :: forall d. BlockId -> ScanState d -> String
renderScanState blockId st =
  Array.intercalate "\n"
    $ [ "scan state - block " <> show blockId <> "   (✓ complete  ▦ pending  ○ locked)" ]
        <> go "" true 1
  where
  n = Array.length st.leaves

  status :: SlotId -> String
  status slot = case slotStatus st slot of
    "complete" -> "✓"
    "pending" -> "▦"
    _ -> "○"

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

