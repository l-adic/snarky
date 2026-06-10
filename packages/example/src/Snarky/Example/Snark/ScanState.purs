-- | The per-block scan state: a perfect binary merge tree over a block's base
-- | jobs, plus the one event-driven operation the scheduler turns on — record a
-- | completed slot, and learn what new work it unlocked (and whether the root is
-- | done). This is the "work collection" the main node owns; it is pure (no Aff,
-- | no channels) so it can be reasoned about and tested in isolation.
-- |
-- | Because a block has a power-of-two number of leaves, the tree is *perfect*
-- | and needs no representation: it is implicit in heap indexing. With `n`
-- | leaves the nodes are slots `1 .. 2n-1` — root at `1`, internal nodes
-- | `1 .. n-1`, leaves `n .. 2n-1` (leaf `j` at `n+j`) — and `parent i = i/2`,
-- | `children i = (2i, 2i+1)`. Completing a slot unlocks its parent iff the
-- | sibling is already done, so there are no layer barriers.
-- |
-- | PRECONDITION: `buildScanState` is given a power-of-two number of jobs (the
-- | caller pads the block to capacity).
module Snarky.Example.Snark.ScanState
  ( SlotId
  , ScanState
  , buildScanState
  , initialWork
  , record
  ) where

import Prelude

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Snark.Work (BaseJob, Proof, WorkItem(..))
import Snarky.Example.Transaction (Statement(..))

-- | A heap index into the perfect tree (root = 1).
type SlotId = Int

-- | The block's leaves (leaf `j` lives at slot `n+j`) and the proofs filled so
-- | far. The tree itself is implicit in the heap indexing.
type ScanState d =
  { leaves :: Array (BaseJob d)
  , proofs :: Map SlotId Proof
  }

-- | Nothing to build — the structure is the heap indexing.
buildScanState :: forall d. Array (BaseJob d) -> ScanState d
buildScanState leaves = { leaves, proofs: Map.empty }

-- | The initially-dispatchable work: every leaf's base job, at slot `n+j`.
initialWork :: forall d. ScanState d -> Array (Tuple SlotId (WorkItem d))
initialWork st = Array.mapWithIndex (\j job -> Tuple (n + j) (Base job)) st.leaves
  where
  n = Array.length st.leaves

-- | Record a slot's proof; unlock its parent merge iff the sibling is already
-- | proved, and report `done` when the root (slot 1) fills.
record
  :: forall d
   . SlotId
  -> Proof
  -> ScanState d
  -> { state :: ScanState d, unlocked :: Array (Tuple SlotId (WorkItem d)), done :: Maybe Proof }
record slot proof st =
  let
    st' = st { proofs = Map.insert slot proof st.proofs }
  in
    if slot == root then
      { state: st', unlocked: [], done: Just proof }
    else
      { state: st'
      , unlocked: case unlockParent slot st' of
          Just u -> [ u ]
          Nothing -> []
      , done: Nothing
      }
  where
  root = 1

-- | The parent merge of `slot`, if both its children are now proved.
unlockParent :: forall d. SlotId -> ScanState d -> Maybe (Tuple SlotId (WorkItem d))
unlockParent slot st = do
  let parent = slot / 2
  proof1 <- Map.lookup (2 * parent) st.proofs
  proof2 <- Map.lookup (2 * parent + 1) st.proofs
  statement <- statementOf st parent
  pure (Tuple parent (Merge { proof1, proof2, statement }))

-- | A node's statement is structural: `source` of its leftmost leaf, `target`
-- | of its rightmost — reached by descending the heap indices into the leaves.
statementOf :: forall d. ScanState d -> SlotId -> Maybe (Statement Vesta.ScalarField)
statementOf st slot = do
  Statement left <- leafStatement (descend leftChild slot)
  Statement right <- leafStatement (descend rightChild slot)
  pure (Statement { source: left.source, target: right.target })
  where
  n = Array.length st.leaves
  leftChild i = 2 * i
  rightChild i = 2 * i + 1
  descend child i = if i >= n then i else descend child (child i)
  leafStatement heapIdx = _.statement <$> Array.index st.leaves (heapIdx - n)
