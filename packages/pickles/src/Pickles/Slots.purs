-- | The type-level slot descriptor, shared by the step- and wrap-side
-- | per-slot carriers: what a parent rule needs to know about each of
-- | its prev slots at the type level.
module Pickles.Slots
  ( Slot
  ) where

-- | One slot: the prev's `max_proofs_verified` — for a side-loaded
-- | slot, the compile-time upper bound on the side-loaded tag's mpv —
-- | and the prev's statement type. `n` doubles as the slot's width for
-- | the wrap circuit, which `Pickles.Prove.Compile.SlotWidths` reads
-- | back rather than having the application restate it.
-- |
-- | Pure phantom; no value-level inhabitants. A rule's prevs spec is
-- | the tuple chain `Slot n₁ s₁ /\ Slot n₂ s₂ /\ … /\ Unit`, `Unit`
-- | terminating it (the empty-prev list).
-- |
-- | No chunk count belongs here: a step circuit verifies the prev's
-- | wrap proof against the prev's wrap VK and never sees its step
-- | proof, so its allocations are sized by
-- | `Pickles.Types.WrapVkChunks`. The counts that do vary are
-- | compile-wide (`stepChunks`) or runtime data
-- | (`Pickles.Prove.Slot.slotNumChunks`), never per-slot type-level
-- | data.
foreign import data Slot :: Int -> Type -> Type
