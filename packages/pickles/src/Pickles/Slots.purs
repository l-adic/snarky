-- | The type-level slot descriptor, shared by the step- and wrap-side
-- | per-slot carriers: what a parent rule needs to know about each of
-- | its prev slots at the type level.
module Pickles.Slots
  ( SlotKind
  , Compiled
  , SideLoaded
  , SlotOf
  , Slot
  , SideLoadedSlot
  ) where

-- | Where a slot's verification key comes from, at the type level.
data SlotKind

-- | A key fixed by this compile: the rule itself, or an imported rule.
foreign import data Compiled :: SlotKind

-- | A key supplied at prove time, which the rule binds to its own
-- | statement.
foreign import data SideLoaded :: SlotKind

-- | One slot: its kind, the prev's `max_proofs_verified` — for a
-- | side-loaded slot, the compile-time upper bound on the side-loaded
-- | tag's mpv — and the prev's statement type. `n` doubles as the
-- | slot's width, which `Pickles.Step.Slots.SlotWidths` reads back
-- | rather than having the application restate it.
-- |
-- | Pure phantom; no value-level inhabitants. A rule's prevs spec is
-- | the tuple chain `Slot n₁ s₁ /\ SideLoadedSlot n₂ s₂ /\ … /\ Unit`,
-- | `Unit` terminating it (the empty-prev list).
-- |
-- | No chunk count belongs here: a step circuit verifies the prev's
-- | wrap proof against the prev's wrap VK and never sees its step
-- | proof, so its allocations are sized by
-- | `Pickles.Types.WrapVkChunks`. The counts that do vary are
-- | compile-wide (`stepChunks`) or runtime data
-- | (`Pickles.Prove.Slot.slotNumChunks`), never per-slot type-level
-- | data.
foreign import data SlotOf :: SlotKind -> Int -> Type -> Type

-- | A slot whose key this compile fixes. The rule reads the prev's
-- | statement and nothing else.
type Slot :: Int -> Type -> Type
type Slot n stmt = SlotOf Compiled n stmt

-- | A slot whose key arrives at prove time. The rule reads that key as
-- | well as the statement, and returns it bound to its own statement,
-- | which is what makes the key more than an unconstrained witness.
type SideLoadedSlot :: Int -> Type -> Type
type SideLoadedSlot n stmt = SlotOf SideLoaded n stmt
