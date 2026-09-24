-- | The spec-indexed carriers that hand a circuit its side-loaded
-- | verification keys: `SideloadedVKsCarrier` at prove time,
-- | `MkUnitVkCarrier` at compile time.
-- |
-- | Both carriers are uniform across slots: whether a slot is
-- | side-loaded follows from its `SlotWrapKey`, which is runtime data,
-- | so no carrier can vary its cell per slot.
module Pickles.Sideload.Advice
  ( class SideloadedVKsCarrier
  , class MkUnitVkCarrier
  ) where

import Prelude

import Data.Tuple.Nested (type (/\))
import Pickles.Field (StepField)
import Pickles.Sideload.Bundle (SlotProveVk)
import Pickles.Sideload.VerificationKey (VerificationKey) as SLVK
import Pickles.Slots (SlotOf)
import Pickles.Types (WrapVkChunks)
import Snarky.Circuit.DSL (F)

-- | The prove-time carrier shape for a spec: `Unit` for `Unit`, and
-- | `SlotProveVk WrapVkChunks /\ restCarrier` for
-- | `Slot n statement /\ rest`. The functional dependency pins the
-- | carrier from the spec alone.
-- |
-- | Every slot gets the same cell — a side-loaded one supplies
-- | `SideLoadedVk` with its bundle, a compiled one `NoSideLoadedVk` —
-- | because which of the two it is depends on the slot's
-- | `SlotWrapKey`, not on its type.
class SideloadedVKsCarrier :: Type -> Type -> Constraint
class SideloadedVKsCarrier spec carrier | spec -> carrier

instance SideloadedVKsCarrier Unit Unit

instance
  SideloadedVKsCarrier rest restCarrier =>
  SideloadedVKsCarrier
    (SlotOf k n statement /\ rest)
    (SlotProveVk WrapVkChunks /\ restCarrier)

-- | The compile-time carrier shape for a spec: the VK descriptor at
-- | every slot. It only types the step circuit's compile-time advice,
-- | which compile never forces, so no carrier value is ever built.
class MkUnitVkCarrier :: Type -> Type -> Constraint
class MkUnitVkCarrier spec (carrier :: Type) | spec -> carrier

instance MkUnitVkCarrier Unit Unit

instance
  MkUnitVkCarrier rest restCarrier =>
  MkUnitVkCarrier
    (SlotOf k n statement /\ rest)
    (SLVK.VerificationKey WrapVkChunks (F StepField) Boolean /\ restCarrier)
