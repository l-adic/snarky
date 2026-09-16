-- | The spec-indexed carrier that hands a circuit its side-loaded
-- | verification keys, in two phases. At compile time a cell is the VK
-- | descriptor alone, synthesised from the spec by `MkUnitVkCarrier`,
-- | because the in-circuit walk reads nothing else. At prove time it is
-- | a `SlotProveVk`, whose `Bundle` adds the hydrated `VerifierIndex`
-- | the prover machinery needs.
-- |
-- | Both carriers are uniform across slots: whether a slot is
-- | side-loaded follows from its `SlotWrapKey`, which is runtime data,
-- | so no carrier can vary its cell per slot.
module Pickles.Sideload.Advice
  ( class SideloadedVKsCarrier
  , class SideloadedVKsM
  , getSideloadedVKsCarrier
  , class MkUnitVkCarrier
  , mkUnitVkCarrier
  ) where

import Prelude

import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Pickles.Field (StepField)
import Pickles.Sideload.Bundle (SlotProveVk)
import Pickles.Sideload.VerificationKey (VerificationKey, compileDummy) as SLVK
import Pickles.Slots (Slot)
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
    (Slot n statement /\ rest)
    (SlotProveVk WrapVkChunks /\ restCarrier)

-- | The monad a spec-indexed VK carrier is drawn from.
class
  Monad m <=
  SideloadedVKsM (spec :: Type) (m :: Type -> Type) (carrier :: Type)
  | spec m -> carrier
  , m -> spec carrier where
  getSideloadedVKsCarrier :: Unit -> m carrier

-- | In `Effect`, the carrier is the placeholder one: compile time,
-- | where the constraint-system pass discards prover-supplied values.
instance
  MkUnitVkCarrier spec carrier =>
  SideloadedVKsM spec Effect carrier where
  getSideloadedVKsCarrier _ = pure (mkUnitVkCarrier @spec)

-- | A placeholder carrier in the spec's shape: `SLVK.compileDummy` at
-- | every slot. Pure construction, no kimchi FFI, because a descriptor
-- | is all the in-circuit walk reads.
-- |
-- | A compiled slot gets a dummy descriptor it never reads: its
-- | blueprint routes to `ConstVk` or `SharedExistsVk` without touching
-- | the cell.
class MkUnitVkCarrier :: Type -> Type -> Constraint
class MkUnitVkCarrier spec (carrier :: Type) | spec -> carrier where
  mkUnitVkCarrier :: carrier

instance MkUnitVkCarrier Unit Unit where
  mkUnitVkCarrier = unit

instance
  MkUnitVkCarrier rest restCarrier =>
  MkUnitVkCarrier
    (Slot n statement /\ rest)
    (SLVK.VerificationKey WrapVkChunks (F StepField) Boolean /\ restCarrier) where
  mkUnitVkCarrier = SLVK.compileDummy /\ mkUnitVkCarrier @rest
