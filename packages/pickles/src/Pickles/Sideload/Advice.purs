-- | Advice classes for prover-side runtime side-loaded VKs.
-- |
-- | Carriers are spec-indexed and phase-aware:
-- |
-- | * Compile-time path uses the side-loaded VK descriptor —
-- |   synthesised pure from the spec via `MkUnitVkCarrier`
-- |   (`SLVK.compileDummy`). No kimchi `VerifierIndex` because the
-- |   in-circuit walk only reads the descriptor; the runtime handle is
-- |   not needed.
-- |
-- | * Prove-time path uses `SlotProveVk` — declared by
-- |   `SideloadedVKsCarrier`. Its `Bundle` carries both halves: the
-- |   descriptor (for the in-circuit walk) and the hydrated
-- |   `VerifierIndex` (for the prover machinery). `NoSideLoadedVk` is
-- |   the cell of a compiled slot, whose key is a compile-time
-- |   constant.
-- |
-- | Both carriers are uniform across slots. Which slots are side-loaded
-- | is runtime data (the slot's `SlotWrapKey`), not a type-level fact,
-- | so neither carrier can vary its cell per slot.
-- |
-- | Reference: OCaml `Pickles.Side_loaded` + `step_main.ml:520-525`.
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

-- | Prove-time spec-indexed VK carrier shape. Funcdep
-- | `spec -> carrier` lets the compiler pin the carrier from the spec
-- | alone.
-- |
-- | * `Unit` → `Unit`
-- | * `Slot n nc stmt /\ rest` → `SlotProveVk nc /\ restCarrier`
-- |
-- | Every slot gets the same cell, because whether a slot is
-- | side-loaded is a property of its `SlotWrapKey`, not of its type.
-- | A side-loaded slot supplies `SideLoadedVk` the runtime bundle; a
-- | compiled slot, whose key is a compile-time constant, supplies
-- | `NoSideLoadedVk`. The `Bundle nc` carries the slot's chunks count
-- | (the slot's own `nc` from `Slot n nc statement`).
class SideloadedVKsCarrier :: Type -> Type -> Constraint
class SideloadedVKsCarrier spec carrier | spec -> carrier

instance SideloadedVKsCarrier Unit Unit

instance
  SideloadedVKsCarrier rest restCarrier =>
  SideloadedVKsCarrier
    (Slot n statement /\ rest)
    (SlotProveVk WrapVkChunks /\ restCarrier)

-- | Prover-monad source for the spec-indexed VK carrier.
-- |
-- | The carrier shape varies per monad: the `Effect` instance returns
-- | a compile-time placeholder carrier (cells = `SLVK.compileDummy`,
-- | synthesised by `MkUnitVkCarrier`); a prover-monad instance would
-- | return the prove-time carrier (cells = `Bundle`).
class
  Monad m <=
  SideloadedVKsM (spec :: Type) (m :: Type -> Type) (carrier :: Type)
  | spec m -> carrier
  , m -> spec carrier where
  getSideloadedVKsCarrier :: Unit -> m carrier

-- | `Effect` instance — synthesises an all-`Unit` / `compileDummy`
-- | carrier via `MkUnitVkCarrier`. Used at compile time where prover-
-- | supplied values are discarded by the constraint-system pass.
instance
  MkUnitVkCarrier spec carrier =>
  SideloadedVKsM spec Effect carrier where
  getSideloadedVKsCarrier _ = pure (mkUnitVkCarrier @spec)

-- | Synthesises a compile-time placeholder carrier matching the spec
-- | shape: `SLVK.compileDummy` at every slot. Pure construction — no
-- | kimchi FFI required, because the placeholder is just the descriptor
-- | (the in-circuit walk reads no `VerifierIndex`).
-- |
-- | Compiled slots get a dummy descriptor they never read: the
-- | constraint-system pass discards prover-supplied values, and a
-- | compiled slot's blueprint routes to `ConstVk` / `SharedExistsVk`
-- | without touching the cell at all.
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
