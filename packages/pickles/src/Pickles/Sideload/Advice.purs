-- | Advice classes for prover-side runtime side-loaded VKs.
-- |
-- | Carriers are spec-indexed and phase-aware:
-- |
-- | * Compile-time path uses the side-loaded VK descriptor directly at
-- |   side-loaded slots — synthesised pure from the spec via
-- |   `MkUnitVkCarrier` (`SLVK.compileDummy`). No kimchi
-- |   `VerifierIndex` because the in-circuit walk only reads the
-- |   descriptor; the runtime handle is not needed.
-- |
-- | * Prove-time path uses `Bundle` at side-loaded slots — declared by
-- |   `SideloadedVKsCarrier`. Carries both halves: the descriptor (for
-- |   the in-circuit walk) and the hydrated `VerifierIndex` (for the
-- |   prover machinery).
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
import Pickles.Sideload.Bundle (Bundle)
import Pickles.Sideload.VerificationKey (VerificationKey, compileDummy) as SLVK
import Pickles.Step.Slots (Compiled, SideLoaded, Slot)
import Pickles.Step.Types (Field)
import Snarky.Circuit.DSL (F)

-- | Prove-time spec-indexed VK carrier shape. Funcdep
-- | `spec -> carrier` lets the compiler pin the carrier from the spec
-- | alone.
-- |
-- | * `Unit` → `Unit`
-- | * `Slot Compiled n stmt /\ rest` → `Unit /\ restCarrier`
-- | * `Slot SideLoaded mpvMax stmt /\ rest` → `Bundle /\ restCarrier`
class SideloadedVKsCarrier :: Type -> Type -> Constraint
class SideloadedVKsCarrier spec carrier | spec -> carrier

instance SideloadedVKsCarrier Unit Unit

-- | Compiled slot — wrap_key + step_domains come from compile-time-baked
-- | data, no runtime VK needed.
instance
  SideloadedVKsCarrier rest restCarrier =>
  SideloadedVKsCarrier
    (Slot Compiled n statement /\ rest)
    (Unit /\ restCarrier)

-- | Side-loaded slot — runtime VK supplied via the prover input.
instance
  SideloadedVKsCarrier rest restCarrier =>
  SideloadedVKsCarrier
    (Slot SideLoaded mpvMax statement /\ rest)
    (Bundle /\ restCarrier)

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
-- | shape. Compiled slots become `Unit`; side-loaded slots become
-- | `SLVK.compileDummy`. Pure construction — no kimchi FFI required,
-- | because the placeholder is just the descriptor (the in-circuit
-- | walk reads no `VerifierIndex`).
class MkUnitVkCarrier :: Type -> Type -> Constraint
class MkUnitVkCarrier spec (carrier :: Type) | spec -> carrier where
  mkUnitVkCarrier :: carrier

instance MkUnitVkCarrier Unit Unit where
  mkUnitVkCarrier = unit

instance
  MkUnitVkCarrier rest restCarrier =>
  MkUnitVkCarrier (Slot Compiled n statement /\ rest) (Unit /\ restCarrier) where
  mkUnitVkCarrier = unit /\ mkUnitVkCarrier @rest

instance
  MkUnitVkCarrier rest restCarrier =>
  MkUnitVkCarrier
    (Slot SideLoaded mpvMax statement /\ rest)
    (SLVK.VerificationKey (F Field) Boolean /\ restCarrier) where
  mkUnitVkCarrier = SLVK.compileDummy /\ mkUnitVkCarrier @rest
