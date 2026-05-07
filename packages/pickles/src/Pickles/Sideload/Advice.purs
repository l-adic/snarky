-- | Advice classes for prover-side runtime side-loaded VKs.
-- |
-- | Parallel to `Pickles.Step.Advice`'s `StepWitnessM`/`StepSlotsM`:
-- | the prover monad implements `SideloadedVKsM` concretely; the
-- | compile-time `Effect` instance throws (the constraint-system pass
-- | discards the `~compute` body).
-- |
-- | Carriers are spec-indexed via `SideloadedVKsCarrier`: a `PrevsSpec`
-- | chain produces an interleaved tuple where each compiled prev
-- | (`PrevsSpecCons`) contributes `Unit` and each side-loaded prev
-- | (`PrevsSpecSideLoadedCons`) contributes a `VerificationKey`.
-- | Mismatch between spec and carrier becomes a type error.
-- |
-- | Reference: OCaml `Pickles.Side_loaded` + `step_main.ml:520-525`.
module Pickles.Sideload.Advice
  ( class SideloadedVKsCarrier
  , class SideloadedVKsM
  , getSideloadedVKsCarrier
  , class MkUnitVkCarrier
  , mkUnitVkCarrier
  , class TraverseSideloadedVKsCarrier
  , traverseSideloadedVKsCarrier
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.Sideload.VerificationKey (VerificationKey, VerificationKeyVar, dummy)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil, PrevsSpecSideLoadedCons)
import Pickles.Types (StepField)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (Snarky, exists)
import Snarky.Circuit.DSL.Monad (class CheckedType, class CircuitM)
import Snarky.Constraint.Kimchi (KimchiConstraint)

-- | Spec-indexed VK carrier shape. Funcdep `spec -> carrier` lets the
-- | compiler pin the carrier from the spec alone.
-- |
-- | * `PrevsSpecNil` → `Unit`
-- | * `PrevsSpecCons n stmt rest` → `Unit /\ restCarrier`
-- | * `PrevsSpecSideLoadedCons mpvMax stmt rest` → `VerificationKey /\ restCarrier`
class SideloadedVKsCarrier :: Type -> Type -> Constraint
class SideloadedVKsCarrier spec carrier | spec -> carrier

instance SideloadedVKsCarrier PrevsSpecNil Unit

-- | Compiled slot — wrap_key + step_domains come from compile-time-baked
-- | data, no runtime VK needed.
instance
  SideloadedVKsCarrier rest restCarrier =>
  SideloadedVKsCarrier
    (PrevsSpecCons n statement rest)
    (Unit /\ restCarrier)

-- | Side-loaded slot — runtime VK supplied via the prover monad's
-- | `getSideloadedVKsCarrier`.
instance
  SideloadedVKsCarrier rest restCarrier =>
  SideloadedVKsCarrier
    (PrevsSpecSideLoadedCons mpvMax statement rest)
    (VerificationKey /\ restCarrier)

-- | Prover-monad source for the spec-indexed VK carrier. Funcdeps:
-- | `spec -> carrier`, `m -> spec carrier` (so a single prover-monad
-- | instance fixes both without callers annotating spec at every
-- | call).
class
  ( Monad m
  , SideloadedVKsCarrier spec carrier
  ) <=
  SideloadedVKsM spec (m :: Type -> Type) carrier
  | spec -> carrier
  , m -> spec carrier where
  getSideloadedVKsCarrier :: Unit -> m carrier

-- | `Effect` instance — synthesises an all-`Unit` carrier via
-- | `MkUnitVkCarrier`. Resolves only for compiled-only specs; specs
-- | with side-loaded prevs need a different prover monad whose
-- | instance reads real runtime VKs.
instance
  ( SideloadedVKsCarrier spec carrier
  , MkUnitVkCarrier spec carrier
  ) =>
  SideloadedVKsM spec Effect carrier where
  getSideloadedVKsCarrier _ = pure (mkUnitVkCarrier @spec)

-- | Synthesises a placeholder VK carrier matching the spec shape.
-- | Compiled slots become `Unit`; side-loaded slots become
-- | `VerificationKey.dummy`. Used at compile time where prover-supplied
-- | values are discarded by the constraint-system pass; real prove-time
-- | carriers come through `SideloadedVKsM` (persisted into
-- | `StepAdvice.sideloadedVKs`).
class MkUnitVkCarrier :: Type -> Type -> Constraint
class MkUnitVkCarrier spec (carrier :: Type) | spec -> carrier where
  mkUnitVkCarrier :: carrier

instance MkUnitVkCarrier PrevsSpecNil Unit where
  mkUnitVkCarrier = unit

instance
  MkUnitVkCarrier rest restCarrier =>
  MkUnitVkCarrier (PrevsSpecCons n statement rest) (Unit /\ restCarrier) where
  mkUnitVkCarrier = unit /\ mkUnitVkCarrier @rest

instance
  MkUnitVkCarrier rest restCarrier =>
  MkUnitVkCarrier
    (PrevsSpecSideLoadedCons mpvMax statement rest)
    (VerificationKey /\ restCarrier) where
  mkUnitVkCarrier = dummy /\ mkUnitVkCarrier @rest

-- | Walks the carrier in lockstep with the spec and emits a parallel
-- | `Vector len (Maybe (VerificationKeyVar StepField))`:
-- |
-- | * Compiled slot → `Nothing` (its wrap VK comes from the shared
-- |   `Req.Wrap_index` allocation, not a per-slot `exists`).
-- | * Side-loaded slot → `Just var`, where `var` is allocated by
-- |   `exists` against the bundle's `circuit` field. The wrap_index's
-- |   per-bit boolean check and on-curve check are emitted by the
-- |   parameterised `CircuitType` instance on `Checked`.
class TraverseSideloadedVKsCarrier
  :: Type -> Int -> Type -> Constraint
class
  TraverseSideloadedVKsCarrier spec len carrier
  | spec -> len carrier
  where
  traverseSideloadedVKsCarrier
    :: forall t m
     . CircuitM StepField (KimchiConstraint StepField) t m
    => CheckedType StepField (KimchiConstraint StepField) (VerificationKeyVar StepField)
    => carrier
    -> Snarky (KimchiConstraint StepField) t m
         (Vector len (Maybe (VerificationKeyVar StepField)))

instance TraverseSideloadedVKsCarrier PrevsSpecNil 0 Unit where
  traverseSideloadedVKsCarrier _ = pure Vector.nil

instance
  ( TraverseSideloadedVKsCarrier rest restLen restCarrier
  , Add restLen 1 len
  ) =>
  TraverseSideloadedVKsCarrier
    (PrevsSpecCons n statement rest)
    len
    (Unit /\ restCarrier)
  where
  traverseSideloadedVKsCarrier (_ /\ rest) = do
    restVks <- traverseSideloadedVKsCarrier @rest rest
    pure (Vector.cons Nothing restVks)

instance
  ( TraverseSideloadedVKsCarrier rest restLen restCarrier
  , Add restLen 1 len
  ) =>
  TraverseSideloadedVKsCarrier
    (PrevsSpecSideLoadedCons mpvMax statement rest)
    len
    (VerificationKey /\ restCarrier)
  where
  traverseSideloadedVKsCarrier (headVk /\ rest) = do
    -- `exists` against the bundle's `circuit` field allocates a
    -- `VerificationKeyVar`. The bundle's `wrapVk` is irrelevant here
    -- and stays in the runtime advice.
    headVar <- exists (pure headVk.circuit)
    restVks <- traverseSideloadedVKsCarrier @rest rest
    pure (Vector.cons (Just headVar) restVks)
