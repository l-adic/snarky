-- | Advice class for the prover-side runtime side-loaded VKs.
-- |
-- | The PS analog of the user-supplied `Verifier_index` request in
-- | OCaml's standalone reference (`dump_side_loaded_main.ml:99-116`):
-- | the rule body needs the runtime VK for each side-loaded prev so
-- | it can populate the in-circuit `VerificationKeyVar`'s witnesses
-- | and (in the follow-up that wires the slot dispatch) feed
-- | `actual_wrap_domain_size` and `wrap_index` into step_main's
-- | per-prev verification.
-- |
-- | This is parallel to `Pickles.Step.Advice`'s
-- | `StepWitnessM`/`StepSlotsM`: the prover monad implements it
-- | concretely, the compile-time `Effect` instance throws (the
-- | constraint-system pass discards the `~compute` body).
-- |
-- | The carrier is **spec-indexed** via `SideloadedVKsCarrier`:
-- | given a `PrevsSpec*` chain, the carrier interleaves a slot per
-- | prev — `Unit` for compiled slots (`PrevsSpecCons`) and a
-- | `VerificationKey` for side-loaded slots (`PrevsSpecSideLoadedCons`).
-- | This mirrors the spec's structure exactly, so a side-loaded slot
-- | without a VK or a compiled slot with a VK becomes a type error.
-- |
-- | Reference:
-- |   mina/src/lib/crypto/pickles/dump_side_loaded_main/dump_side_loaded_main.ml:99-156
-- |   mina/src/lib/crypto/pickles/compile.ml:1049-1051 (in_circuit / in_prover)
-- |   mina/src/lib/crypto/pickles/step_main.ml:520-525 (`Side_loaded -> of_side_loaded`)
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
import Pickles.Sideload.VerificationKey (VerificationKey, VerificationKeyVar)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil, PrevsSpecSideLoadedCons)
import Pickles.Types (StepField)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (Snarky, exists)
import Snarky.Circuit.DSL.Monad (class CheckedType, class CircuitM)
import Snarky.Constraint.Kimchi (KimchiConstraint)

--------------------------------------------------------------------------------
-- SideloadedVKsCarrier — derive the per-slot VK carrier from the spec
--
-- Walks the same `PrevsSpec*` chain as `PrevsCarrier` /
-- `PrevValuesCarrier` (in `Pickles.Step.Prevs`) and produces an
-- interleaved tuple of VK slots:
--   PrevsSpecNil                              → Unit
--   PrevsSpecCons n stmt rest                 → Unit            /\ rest_carrier
--   PrevsSpecSideLoadedCons mpvMax stmt rest  → VerificationKey /\ rest_carrier
--
-- The fundep `spec -> carrier` lets the compiler pin the carrier
-- shape from the spec alone — no explicit length parameter, no
-- per-slot Maybe.
--------------------------------------------------------------------------------

class SideloadedVKsCarrier :: Type -> Type -> Constraint
class SideloadedVKsCarrier spec carrier | spec -> carrier

instance SideloadedVKsCarrier PrevsSpecNil Unit

-- | Compiled slot contributes `Unit` — its wrap_key + step_domains
-- | come from compile-time-baked data (the existing per-slot path).
instance
  SideloadedVKsCarrier rest restCarrier =>
  SideloadedVKsCarrier
    (PrevsSpecCons n statement rest)
    (Unit /\ restCarrier)

-- | Side-loaded slot contributes a `VerificationKey` — supplied at
-- | prove time via the rule's `~handler` analog (the prover monad's
-- | `getSideloadedVKsCarrier`).
instance
  SideloadedVKsCarrier rest restCarrier =>
  SideloadedVKsCarrier
    (PrevsSpecSideLoadedCons mpvMax statement rest)
    (VerificationKey /\ restCarrier)

--------------------------------------------------------------------------------
-- SideloadedVKsM — prover-monad source for the carrier
--------------------------------------------------------------------------------

-- | Spec-indexed runtime VK source.
-- |
-- | The `spec` parameter pins the carrier shape via
-- | `SideloadedVKsCarrier`; the `m -> spec` fundep lets a single
-- | prover-monad instance fix the carrier without callers needing to
-- | annotate the spec at every call.
class
  ( Monad m
  , SideloadedVKsCarrier spec carrier
  ) <=
  SideloadedVKsM spec (m :: Type -> Type) carrier
  | spec -> carrier
  , m -> spec carrier where
  getSideloadedVKsCarrier :: Unit -> m carrier

-- | Effect instance: synthesizes the all-Unit carrier via
-- | `MkUnitVkCarrier`. This covers compiled-only specs (where the
-- | carrier shape is `Unit /\ Unit /\ … /\ Unit`); specs that
-- | contain `PrevsSpecSideLoadedCons` slots have carriers shaped
-- | like `… /\ VerificationKey /\ …` and the `MkUnitVkCarrier`
-- | constraint won't resolve — those callers must use a different
-- | prover monad whose `SideloadedVKsM` instance reads real
-- | runtime VKs from the test setup.
-- |
-- | Routing the synthesis through this instance (rather than
-- | calling `mkUnitVkCarrier` directly at the use sites) keeps the
-- | side-loaded VK source uniformly behind `getSideloadedVKsCarrier`
-- | — the right channel for any future swap to a real
-- | runtime-VK-providing prover monad.
instance
  ( SideloadedVKsCarrier spec carrier
  , MkUnitVkCarrier carrier
  ) =>
  SideloadedVKsM spec Effect carrier where
  getSideloadedVKsCarrier _ = pure mkUnitVkCarrier

--------------------------------------------------------------------------------
-- MkUnitVkCarrier — synthesize an all-Unit VK carrier
--
-- Used by external callers (e.g. `runMultiProverBody`) that haven't
-- yet wired side-loaded VK sourcing through the prover monad. Produces
-- a value of any all-Unit nested-tuple shape — which is exactly the
-- carrier shape `SideloadedVKsCarrier` derives for specs whose slots
-- are all `PrevsSpecCons` (no `PrevsSpecSideLoadedCons`).
--
-- Specs that DO contain side-loaded slots have carriers shaped like
-- `Unit /\ VerificationKey /\ … `; this class is intentionally
-- unsatisfiable for those, forcing such call sites to source the
-- carrier from a real `SideloadedVKsM` instance.
--------------------------------------------------------------------------------

class MkUnitVkCarrier (carrier :: Type) where
  mkUnitVkCarrier :: carrier

instance MkUnitVkCarrier Unit where
  mkUnitVkCarrier = unit

instance MkUnitVkCarrier rest => MkUnitVkCarrier (Unit /\ rest) where
  mkUnitVkCarrier = unit /\ mkUnitVkCarrier

--------------------------------------------------------------------------------
-- TraverseSideloadedVKsCarrier — walk the carrier in lockstep with the spec
-- and allocate per-slot side-loaded VK vars
--
-- Walks a `SideloadedVKsCarrier`-shaped value (each `PrevsSpecCons`
-- slot is `Unit`, each `PrevsSpecSideLoadedCons` slot is a
-- `VerificationKey` bundle), emitting a parallel `Vector len (Maybe
-- (VerificationKeyVar StepField))`:
--
--   * Compiled slot (`PrevsSpecCons`) → `Nothing` (its wrap VK comes
--     from the shared `Req.Wrap_index` allocation, not a per-slot
--     exists).
--   * Side-loaded slot (`PrevsSpecSideLoadedCons`) → `Just var`,
--     where `var :: VerificationKeyVar StepField` is allocated by
--     `exists` against the bundle's `circuit` (a `Checked Boolean
--     …`). The existing `CircuitType (Checked b pt) (Checked bvar
--     ptvar)` instance handles the per-bit boolean check and
--     on-curve check on each wrap_index commitment.
--
-- The instance head's spec drives the dispatch; `len` is the prev
-- count (matching `PrevsCarrier`'s `len` fundep).
--------------------------------------------------------------------------------

class TraverseSideloadedVKsCarrier
  :: Type -> Int -> Type -> Constraint
class TraverseSideloadedVKsCarrier spec len carrier
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
    -- `exists` against the bundle's `circuit` field — a `Checked
    -- Boolean (WeierstrassAffinePoint Pallas.G (F StepField))` —
    -- allocates a `VerificationKeyVar StepField` (= `Checked
    -- (BoolVar StepField) (WeierstrassAffinePoint Pallas.G (FVar
    -- StepField))`). The bundle's `wrapVk` field is irrelevant here
    -- and stays in the runtime advice for `mkStepAdvice` /
    -- `shapeProveData` consumption.
    headVar <- exists (pure headVk.circuit)
    restVks <- traverseSideloadedVKsCarrier @rest rest
    pure (Vector.cons (Just headVar) restVks)
