-- | Advice classes for prover-side runtime side-loaded VKs.
-- |
-- | Carriers are spec-indexed and phase-aware:
-- |
-- | * Compile-time path uses `CompilePlaceholderVK` at side-loaded
-- |   slots — synthesised pure from the spec via `MkUnitVkCarrier`.
-- |   Has no `VerifierIndex` because `traverseSideloadedVKsCarrier`
-- |   only reads the in-circuit `Checked` shape; constructing a real
-- |   kimchi `VerifierIndex` placeholder would require Effect-ful FFI.
-- |
-- | * Prove-time path uses `VerificationKey` at side-loaded slots —
-- |   declared by `SideloadedVKsCarrier`. Carries a real hydrated
-- |   `VerifierIndex` (smart-constructor enforced; see
-- |   `Pickles.Sideload.VerificationKey`).
-- |
-- | `traverseSideloadedVKsCarrier` is cell-polymorphic via the
-- | `HasCircuit` class; each call site pins the cell type via the
-- | carrier value's literal structure.
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
import Pickles.Sideload.VerificationKey (VerificationKey, VerificationKeyVar)
import Pickles.Sideload.VerificationKey.Internal (CompilePlaceholderVK, SideloadedVK, cellCircuit, compileDummy)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil, PrevsSpecSideLoadedCons)
import Pickles.Types (StepField)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (Snarky, exists)
import Snarky.Circuit.DSL.Monad (class CheckedType, class CircuitM)
import Snarky.Constraint.Kimchi (KimchiConstraint)

-- | Prove-time spec-indexed VK carrier shape. Funcdep
-- | `spec -> carrier` lets the compiler pin the carrier from the spec
-- | alone.
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

-- | Side-loaded slot — runtime VK supplied via the prover input.
instance
  SideloadedVKsCarrier rest restCarrier =>
  SideloadedVKsCarrier
    (PrevsSpecSideLoadedCons mpvMax statement rest)
    (VerificationKey /\ restCarrier)

-- | Prover-monad source for the spec-indexed VK carrier.
-- |
-- | The carrier shape varies per monad: the `Effect` instance returns
-- | a compile-time placeholder carrier (cells = `CompilePlaceholderVK`,
-- | synthesised by `MkUnitVkCarrier`); a prover-monad instance would
-- | return the prove-time carrier (cells = `VerificationKey`).
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
-- | `compileDummy :: CompilePlaceholderVK`. Pure construction — no
-- | kimchi FFI required, because the placeholder cell carries only
-- | the in-circuit `Checked` shape (no `VerifierIndex`).
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
    (CompilePlaceholderVK /\ restCarrier) where
  mkUnitVkCarrier = compileDummy /\ mkUnitVkCarrier @rest

-- | Walks the carrier in lockstep with the spec and emits a parallel
-- | `Vector len (Maybe (VerificationKeyVar StepField))`.
-- |
-- | Cell-polymorphic: works on either the compile-time
-- | `CompilePlaceholderVK` (= `SideloadedVK Unit`) or prove-time
-- | `VerificationKey` (= `SideloadedVK (VerifierIndex …)`). The
-- | side-loaded instance reads only the `circuit` field via the
-- | parametric `cellCircuit`; no class dispatch.
class TraverseSideloadedVKsCarrier
  :: Type -> Type -> Int -> Type -> Constraint
class
  TraverseSideloadedVKsCarrier cell spec len carrier
  | cell spec -> len carrier
  where
  traverseSideloadedVKsCarrier
    :: forall t m
     . CircuitM StepField (KimchiConstraint StepField) t m
    => CheckedType StepField (KimchiConstraint StepField) (VerificationKeyVar StepField)
    => carrier
    -> Snarky (KimchiConstraint StepField) t m
         (Vector len (Maybe (VerificationKeyVar StepField)))

instance TraverseSideloadedVKsCarrier cell PrevsSpecNil 0 Unit where
  traverseSideloadedVKsCarrier _ = pure Vector.nil

instance
  ( TraverseSideloadedVKsCarrier cell rest restLen restCarrier
  , Add restLen 1 len
  ) =>
  TraverseSideloadedVKsCarrier
    cell
    (PrevsSpecCons n statement rest)
    len
    (Unit /\ restCarrier)
  where
  traverseSideloadedVKsCarrier (_ /\ rest) = do
    restVks <- traverseSideloadedVKsCarrier @cell @rest rest
    pure (Vector.cons Nothing restVks)

instance
  ( TraverseSideloadedVKsCarrier (SideloadedVK a) rest restLen restCarrier
  , Add restLen 1 len
  ) =>
  TraverseSideloadedVKsCarrier
    (SideloadedVK a)
    (PrevsSpecSideLoadedCons mpvMax statement rest)
    len
    (SideloadedVK a /\ restCarrier)
  where
  traverseSideloadedVKsCarrier (headCell /\ rest) = do
    -- `exists` against the cell's `circuit` field (a `Checked` —
    -- extracted by the parametric `cellCircuit`) allocates a
    -- `VerificationKeyVar`.
    headVar <- exists (pure (cellCircuit headCell))
    restVks <- traverseSideloadedVKsCarrier @(SideloadedVK a) @rest rest
    pure (Vector.cons (Just headVar) restVks)
