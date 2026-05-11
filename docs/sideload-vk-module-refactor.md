# Side-loaded VK module refactor — plan

## Goal

Replace the current side-loaded VK machinery (`Pickles.Sideload.VerificationKey`
+ `Pickles.Sideload.VerificationKey.Internal`) with a hierarchy that:

- separates regular-VK from side-loaded-VK data into distinct modules,
- separates side-loaded VK *data* from the prove-time *kimchi handle*
  pairing,
- uses a single 2-parameter newtype for the side-loaded VK shape (one
  declaration for both value and var forms — single source of truth),
- eliminates the `unsafeCrashWith` at `Step/Main.purs:911` that the PR
  reviewer flagged "HUGE RED FLAG" by putting the in-circuit-allocated
  VK into the same `SlotVkSource.SideloadedExistsVk` constructor that
  says the slot is side-loaded,
- removes the misleading `Checked b pt` / `SideloadedVK a` /
  `CompilePlaceholderVK` / `cellCircuit` apparatus in favour of named
  types in well-scoped modules.

## Module hierarchy

```
Pickles.ProofsVerified                — N0/N1/N2 enum + conversions
Pickles.VerificationKey               — regular wrap-VK shape (commitments)
Pickles.Sideload.VerificationKey      — side-loaded VK descriptor (2-param newtype)
Pickles.Sideload.Bundle               — prove-time pairing of VK + kimchi handle
Pickles.Sideload.Advice               — (existing) carrier classes; updated to use new types
Pickles.Sideload.FFI                  — (existing) JSON loader FFI; updated as needed
```

`Pickles.Sideload.*` is the umbrella for the side-loaded feature
(matching OCaml's `Pickles.Side_loaded.*` and the existing PS code).
The bundle and the VK data both live under that umbrella because both
are aspects of the side-loaded feature.

Dependency edges (acyclic; arrows point from importer to import):

```
ProofsVerified  ← VerificationKey ← Sideload.VerificationKey ← Sideload.Bundle
                                  ↖
                                    Sideload.Advice (existing)
```

## Skeletons

### `Pickles.ProofsVerified`

```purescript
-- The {N0, N1, N2} enum used as both proof-count and side-loaded
-- wrap-domain tags. Mirrors OCaml `Pickles_base.Proofs_verified.t`.
module Pickles.ProofsVerified
  ( ProofsVerified(..)
  , ProofsVerifiedCount
  , proofsVerifiedToBoolVec
  , boolVecToProofsVerified
  ) where

import Prelude
import Data.Enum (class BoundedEnum, class Enum)
import Data.Generic.Rep (class Generic)
import Data.Vector (Vector)

data ProofsVerified = N0 | N1 | N2
type ProofsVerifiedCount = 3

derive instance Eq ProofsVerified
derive instance Ord ProofsVerified
derive instance Generic ProofsVerified _
instance Show ProofsVerified
instance Bounded ProofsVerified
instance Enum ProofsVerified
instance BoundedEnum ProofsVerified

proofsVerifiedToBoolVec :: ProofsVerified -> Vector ProofsVerifiedCount Boolean
boolVecToProofsVerified :: Vector ProofsVerifiedCount Boolean -> ProofsVerified
```

### `Pickles.VerificationKey`

```purescript
-- Regular wrap-VK commitment shape (σ / coeff / index). Polymorphic
-- in the point type so the same record serves value form
-- (a = Weierstrass G (F f)) and var form (a = Weierstrass G (FVar f)).
module Pickles.VerificationKey
  ( VerificationKey(..)
  , extractWrapVKComms
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Vector (Vector)
import Pickles.Types (StepField, WrapField)
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Circuit.DSL (F)
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.Types (class CircuitType)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)

newtype VerificationKey a = VerificationKey
  { sigma :: Vector 7 a
  , coeff :: Vector 15 a
  , index :: Vector 9 a
  }

derive instance Generic (VerificationKey a) _
derive instance Functor VerificationKey
instance (CircuitType f a var) => CircuitType f (VerificationKey a) (VerificationKey var)
instance (CheckedType f c var) => CheckedType f c (VerificationKey var)

-- Project σ / coeff / index commitments out of a hydrated kimchi
-- VerifierIndex — the boundary between kimchi's runtime VK and the
-- Pickles protocol-level VK shape.
extractWrapVKComms
  :: VerifierIndex Pallas.G WrapField
  -> VerificationKey (WeierstrassAffinePoint Pallas.G (F StepField))
```

### `Pickles.Sideload.VerificationKey`

```purescript
-- Side-loaded VK descriptor: a child's wrap VK at the protocol level,
-- containing only the data the parent's step circuit walks. Two type
-- parameters select between value and var forms via the same record:
--   value:  VerificationKey (F StepField)  Boolean
--   var:    VerificationKey (FVar f)       (BoolVar f)
-- No kimchi runtime handle here — that lives in Pickles.Sideload.Bundle.
module Pickles.Sideload.VerificationKey
  ( VerificationKey(..)
  , compileDummy
  , mkVerificationKey
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Vector (Vector)
import Pickles.ProofsVerified (ProofsVerified, ProofsVerifiedCount)
import Pickles.Types (StepField)
import Pickles.VerificationKey as VK
import Snarky.Circuit.DSL (BoolVar, F, FVar)
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.Types (class CircuitType)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)

newtype VerificationKey f b = VerificationKey
  { maxProofsVerified :: Vector ProofsVerifiedCount b
  , actualWrapDomainSize :: Vector ProofsVerifiedCount b
  , wrapIndex :: VK.VerificationKey (WeierstrassAffinePoint Pallas.G f)
  }

derive instance Generic (VerificationKey f b) _

-- Bridges value form to var form via the parametric CircuitType
-- instances on the row's elements.
instance
  ( CircuitType StepField f fvar
  , CircuitType StepField b bvar
  ) =>
  CircuitType StepField (VerificationKey f b) (VerificationKey fvar bvar)

-- Validity constraints emitted on allocation: boolean + one-hot on
-- each mask, on-curve on every commitment. Only applies to the
-- var-form specialization.
instance
  ( CheckedType g c (BoolVar g)
  , CheckedType g c (WeierstrassAffinePoint Pallas.G (FVar g))
  , PrimeField g
  ) =>
  CheckedType g c (VerificationKey (FVar g) (BoolVar g))

-- Compile-time placeholder sized for the largest possible VK
-- (mpv = N2, wrap_domain = N2). Used to feed `exists` for in-circuit
-- placeholder allocation; smaller-mpv runtime VKs mask down via their
-- own one-hot bits.
compileDummy :: VerificationKey (F StepField) Boolean

-- Smart constructor from the user-friendly ProofsVerified enum.
mkVerificationKey
  :: { maxProofsVerified :: ProofsVerified
     , actualWrapDomainSize :: ProofsVerified
     , wrapIndex :: VK.VerificationKey (WeierstrassAffinePoint Pallas.G (F StepField))
     }
  -> VerificationKey (F StepField) Boolean
```

### `Pickles.Sideload.Bundle`

```purescript
-- Prove-time pairing of a child's wrap VK in its two views:
--   * `vk` — the circuit-representable side-loaded VK shape (feeds
--     `exists` during the parent step circuit walk).
--   * `verifierIndex` — the kimchi runtime handle. No circuit
--     representation — used only by prover machinery that needs to
--     compute oracles or run kimchi verify against the child's wrap
--     proof.
-- Constructor is hidden; construct via `mkBundle`. The smart
-- constructor derives `vk`'s commitments from `verifierIndex` so the
-- two halves are guaranteed consistent.
module Pickles.Sideload.Bundle
  ( Bundle
  , class HasSideLoadedVk
  , projectVk
  , mkBundle
  , verifierIndex
  ) where

import Prelude
import Pickles.ProofsVerified (ProofsVerified)
import Pickles.Types (StepField, WrapField)
import Pickles.Sideload.VerificationKey as SLVK
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Circuit.DSL (F)
import Snarky.Curves.Pallas as Pallas

newtype Bundle = Bundle
  { vk :: SLVK.VerificationKey (F StepField) Boolean
  , verifierIndex :: VerifierIndex Pallas.G WrapField
  }

-- Projects the side-loaded VK out of a carrier cell regardless of
-- phase. Compile-time cells (SLVK.VerificationKey directly) project
-- as identity; prove-time cells (Bundle) project to the `.vk` field.
class HasSideLoadedVk cell where
  projectVk :: cell -> SLVK.VerificationKey (F StepField) Boolean

instance HasSideLoadedVk (SLVK.VerificationKey (F StepField) Boolean)
instance HasSideLoadedVk Bundle

mkBundle
  :: { verifierIndex :: VerifierIndex Pallas.G WrapField
     , maxProofsVerified :: ProofsVerified
     , actualWrapDomainSize :: ProofsVerified
     }
  -> Bundle

verifierIndex :: Bundle -> VerifierIndex Pallas.G WrapField
```

## Changes to existing modules

### `Pickles.Sideload.Advice`

Replace the old `SideloadedVKsCarrier` instance that placed
`VerificationKey` (the old bundle type) at side-loaded slots with one
that places `Sideload.Bundle.Bundle`:

```purescript
instance
  SideloadedVKsCarrier rest restCarrier =>
  SideloadedVKsCarrier
    (Slot SideLoaded mpvMax statement /\ rest)
    (Sideload.Bundle.Bundle /\ restCarrier)
```

Replace the `MkUnitVkCarrier` instance for `Slot SideLoaded` similarly
— the compile-time placeholder is now `SLVK.VerificationKey (F
StepField) Boolean` directly (using `SLVK.compileDummy`), not a
`CompilePlaceholderVK` wrapper:

```purescript
instance
  MkUnitVkCarrier rest restCarrier =>
  MkUnitVkCarrier
    (Slot SideLoaded mpvMax statement /\ rest)
    (SLVK.VerificationKey (F StepField) Boolean /\ restCarrier) where
  mkUnitVkCarrier = SLVK.compileDummy /\ mkUnitVkCarrier @rest
```

### `Pickles.Sideload.FFI`

The on-disk JSON loader path produces a `VerifierIndex` (via
`vestaVerifierIndexFromSerdeJson` + `vestaHydrateVerifierIndex`).
Callers that previously built a `VerificationKey` (old bundle) from
that now build a `Bundle` via `Sideload.Bundle.mkBundle`. No FFI
signatures change.

### `Pickles.Types`

Move `data VerificationKey a = …` out of `Pickles.Types` into the new
`Pickles.VerificationKey` module. Update all consumers' imports.

### Consumers of the deleted types

- `Pickles.Step.Main` — current code references `Checked(..)`,
  `SideloadedVK`, `cellCircuit`. Update to use
  `SLVK.VerificationKey (FVar f) (BoolVar f)` and
  `Sideload.Bundle.projectVk`.
- `Pickles.Prove.Compile` — same renames; also update
  `BuildSlotVkSources` constraint usage to match the new
  `HasSideLoadedVk` class.
- `Pickles.Prove.Step` — re-export updates only; no semantic change.
- Test fixtures (`packages/pickles/test/Test/Pickles/...`) and
  circuit-diff fixtures (`packages/pickles-circuit-diffs/...`) —
  rewrite constructions of side-loaded VKs from the old `SideloadedVK
  { circuit, wrapVk }` shape to the new `mkBundle` /
  `SLVK.compileDummy` / `SLVK.mkVerificationKey` smart constructors.

## Deletions

- `Pickles.Sideload.VerificationKey.Internal` — contents migrate to
  the new modules; module deleted.
- `Pickles.Sideload.VerificationKey` (the existing facade) — replaced
  by the new module of the same name with a fundamentally different
  type (`VerificationKey f b`).
- Old types that go away entirely: `Checked b pt`, `SideloadedVK a`,
  `CompilePlaceholderVK`, `VerificationKeyVar f`.
- Old functions that go away: `cellCircuit`, `mkChecked`,
  `compileDummy :: CompilePlaceholderVK` (replaced by `compileDummy ::
  SLVK.VerificationKey (F StepField) Boolean`).
- Old function migrating: `fromCompiledWrap` becomes `mkBundle` in
  `Pickles.Sideload.Bundle`.

## Migration table

| Currently at | Goes to |
|---|---|
| `Pickles.Types.VerificationKey a` | `Pickles.VerificationKey.VerificationKey a` |
| `Pickles.Sideload.VerificationKey.Internal.Checked b pt` | `Pickles.Sideload.VerificationKey.VerificationKey f b` (rebased: `b` is Boolean axis, `f` is point-coord axis) |
| `Pickles.Sideload.VerificationKey.Internal.SideloadedVK a` | `Pickles.Sideload.Bundle.Bundle` (when `a` was prove-time `VerifierIndex`); compile-time placeholder uses `SLVK.VerificationKey (F StepField) Boolean` directly |
| `Pickles.Sideload.VerificationKey.Internal.VerificationKey` (prove-time alias) | `Pickles.Sideload.Bundle.Bundle` |
| `Pickles.Sideload.VerificationKey.Internal.CompilePlaceholderVK` (compile-time alias) | deleted; use `SLVK.VerificationKey (F StepField) Boolean` |
| `Pickles.Sideload.VerificationKey.Internal.VerificationKeyVar f` | `SLVK.VerificationKey (FVar f) (BoolVar f)` (inline saturation) |
| `Pickles.Sideload.VerificationKey.Internal.compileDummy :: CompilePlaceholderVK` | `SLVK.compileDummy :: SLVK.VerificationKey (F StepField) Boolean` |
| `Pickles.Sideload.VerificationKey.Internal.cellCircuit` | replaced by `Sideload.Bundle.HasSideLoadedVk.projectVk` |
| `Pickles.Sideload.VerificationKey.Internal.fromCompiledWrap` | `Pickles.Sideload.Bundle.mkBundle` |
| `Pickles.Sideload.VerificationKey.Internal.mkChecked` | `Pickles.Sideload.VerificationKey.mkVerificationKey` |
| `Pickles.Sideload.VerificationKey.Internal.ProofsVerified(..)` etc. | `Pickles.ProofsVerified.*` (separate module) |
| `Pickles.Sideload.VerificationKey` (facade) | deleted; public API is the four new modules directly |
| `Pickles.Sideload.VerificationKey.Internal` | deleted |

## Inventory

| Module | Types | Instances | Functions |
|---|---|---|---|
| `Pickles.ProofsVerified` | `ProofsVerified`, `ProofsVerifiedCount` | Eq, Ord, Generic, Show, Bounded, Enum, BoundedEnum | `proofsVerifiedToBoolVec`, `boolVecToProofsVerified` |
| `Pickles.VerificationKey` | `VerificationKey a` | Generic, Functor, CircuitType, CheckedType | `extractWrapVKComms` |
| `Pickles.Sideload.VerificationKey` | `VerificationKey f b` | Generic, CircuitType (parametric bridge), CheckedType (var-form specialization) | `compileDummy`, `mkVerificationKey` |
| `Pickles.Sideload.Bundle` | `Bundle` (constructor hidden), `class HasSideLoadedVk` | `HasSideLoadedVk` for `SLVK.VerificationKey (F StepField) Boolean` and `Bundle` | `projectVk`, `mkBundle`, `verifierIndex` |

## Key design decisions and rationale

### Why one 2-parameter newtype instead of two distinct types

Earlier drafts split into `SideLoadedVk` (value form) and
`SideLoadedVkVar f` (var form). The reviewer flagged the
synchronization burden — adding a field to one and forgetting the
other would silently misalign serialized fields.

A 2-parameter newtype `VerificationKey f b` (point-coord axis and
boolean axis) gives single-source-of-truth. The two saturations
(`(F StepField) Boolean` for value, `(FVar f) (BoolVar f)` for var)
fall out of the same record declaration; CircuitType bridges them via
the existing parametric machinery.

### Why no `.Checked` submodule

Earlier drafts proposed `Pickles.VerificationKey.Checked` and
`Pickles.Sideload.VerificationKey.Checked` as alias modules for the
in-circuit forms, to maintain a uniform "in-circuit types live under
`.Checked`" rule. With the 2-parameter approach, the in-circuit form
is just a saturation of the same type; PS's instance resolution
catches mixed-axis mistakes (`VerificationKey (FVar f) Boolean` etc.)
at the constraint level. The aliases would add a layer of indirection
with no type-safety payoff.

### Why the bundle is in `Sideload`, not `VerificationKey.SideLoaded`

The bundle pairs the VK descriptor with a kimchi `VerifierIndex` — a
runtime FFI artifact. Both halves are "side-loaded feature" concerns,
not pure VK data. The umbrella `Pickles.Sideload.*` already houses
the side-loaded feature's runtime machinery (`Sideload.Advice`,
`Sideload.FFI`); the VK descriptor and the bundle live there too.
This matches OCaml's `Pickles.Side_loaded.*` hierarchy.

### Why the bundle constructor is hidden

The two halves of `Bundle` must agree — the `vk`'s commitments must
match what `verifierIndex` describes. `mkBundle` enforces this by
deriving `vk` from `verifierIndex` via `VK.extractWrapVKComms`.
Hiding the constructor makes mismatched bundles unrepresentable.

### Why `HasSideLoadedVk` as a class

At parent-prove time the carrier holds `Bundle`s at side-loaded
slots; at compile time the carrier holds `SLVK.VerificationKey (F
StepField) Boolean` (the placeholder). `BuildSlotVkSources` walks
the carrier and feeds `exists` with a uniform `SLVK.VerificationKey
(F StepField) Boolean` value at every position. The
`HasSideLoadedVk.projectVk` method provides that uniform projection —
identity for the compile-time cell, `.vk` field access for the
prove-time bundle. The phase distinction is localized to the class;
no record-shape parameter propagates through other consumers.
