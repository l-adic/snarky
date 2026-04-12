-- | Type-level slot-list specs for `Pickles.Wrap.Main.wrapMain`.
-- |
-- | This module is the **closed-world enumeration layer** over the
-- | `PadSlots` / `HashSlots` / etc. type classes that wrap_main uses
-- | internally. Those classes express the abstract algebraic structure
-- | "a list of per-slot bp-challenge stacks, inducted over slot
-- | shape" — but in practice Pickles only ever instantiates that
-- | structure at `max_proofs_verified ∈ {0, 1, 2}`, so the classes
-- | are exercised at exactly 13 points in their polymorphic space
-- | (1 shape for N0, 3 for N1, 9 for N2).
-- |
-- | The type synonyms below name those 13 cases. Library users pick
-- | the one that matches their circuit's `max_proofs_verified` and
-- | slot widths:
-- |
-- | @
-- |   -- Trivial rule (transaction_snark.ml:4278 style)
-- |   wrapMain @branches @NoSlots config stmt
-- |
-- |   -- Step0's wrap (mpv=1, single slot width 1)
-- |   wrapMain @branches @(Slots1 1) config stmt
-- |
-- |   -- Blockchain snark (mpv=2, widths (0, 2))
-- |   wrapMain @branches @(Slots2 0 2) config stmt
-- | @
-- |
-- | All three synonyms expand to nested `Data.Functor.Product` +
-- | `Data.Const` forms, so the `PadSlots` class instances still see
-- | the `Product (Vector w) rest` / `Const Unit` shapes and dispatch
-- | accordingly. Readers of library code see the memorable names;
-- | the class machinery sees the underlying structure.
-- |
-- | The `a` parameter is the per-slot-stack element type. For the
-- | real wrap-prover use case it's always
-- | `Vector WrapIPARounds (FVar WrapField)` (one bp-challenge
-- | vector), but the type synonyms keep it polymorphic so they work
-- | with value-level `FVar` during circuit compilation and with the
-- | concrete `F WrapField` during witness generation.
module Pickles.Wrap.Slots
  ( NoSlots
  , Slots1
  , Slots2
  , noSlots
  , slots1
  , slots2
  ) where

import Prelude

import Data.Const (Const(..))
import Data.Functor.Product (Product, product)
import Data.Vector (Vector)

-- | The empty slot list (`max_proofs_verified = 0`). `Const Unit` is
-- | the nil functor — it wraps a single `Unit` value and ignores its
-- | element type parameter, matching "no slots means no element
-- | storage."
type NoSlots :: Type -> Type
type NoSlots = Const Unit

-- | A slot list with exactly one slot of width `w`
-- | (`max_proofs_verified = 1`).
type Slots1 :: Int -> Type -> Type
type Slots1 w = Product (Vector w) NoSlots

-- | A slot list with exactly two slots of widths `w0` and `w1`
-- | (`max_proofs_verified = 2`).
type Slots2 :: Int -> Int -> Type -> Type
type Slots2 w0 w1 = Product (Vector w0) (Slots1 w1)

-- | Smart constructor for `NoSlots`. Produces the single `Const unit`
-- | value that inhabits every `NoSlots a` type.
noSlots :: forall a. NoSlots a
noSlots = Const unit

-- | Smart constructor for `Slots1 w`. Takes the single slot's
-- | bp-challenge stack and terminates with `noSlots`.
slots1 :: forall w a. Vector w a -> Slots1 w a
slots1 v = product v noSlots

-- | Smart constructor for `Slots2 w0 w1`. Takes both slots' stacks
-- | in order (slot 0 first, slot 1 second).
slots2 :: forall w0 w1 a. Vector w0 a -> Vector w1 a -> Slots2 w0 w1 a
slots2 v0 v1 = product v0 (slots1 v1)
