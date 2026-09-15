-- | Type-level slot-list specs for `Pickles.Wrap.Main.wrapMain`, plus
-- | the class machinery that inducts over them.
-- |
-- | # Two layers
-- |
-- | **Algebraic structure** (classes `PadSlots` / `HashSlots`): the
-- | abstract "list of per-slot bp-challenge stacks, inducted over
-- | slot shape." Each class has a `Const Unit` nil instance and a
-- | `Product (Vector w) rest` cons instance. The class methods —
-- | `slotWidthsOf`, `padAllSlots`, etc. — recurse through the slot
-- | list, pattern-matching on its structural shape.
-- |
-- | **Closed-world enumeration** (type synonyms `NoSlots` / `Slots1` /
-- | `Slots2` and smart constructors): the 13 instantiations Pickles
-- | actually uses (1 for N0, 3 for N1, 9 for N2), named so library
-- | users can pick the one matching their circuit's
-- | `max_proofs_verified` and slot widths. The synonyms expand to
-- | the same `Product` / `Const Unit` forms the classes pattern-
-- | match on, so instance resolution sees them as equivalent.
-- |
-- | # Usage
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
-- | # Note on the shared element type
-- |
-- | `Product f g a = Product (Tuple (f a) (g a))` applies both factors
-- | to the same `a` — this is the functor-product's correctness
-- | invariant and it matches reality: every slot in the wrap
-- | accumulator stores the same thing (one bp-challenge vector of
-- | length `WrapIPARounds`). Element-type homogeneity across slots
-- | is enforced by the type, not by a convention.
module Pickles.Wrap.Slots
  ( -- * Type-level slot specs
    NoSlots
  , Slots1
  , Slots2
  -- * Class machinery for structural induction
  , class PadSlots
  , slotWidthsOf
  ) where

import Prelude

import Data.Const (Const)
import Data.Functor.Product (Product)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Prim.Int (class Add)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Type-level slot specs
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- PadSlots class: structural induction over slot lists
--------------------------------------------------------------------------------

-- | Structural traversal of a slot list. Provides the widths of each
-- | slot (for sponge-state indexing) and the padded form of the slot
-- | data (for the FOP loop's `prevChallenges` input).
-- |
-- | The fundep `| slots -> mpv` infers the slot count from the
-- | tuple depth. Element-type polymorphism on `padAllSlots` is via
-- | method-level `forall a`, avoiding the class-level `a` fundep
-- | hole that a tuple-based encoding would create at the nil case.
class PadSlots (slots :: Type -> Type) (mpv :: Int) | slots -> mpv where
  -- | Per-slot widths as a homogeneous `Vector mpv Int`. Each entry
  -- | is the corresponding slot's `max_local_max_proofs_verified`.
  -- | Used to index into `Pickles.Wrap.MessageHash.dummyPaddingSpongeStates`
  -- | for pre-computed sponge-state lookup.
  slotWidthsOf :: Proxy slots -> Vector mpv Int

-- Nil case: empty slot list (`NoSlots`), mpv=0.
instance PadSlots NoSlots 0 where
  slotWidthsOf _ = Vector.nil

-- Cons case: head slot of width `w`, tail `rest :: Type -> Type`
-- (either another `Product (Vector w') rest'` or `NoSlots`). The
-- recursive `PadSlots rest restLen` constraint dispatches on the
-- tail's shape and eventually terminates at `NoSlots`.
instance
  ( Reflectable w Int
  , PadSlots rest restLen
  , Add restLen 1 mpv
  , Reflectable mpv Int
  ) =>
  PadSlots (Product (Vector w) rest) mpv where
  slotWidthsOf _ =
    reflectType (Proxy :: Proxy w) :< slotWidthsOf (Proxy :: Proxy rest)

