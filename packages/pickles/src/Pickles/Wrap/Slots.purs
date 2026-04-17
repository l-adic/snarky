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
  -- * Smart constructors for value-level slots
  , noSlots
  , slots1
  , slots2
  -- * Class machinery for structural induction
  , class PadSlots
  , slotWidthsOf
  , padAllSlots
  , replicateSlots
  ) where

import Prelude

import Data.Const (Const(..))
import Data.Functor.Product (Product, product)
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Types (PaddedLength)
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
-- Smart constructors
--------------------------------------------------------------------------------

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

  -- | Pad each slot's bp-challenge stack to `PaddedLength = 2` by
  -- | front-padding with the `dummy` element, and collect the
  -- | results into a homogeneous outer `Vector mpv`. Matches
  -- | OCaml's `Wrap_hack.Checked.pad_challenges` applied per-slot.
  -- |
  -- | After this call, downstream code operates on a plain
  -- | `Vector mpv (Vector PaddedLength a)` and no longer needs
  -- | class dispatch for per-slot iteration.
  padAllSlots
    :: forall a
     . a
    -> slots a
    -> Vector mpv (Vector PaddedLength a)

  -- | Build a `slots a` populated with `seed` in every per-slot vector
  -- | position. The shape (per-slot widths) is determined by the
  -- | instance — the seed value is broadcast.
  -- |
  -- | Used by `zeroWrapAdvice` to construct an mpv-polymorphic
  -- | placeholder for the `oldBpChals` field of `WrapAdvice`. Mirrors
  -- | the structural layout of `padAllSlots` but skips the per-slot
  -- | dummy padding (the result is the unpadded `slots a`, not a
  -- | padded `Vector mpv (Vector PaddedLength a)`).
  replicateSlots
    :: forall a
     . a
    -> slots a

-- Nil case: empty slot list (`NoSlots`), mpv=0. The `a` is truly
-- phantom here — the method signature quantifies over it at the
-- method level, and `Const Unit a` ignores `a` by definition.
instance PadSlots NoSlots 0 where
  slotWidthsOf _ = Vector.nil
  padAllSlots _ _ = Vector.nil
  replicateSlots _ = noSlots

-- Cons case: head slot of width `w`, tail `rest :: Type -> Type`
-- (either another `Product (Vector w') rest'` or `NoSlots`). The
-- recursive `PadSlots rest restLen` constraint dispatches on the
-- tail's shape and eventually terminates at `NoSlots`.
instance
  ( Reflectable w Int
  , Add pad w PaddedLength
  , Reflectable pad Int
  , PadSlots rest restLen
  , Add restLen 1 mpv
  , Reflectable mpv Int
  ) =>
  PadSlots (Product (Vector w) rest) mpv where
  slotWidthsOf _ =
    reflectType (Proxy :: Proxy w) :< slotWidthsOf (Proxy :: Proxy rest)
  padAllSlots dummy p =
    let
      Tuple headSlot restSlot = unwrap p
    in
      padSlotDummy dummy headSlot :< padAllSlots dummy restSlot
  replicateSlots seed =
    product (Vector.replicate seed) (replicateSlots seed)

-- | Pad a single slot's vector to `PaddedLength` by prepending
-- | `(PaddedLength - w)` copies of the dummy. The `Add pad w
-- | PaddedLength` + `Reflectable pad Int` constraints come from
-- | the Cons instance's context and give us the runtime padding
-- | length.
-- |
-- | Unexported because the class's `padAllSlots` is the only
-- | intended user.
padSlotDummy
  :: forall w pad a
   . Reflectable pad Int
  => Add pad w PaddedLength
  => a
  -> Vector w a
  -> Vector PaddedLength a
padSlotDummy dummy slot =
  let
    padding :: Vector pad a
    padding = Vector.replicate dummy
  in
    Vector.append padding slot

