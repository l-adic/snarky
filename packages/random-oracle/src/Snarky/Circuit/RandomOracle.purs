-- | Circuit (checked) version of the Random Oracle.
-- |
-- | This module provides random oracle operations that work within
-- | the circuit/constraint system. Unlike the pure version, inputs
-- | must have statically known sizes.
module Snarky.Circuit.RandomOracle
  ( Digest(..)
  , class Hashable
  , toHashInput
  , class HashInput
  , hashInput
  , hashOf
  , hashVec
  , hash2
  , update
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (unsafeFinite)
import Data.Foldable (foldM)
import Data.Generic.Rep (class Generic)
import Data.Int (odd)
import Data.Maybe (fromJust)
import Data.Newtype (class Newtype)
import Data.Traversable (traverse)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField)
import Poseidon as Poseidon
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CheckedType, class CircuitM, class CircuitType, F(..), FVar, Snarky, add_, const_, genericCheck, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (poseidon)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)

-- | Initial state for the sponge: all zeros
initialState :: forall f. PrimeField f => Vector 3 (FVar f)
initialState = Vector.generate (const (const_ zero))

-- | Add a block of 2 elements to the sponge state (positions 0 and 1)
addBlock
  :: forall f
   . PrimeField f
  => Vector 3 (FVar f)
  -> Vector 2 (FVar f)
  -> Vector 3 (FVar f)
addBlock state block =
  let
    s0 = Vector.index state (unsafeFinite 0)
    s1 = Vector.index state (unsafeFinite 1)
    s2 = Vector.index state (unsafeFinite 2)
    b0 = Vector.index block (unsafeFinite 0)
    b1 = Vector.index block (unsafeFinite 1)
  in
    (s0 `add_` b0) Vector.:< (s1 `add_` b1) Vector.:< s2 Vector.:< Vector.nil

-- | Update the sponge state with a single block and permute.
-- |
-- | This is the core sponge operation: add block to rate positions, then permute.
updateBlock
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f)
  -> Vector 2 (FVar f)
  -> Snarky (KimchiConstraint f) t m (Vector 3 (FVar f))
updateBlock state block = do
  let stateWithBlock = addBlock state block
  poseidon stateWithBlock

newtype Digest f = Digest f

derive newtype instance Eq f => Eq (Digest f)
derive newtype instance Show f => Show (Digest f)
derive newtype instance Ord f => Ord (Digest f)

derive instance Generic (Digest f) _

derive instance Newtype (Digest f) _

instance CircuitType f (Digest (F f)) (Digest (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(Digest (F f))
  fieldsToVar = genericFieldsToVar @(Digest (F f))

instance CheckedType f c (Digest (FVar f)) where
  check = genericCheck

-- | Hash exactly 2 field elements.
-- |
-- | This is the most common case: hash(a, b).
hash2
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => FVar f
  -> FVar f
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
hash2 a b = do
  let
    block :: Vector 2 (FVar f)
    block = a Vector.:< b Vector.:< Vector.nil
  finalState <- updateBlock initialState block
  -- Squeeze from position 0 (standard sponge)
  pure $ Digest $ Vector.index finalState (unsafeFinite 0)

-- | Update state with a vector of inputs (must be even length for simplicity).
-- |
-- | The input vector is chunked into rate-sized blocks (2 elements each),
-- | and each block is absorbed with a permutation.
-- | For empty input, a single block of zeros is processed to match the
-- | pure implementation behavior.
update
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f)
  -> Array (FVar f)
  -> Snarky (KimchiConstraint f) t m (Vector 3 (FVar f))
update initState inputs = do
  let
    blocks :: Array (Vector 2 (FVar f))
    blocks =
      let
        n = Array.length inputs
        -- Pad to even length
        as = if odd n then inputs `Array.snoc` (const_ zero) else inputs
        -- Ensure at least one block for empty input (matching pure impl)
        as' = if n == 0 then [ const_ zero, const_ zero ] else as
      in
        unsafePartial fromJust $ traverse (Vector.toVector @2) (Vector.chunk 2 as')

  -- Fold over blocks, updating state with each
  foldM updateBlock initState blocks

-- | Hash a vector of field elements (must be even length).
-- |
-- | Example usage:
-- | ```
-- | result <- hashVec @4 inputs  -- hash 4 elements
-- | ```
hashVec
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Array (FVar f)
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
hashVec inputs = do
  finalState <- update initialState inputs
  -- Squeeze from position 0
  pure $ Digest $ Vector.index finalState (unsafeFinite 0)

--------------------------------------------------------------------------------
-- | Flatten a structured value into the field-element leaves that feed
-- | the hash — the analogue of Mina's `Random_oracle.Input` / `to_input`.
-- |
-- | Total and compositional: composites concatenate their children's
-- | inputs. `a` is the structure; `b` is its leaf field representation
-- | (`F f` out of circuit, `FVar f` in circuit). `a` determines `b`.
class Hashable a b | a -> b where
  toHashInput :: a -> Array b

-- | A field element is its own singleton input (the leaf base cases).
instance Hashable (F f) (F f) where
  toHashInput x = [ x ]

instance Hashable (FVar f) (FVar f) where
  toHashInput x = [ x ]

--------------------------------------------------------------------------------
-- | Hash a flat array of leaf field elements into a `Digest` — the
-- | analogue of `Random_oracle.hash`. Representation-specific: pure
-- | values hash directly, circuit variables hash inside `Snarky`.
class HashInput b h where
  hashInput :: Array b -> h

instance PoseidonField f => HashInput (F f) (Digest (F f)) where
  hashInput xs = Digest (F (Poseidon.hash (coerce xs)))

instance
  ( CircuitM f (KimchiConstraint f) t m
  , PoseidonField f
  ) =>
  HashInput (FVar f) (Snarky (KimchiConstraint f) t m (Digest (FVar f))) where
  hashInput = hashVec

-- | Hash a value directly: flatten it (`toHashInput`) then hash the
-- | leaves (`hashInput`). The non-`Maybe` counterpart of the merkle
-- | layer's `hashLeaf`.
hashOf :: forall a b h. Hashable a b => HashInput b h => a -> h
hashOf = hashInput <<< toHashInput