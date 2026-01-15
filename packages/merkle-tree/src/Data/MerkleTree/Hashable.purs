module Data.MerkleTree.Hashable
  ( class MerkleHashable
  , class MergeHash
  , merge
  , module RO
  , defaultHash
  , FreeHash(..)
  , hashCircuit
  , mergeCircuit
  ) where

import Prelude

import Control.Apply (lift2)
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Poseidon (class PoseidonField)
import Poseidon as Poseidon
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_)
import Snarky.Circuit.RandomOracle (Digest(..), hash2)
import Snarky.Circuit.RandomOracle (class Hashable, hash) as RO
import Snarky.Constraint.Kimchi (KimchiConstraint)

-- | Type class for merging two hashes into one.
-- | Used for computing internal node hashes in merkle trees.
class MergeHash hash where
  merge :: hash -> hash -> hash

instance PoseidonField f => MergeHash (Digest (F f)) where
  merge (Digest (F a)) (Digest (F b)) = Digest $ F $ Poseidon.hash [ a, b ]

instance
  ( CircuitM f (KimchiConstraint f) t m
  , PoseidonField f
  ) =>
  MergeHash (Snarky (KimchiConstraint f) t m (Digest (FVar f))) where
  merge a b = join $ lift2 hash2 (map (un Digest) a) (map (un Digest) b)

-- | The default/empty hash for a type
defaultHash :: forall @a hash. RO.Hashable a hash => hash
defaultHash = RO.hash @a @hash Nothing

-- | Combined constraint for merkle tree operations.
-- | Requires both hashing elements and merging hashes.
class (MergeHash hash, RO.Hashable a hash) <= MerkleHashable a hash

instance PoseidonField f => MerkleHashable (F f) (Digest (F f))

instance
  ( CircuitM f (KimchiConstraint f) t m
  , PoseidonField f
  ) =>
  MerkleHashable (FVar f) (Snarky (KimchiConstraint f) t m (Digest (FVar f)))

-- | Free hash type for lazy/symbolic hash computation
data FreeHash a
  = HashValue a
  | HashEmpty
  | Merge (FreeHash a) (FreeHash a)

derive instance Eq a => Eq (FreeHash a)
derive instance Functor FreeHash

-- | Circuit-level hash function for a single field element
hashCircuit
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Maybe (FVar f)
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
hashCircuit = case _ of
  Nothing -> hash2 (const_ zero) (const_ zero)
  Just a -> hash2 a (const_ zero)

-- | Circuit-level merge of two digests
mergeCircuit
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Digest (FVar f)
  -> Digest (FVar f)
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
mergeCircuit (Digest a) (Digest b) = hash2 a b
