module Data.MerkleTree.Hashable
  ( class MerkleHashable
  , class MergeHash
  , merge
  , class Hashable
  , hash
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
import Snarky.Constraint.Kimchi (KimchiConstraint)

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

class MergeHash hash <= Hashable a hash where
  hash :: Maybe a -> hash

instance PoseidonField f => Hashable (F f) (Digest (F f)) where
  hash = case _ of
    Nothing -> Digest $ F $ Poseidon.hash []
    Just (F a) -> Digest $ F $ Poseidon.hash [ a ]

instance
  ( CircuitM f (KimchiConstraint f) t m
  , PoseidonField f
  ) =>
  Hashable (FVar f) (Snarky (KimchiConstraint f) t m (Digest (FVar f))) where
  hash = case _ of
    Nothing -> hash2 (const_ zero) (const_ zero)
    Just a -> hash2 a (const_ zero)

defaultHash :: forall @a hash. Hashable a hash => hash
defaultHash = hash @a @hash Nothing

class (MergeHash hash, Hashable a hash) <= MerkleHashable a hash

instance PoseidonField f => MerkleHashable (F f) (Digest (F f))

instance
  ( CircuitM f (KimchiConstraint f) t m
  , PoseidonField f
  ) =>
  MerkleHashable (FVar f) (Snarky (KimchiConstraint f) t m (Digest (FVar f)))

-- Free hash type
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