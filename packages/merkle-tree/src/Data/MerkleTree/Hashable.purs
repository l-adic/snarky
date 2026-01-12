module Data.MerkleTree.Hashable
  ( class MerkleHashable
  , class MergeHash
  , merge
  , class Hashable
  , hash
  , defaultHash
  , FreeHash(..)
  ) where

import Prelude

import Control.Apply (lift2)
import Data.Maybe (Maybe(..))
import Poseidon (class PoseidonField)
import Poseidon as Poseidon
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky)
import Snarky.Circuit.RandomOracle (hash2)
import Snarky.Constraint.Kimchi (KimchiConstraint)

class MergeHash hash where
  merge :: hash -> hash -> hash

instance PoseidonField f => MergeHash (F f) where
  merge (F a) (F b) = F $ Poseidon.hash [ a, b ]

instance
  ( CircuitM f (KimchiConstraint f) t m
  , PoseidonField f
  ) =>
  MergeHash (Snarky (KimchiConstraint f) t m (FVar f)) where
  merge a b = join $ lift2 hash2 a b

class MergeHash hash <= Hashable a hash where
  hash :: Maybe a -> hash

defaultHash :: forall @a hash. Hashable a hash => hash
defaultHash = hash @a @hash Nothing

class (MergeHash hash, Hashable a hash) <= MerkleHashable a hash

-- Free hash type
data FreeHash a
  = HashValue a
  | HashEmpty
  | Merge (FreeHash a) (FreeHash a)

derive instance Eq a => Eq (FreeHash a)
derive instance Functor FreeHash