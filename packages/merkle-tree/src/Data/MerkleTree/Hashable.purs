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

import Data.Maybe (Maybe(..))

class MergeHash hash where
  merge :: hash -> hash -> hash

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