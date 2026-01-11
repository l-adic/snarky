module Test.Data.MerkleTree.Helpers where

import Prelude

import Data.Maybe (Maybe(..))
import Data.MerkleTree (class Hashable, class MergeHash, class MerkleHashable)
import Poseidon.Class (class PoseidonField, hash)

-- Newtype for Poseidon hash to avoid orphan instance
newtype PoseidonHash f = PoseidonHash f

derive newtype instance Eq f => Eq (PoseidonHash f)
derive newtype instance Show f => Show (PoseidonHash f)

-- Instance of MergeHash for PoseidonHash
instance PoseidonField f => MergeHash (PoseidonHash f) where
  merge (PoseidonHash left) (PoseidonHash right) = PoseidonHash (hash [ left, right ])

-- Instance of Hashable for PoseidonHash
instance PoseidonField f => Hashable f (PoseidonHash f) where
  hash = case _ of
    Nothing -> PoseidonHash (hash [ zero ])
    Just x -> PoseidonHash (hash [ x ])

instance PoseidonField f => MerkleHashable f (PoseidonHash f)