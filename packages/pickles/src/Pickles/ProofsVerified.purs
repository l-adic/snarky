-- | The {N0, N1, N2} enum used as both proof-count and side-loaded
-- | wrap-domain tags. Mirrors OCaml `Pickles_base.Proofs_verified.t`.
module Pickles.ProofsVerified
  ( ProofsVerified(..)
  , ProofsVerifiedCount
  , proofsVerifiedToBoolVec
  , boolVecToProofsVerified
  ) where

import Prelude

import Data.Enum (class BoundedEnum, class Enum)
import Data.Enum.Generic (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector

-- | Number of proofs a Pickles VK verifies; capped at 2 for the
-- | side-loaded protocol (`Width.Max = Nat.N2`).
data ProofsVerified = N0 | N1 | N2

-- | Type-level cardinality of `ProofsVerified` (= 3 for {N0, N1, N2}).
-- | Used to size one-hot bool vectors and per-domain lookup tables
-- | indexed by a side-loaded VK's `actualWrapDomainSize`.
type ProofsVerifiedCount = 3

derive instance Eq ProofsVerified
derive instance Ord ProofsVerified
derive instance Generic ProofsVerified _

instance Show ProofsVerified where
  show = genericShow

instance Bounded ProofsVerified where
  bottom = N0
  top = N2

instance Enum ProofsVerified where
  succ = genericSucc
  pred = genericPred

instance BoundedEnum ProofsVerified where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

-- | Boolean one-hot vector.
proofsVerifiedToBoolVec :: ProofsVerified -> Vector ProofsVerifiedCount Boolean
proofsVerifiedToBoolVec = case _ of
  N0 -> true :< false :< false :< Vector.nil
  N1 -> false :< true :< false :< Vector.nil
  N2 -> false :< false :< true :< Vector.nil

-- | Inverse of `proofsVerifiedToBoolVec`. Defaults to `N0` for the
-- | zero-bit input and for malformed (non-one-hot) inputs.
boolVecToProofsVerified :: Vector ProofsVerifiedCount Boolean -> ProofsVerified
boolVecToProofsVerified v =
  let
    { head: b0, tail: t1 } = Vector.uncons v
    { head: b1, tail: t2 } = Vector.uncons t1
    { head: b2 } = Vector.uncons t2
  in
    if b0 then N0 else if b1 then N1 else if b2 then N2 else N0
