-- | The {N0, N1, N2} enum, used both as a proof count and as a
-- | side-loaded wrap-domain tag.
module Pickles.ProofsVerified
  ( ProofsVerified(..)
  , ProofsVerifiedCount
  , allPossibleDomainLog2s
  , wrapDomainShifts
  , proofsVerifiedToBoolVec
  , boolVecToProofsVerified
  ) where

import Prelude

import Data.Enum (class BoundedEnum, class Enum)
import Data.Enum.Generic (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Fin (Finite, getFinite, reflectFinite)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Field (WrapField)
import Pickles.Linearization.FFI (domainShifts)

-- | Number of proofs a Pickles VK verifies; capped at 2 for the
-- | side-loaded protocol (`Width.Max = Nat.N2`).
data ProofsVerified = N0 | N1 | N2

-- | Cardinality of `ProofsVerified`, at the type level. It sizes the
-- | one-hot bool vectors and the per-domain tables indexed by a
-- | side-loaded VK's `actualWrapDomainSize`.
type ProofsVerifiedCount = 3

-- | Every wrap domain's log2, indexed by `proofs_verified`: OCaml's
-- | `Wrap_verifier.all_possible_domains`. The `Finite 16` bound is
-- | `1 + WrapIPARounds`, since a wrap domain is at most the wrap SRS
-- | size `2^WrapIPARounds`.
allPossibleDomainLog2s :: Vector ProofsVerifiedCount (Finite 16)
allPossibleDomainLog2s =
  reflectFinite @13 :< reflectFinite @14 :< reflectFinite @15 :< Vector.nil

-- | The permutation shifts `k_0..k_6` of every wrap domain in
-- | `allPossibleDomainLog2s`. kimchi's shifts for the three sizes
-- | coincide, so one set serves whichever domain a circuit selects.
wrapDomainShifts :: Vector 7 WrapField
wrapDomainShifts =
  domainShifts @WrapField (getFinite (Vector.head allPossibleDomainLog2s))

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
