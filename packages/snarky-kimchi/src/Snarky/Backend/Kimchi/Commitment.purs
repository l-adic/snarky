-- | Generic polynomial-commitment container used by kimchi proofs.
-- |
-- | A kimchi polynomial commitment splits into
-- | `ceil(domain_size / SRS_max_poly_size)` curve-point chunks. The
-- | generic `ChunkedCommitment` container holds one such commitment;
-- | its `chunks` parameter is dimension-agnostic at this layer (callers
-- | instantiate it to the appropriate per-dimension chunk count).
module Snarky.Backend.Kimchi.Commitment
  ( ChunkedCommitment(..)
  ) where

import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Prelude ((<<<))
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.Types (class CircuitType, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Type.Proxy (Proxy(..))

-- | Single polynomial-commitment as a vector of `chunks` chunks. Wraps
-- | `Vector chunks pt` so that the two axes — outer "which commitment"
-- | vs inner "which chunk of one commitment" — stay distinguishable at
-- | use sites. The runtime representation is identical to the
-- | underlying Vector; consumers use `Data.Newtype` combinators
-- | (`over`, `under`, `over2`, `un`, `coerce`) instead of manual
-- | wrap/unwrap chains.
newtype ChunkedCommitment :: Int -> Type -> Type
newtype ChunkedCommitment chunks pt = ChunkedCommitment (Vector chunks pt)

derive instance Newtype (ChunkedCommitment chunks pt) _

instance
  ( CircuitType f a var
  , Reflectable chunks Int
  ) =>
  CircuitType f (ChunkedCommitment chunks a) (ChunkedCommitment chunks var) where
  sizeInFields pf _ = sizeInFields pf (Proxy @(Vector chunks a))
  valueToFields = valueToFields @f @(Vector chunks a) <<< unwrap
  fieldsToValue = wrap <<< fieldsToValue @f @(Vector chunks a)
  varToFields = varToFields @f @(Vector chunks a) <<< unwrap
  fieldsToVar = wrap <<< fieldsToVar @f @(Vector chunks a)

instance CheckedType f c (Vector chunks var) => CheckedType f c (ChunkedCommitment chunks var) where
  check = check <<< unwrap
