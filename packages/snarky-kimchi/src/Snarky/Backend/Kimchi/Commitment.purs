-- | Polynomial-commitment shapes used by kimchi proofs.
-- |
-- | A kimchi polynomial commitment splits into
-- | `ceil(domain_size / SRS_max_poly_size)` curve-point chunks. The
-- | generic `ChunkedCommitment` container holds one such commitment;
-- | its parameter is the neutral `chunks` (used at all three pickles
-- | "chunk-count dimensions" — see the longer Pickles-internal note in
-- | the pickles consumer modules for the disambiguation).
-- |
-- | The IPA-rounds aliases capture the Pasta-cycle protocol constants
-- | (`Rounds.Step = 16`, `Rounds.Wrap = 15`) — they live here rather
-- | than in pickles because the proof-system FFI (`Snarky.Backend.Kimchi.Proof`)
-- | uses them in instance heads, and the kimchi proof system is the
-- | natural home for protocol-level constants of this kind.
module Snarky.Backend.Kimchi.Commitment
  ( StepIPARounds
  , WrapIPARounds
  , ChunkedCommitment(..)
  ) where

import Prelude ((<<<))

import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.Types (class CircuitType, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Type.Proxy (Proxy(..))

-- | IPA rounds in a Step proof (= log2 of Vesta SRS size = `Rounds.Step` = 16).
type StepIPARounds = 16

-- | IPA rounds in a Wrap proof (= log2 of Pallas SRS size = `Rounds.Wrap` = 15).
type WrapIPARounds = 15

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
