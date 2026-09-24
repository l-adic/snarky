-- | The `Params` and `Output` shared by the step and wrap
-- | `finalize_other_proof` circuits. Each side keeps its own input
-- | record, because the shifted-scalar representation differs.
module Pickles.FinalizeOtherProof
  ( Params
  , Output
  , DomainMode(..)
  , pow2PowSquare
  ) where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Vector (Vector)
import Pickles.DeferredValues (BulletproofChallenges)
import Pickles.Linearization.Types (LinearizationPoly)
import Snarky.Circuit.DSL (class BasicSystem, BoolVar, FVar, Snarky, square_)
import Snarky.Curves.Class (class PrimeField)

-- | `x^(2^n)` by repeated squaring, emitting exactly `n` Square
-- | constraints.
pow2PowSquare
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> Int
  -> Snarky f c r (FVar f)
pow2PowSquare x n = go x n
  where
  go acc i
    | i <= 0 = pure acc
    | otherwise = do
        sq <- square_ acc
        go sq (i - 1)

-- | How `finalize_other_proof` resolves the prev proof's domain.
-- | `KnownDomainsMode` selects among the compile-time candidates in
-- | `params.domains`; `SideLoadedMode` ignores them and selects over
-- | the `[0..16]` log2 universe, from a domain log2 carried in the
-- | public input.
data DomainMode
  = KnownDomainsMode
  | SideLoadedMode

-- | What `finalize_other_proof` knows at compile time, from the
-- | verification key.
-- |
-- | - `domains`: one `{ generator, log2 }` per step-domain size the
-- |   prev proof could have been proved over: one per branch of the
-- |   system that produced it. Duplicates are harmless; the selection
-- |   deduplicates.
-- | - `shifts`: one vector of kimchi permutation shifts for all of
-- |   them; the candidate domains are required to share their shifts.
type Params :: Type -> Row Type -> Type
type Params f r =
  { domains :: NonEmptyArray { generator :: FVar f, log2 :: Int }
  , shifts :: Vector 7 (FVar f)
  , srsLengthLog2 :: Int
  , zkRows :: Int
  , endo :: f -- ^ EndoScalar coefficient
  , linearizationPoly :: LinearizationPoly f
  , domainMode :: DomainMode
  | r
  }

-- | The outcome of each deferred-value check, with `finalized` their
-- | conjunction, alongside the prev proof's bulletproof challenges as
-- | 128-bit values and expanded through the endomorphism.
type Output d f =
  { finalized :: BoolVar f
  , xiCorrect :: BoolVar f
  , bCorrect :: BoolVar f
  , cipCorrect :: BoolVar f
  , plonkOk :: BoolVar f
  , challenges :: BulletproofChallenges d (FVar f)
  , expandedChallenges :: Vector d (FVar f)
  }
