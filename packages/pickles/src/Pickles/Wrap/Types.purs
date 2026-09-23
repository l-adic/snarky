-- | The types the wrap circuit allocates: its own public input and its
-- | view of the step proof's proof state. Built by `Pickles.Prove.Wrap`,
-- | read by `Pickles.Wrap.Main` and `Pickles.Verify`.
module Pickles.Wrap.Types
  ( IvpBaseline
  , PrevProofState(..)
  , StatementPacked(..)
  ) where

import Data.Foldable (traverse_)
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple2, Tuple3, Tuple7, tuple2, tuple3, tuple7, uncurry2, uncurry3, uncurry7)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Types (PerProofUnfinalized, WrapIPARounds)
import Snarky.Circuit.DSL (BoolVar, F, FVar, UnChecked)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Curves.Class (class FieldSizeInBits)
import Type.Proxy (Proxy(..))

-- | The wrap IVP's MSM base count at one chunk, excluding the `sg_old`
-- | of each previous proof: the commitments, sigma commitments and the
-- | rest. The full count is `mpv + IvpBaseline`.
type IvpBaseline = 45

-- | The step proof state the wrap circuit allocates as one witness:
-- | `mpv` unfinalized proofs with Type2-shifted scalars, then the
-- | messages-for-next-step digest. That field order is the allocation
-- | order, and the `CircuitType` instance below pins it.
newtype PrevProofState (mpv :: Int) sf f b = PrevProofState
  { unfinalizedProofs :: Vector mpv (PerProofUnfinalized WrapIPARounds sf f b)
  , messagesForNextStepProof :: f
  }

instance
  ( CircuitType f sf sfvar
  , CircuitType f b bvar
  , FieldSizeInBits f m
  , Reflectable mpv Int
  ) =>
  CircuitType f
    (PrevProofState mpv sf (F f) b)
    (PrevProofState mpv sfvar (FVar f) bvar) where
  sizeInFields pf _ = genericSizeInFields pf
    (Proxy @(Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sf (F f) b)) (F f)))
  valueToFields (PrevProofState r) = genericValueToFields
    (tuple2 r.unfinalizedProofs r.messagesForNextStepProof)
  fieldsToValue fs =
    let
      tup :: Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sf (F f) b)) (F f)
      tup = genericFieldsToValue fs
    in
      uncurry2
        ( \unfinalizedProofs messagesForNextStepProof ->
            PrevProofState { unfinalizedProofs, messagesForNextStepProof }
        )
        tup
  varToFields (PrevProofState r) = genericVarToFields
    @(Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sf (F f) b)) (F f))
    (tuple2 r.unfinalizedProofs r.messagesForNextStepProof)
  fieldsToVar fs =
    let
      tup :: Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sfvar (FVar f) bvar)) (FVar f)
      tup = genericFieldsToVar
        @(Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sf (F f) b)) (F f))
        fs
    in
      uncurry2
        ( \unfinalizedProofs messagesForNextStepProof ->
            PrevProofState { unfinalizedProofs, messagesForNextStepProof }
        )
        tup

instance
  ( CheckedType f c (PerProofUnfinalized WrapIPARounds sfvar fvar bvar)
  , CheckedType f c fvar
  ) =>
  CheckedType f c (PrevProofState mpv sfvar fvar bvar) where
  check (PrevProofState r) = check (tuple2 r.unfinalizedProofs r.messagesForNextStepProof)

-- | The wrap circuit's public input, in allocation layout. The field
-- | order below is the wire order:
-- |
-- |   5 fp fields, 2 challenges, 3 scalar challenges, 3 digests,
-- |   `d` bullet-proof challenges, 1 branch-data index.
-- |
-- | Challenges carry `UnChecked` because nothing range-checks them at
-- | allocation; the consumer that needs the 128-bit invariant
-- | re-establishes it, as `Scalar_challenge.to_field_checked` does at
-- | endo-expansion time. The 5 fp fields stay `sf` (`Type1 (FVar f)` in
-- | circuit); digests and branch data are plain `f`. None of them gets
-- | an allocation check.
newtype StatementPacked :: Int -> Type -> Type -> Type -> Type
newtype StatementPacked d sf f b = StatementPacked
  { -- combined_inner_product, b, zetaToSrsLength, zetaToDomainSize, perm
    fpFields :: Vector 5 sf
  -- beta, gamma
  , challenges :: Vector 2 (UnChecked (SizedF 128 f))
  -- alpha, zeta, xi
  , scalarChallenges :: Vector 3 (UnChecked (SizedF 128 f))
  -- sponge_digest, msg_for_next_wrap, msg_for_next_step
  , digests :: Vector 3 f
  , bulletproofChallenges :: Vector d (UnChecked (SizedF 128 f))
  , branchData :: f
  -- Allocated to hold the wire slots open, never read: the feature
  -- flags are all constant `false`, and the lookup pair is one flag
  -- plus one scalar challenge for a lookup configuration that is off.
  -- Dropping them would shorten the public input.
  , featureFlags :: Vector 8 f
  , lookupOptFlag :: f
  , lookupOptScalarChallenge :: f
  }

-- | The wire order of `StatementPacked`, as a tuple the `CircuitType`
-- | instance delegates through. The feature-flag and lookup tail is
-- | grouped into a `Tuple3` so the whole thing fits in `Tuple7`.
type StatementPackedTuple d sf x =
  Tuple7
    (Vector 5 sf)
    (Vector 2 (UnChecked (SizedF 128 x)))
    (Vector 3 (UnChecked (SizedF 128 x)))
    (Vector 3 x)
    (Vector d (UnChecked (SizedF 128 x)))
    x
    (Tuple3 (Vector 8 x) x x)

instance
  ( CircuitType f sf sfvar
  , FieldSizeInBits f m
  , Reflectable d Int
  ) =>
  CircuitType f
    (StatementPacked d sf (F f) Boolean)
    (StatementPacked d sfvar (FVar f) (BoolVar f)) where
  sizeInFields pf _ = genericSizeInFields pf
    (Proxy @(StatementPackedTuple d sf (F f)))
  valueToFields (StatementPacked r) = genericValueToFields
    ( tuple7 r.fpFields r.challenges r.scalarChallenges r.digests r.bulletproofChallenges r.branchData
        (tuple3 r.featureFlags r.lookupOptFlag r.lookupOptScalarChallenge)
    )
  fieldsToValue fs =
    let
      tup :: StatementPackedTuple d sf (F f)
      tup = genericFieldsToValue fs
    in
      uncurry7
        ( \fpFields challenges scalarChallenges digests bulletproofChallenges branchData tail3 ->
            uncurry3
              ( \featureFlags lookupOptFlag lookupOptScalarChallenge ->
                  StatementPacked
                    { fpFields
                    , challenges
                    , scalarChallenges
                    , digests
                    , bulletproofChallenges
                    , branchData
                    , featureFlags
                    , lookupOptFlag
                    , lookupOptScalarChallenge
                    }
              )
              tail3
        )
        tup
  varToFields (StatementPacked r) = genericVarToFields
    @(StatementPackedTuple d sf (F f))
    ( tuple7 r.fpFields r.challenges r.scalarChallenges r.digests r.bulletproofChallenges r.branchData
        (tuple3 r.featureFlags r.lookupOptFlag r.lookupOptScalarChallenge)
    )
  fieldsToVar fs =
    let
      tup :: StatementPackedTuple d sfvar (FVar f)
      tup = genericFieldsToVar @(StatementPackedTuple d sf (F f)) fs
    in
      uncurry7
        ( \fpFields challenges scalarChallenges digests bulletproofChallenges branchData tail3 ->
            uncurry3
              ( \featureFlags lookupOptFlag lookupOptScalarChallenge ->
                  StatementPacked
                    { fpFields
                    , challenges
                    , scalarChallenges
                    , digests
                    , bulletproofChallenges
                    , branchData
                    , featureFlags
                    , lookupOptFlag
                    , lookupOptScalarChallenge
                    }
              )
              tail3
        )
        tup

instance
  ( CheckedType f c sfvar
  , CheckedType f c fvar
  ) =>
  CheckedType f c (StatementPacked d sfvar fvar bvar) where
  check (StatementPacked r) =
    -- Only the fp fields check; every other field is `UnChecked` or a
    -- plain `f`. The reverse is load-bearing: the checks run on `perm`
    -- first and `combined_inner_product` last, and that order fixes
    -- which public-input variables end up in which copy cycle.
    traverse_ check (Vector.reverse r.fpFields)
