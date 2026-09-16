-- | The step statement in the field order the verifier fixes: the
-- | Lagrange MSM for `x_hat` consumes public-input fields
-- | left-to-right, so the layout is not free.
-- |
-- | Hence a newtype rather than the bare record — a record would pick
-- | up `RCircuitType`'s alphabetical field order, and the wire order is
-- | different. The `CircuitType` and `PublicInputCommit` instances
-- | delegate to the `Data.Tuple.Nested` shapes below, which spell the
-- | real order out; swapping the newtype for the record compiles and
-- | silently corrupts the encoding.
module Pickles.PackedStatement
  ( PackedStepPublicInput(..)
  -- Exported for `pickles-circuit-diffs`, which builds a
  -- `PackedStepPublicInput` from a flat input array.
  , PerProofTuple
  , StmtTuple
  , fromPackedTuple
  , toPackedTuple
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple3, Tuple6, tuple3, tuple6, uncurry3, uncurry6)
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Pickles.DeferredValues (UnfinalizedProof)
import Pickles.PublicInputCommit (class PublicInputCommit, LagrangeBaseLookup, ScalarMulResult, scalarMuls)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F, FVar, SizedF, Snarky, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Circuit.Kimchi (SplitField, Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (CurveParams)
import Type.Proxy (Proxy(..))

newtype PackedStepPublicInput (n :: Int) (dw :: Int) fv b = PackedStepPublicInput
  { proofState ::
      { unfinalizedProofs :: Vector n (UnfinalizedProof dw fv (Type2 (SplitField fv b)) b)
      , messagesForNextStepProof :: fv
      }
  , messagesForNextWrapProof :: Vector n fv
  }

-- | One per-proof page of the statement, in wire order.
type PerProofTuple dw fv b =
  Tuple6
    (Vector 5 (Type2 (SplitField fv b))) -- fq: cip, b, ztSrs, ztDs, perm
    fv -- digest: sponge_digest_before_evaluations
    (Vector 2 (SizedF 128 fv)) -- challenge: beta, gamma
    (Vector 3 (SizedF 128 fv)) -- scalar_challenge: alpha, zeta, xi
    (Vector dw (SizedF 128 fv)) -- bp_challenges
    b -- bool: should_finalize

-- | The whole statement in wire order: the `n` per-proof pages, the
-- | `messages_for_next_step_proof` digest, then the `n`
-- | `messages_for_next_wrap_proof` digests.
type StmtTuple n dw fv b =
  Tuple3
    (Vector n (PerProofTuple dw fv b))
    fv
    (Vector n fv)

-- | `StmtTuple` at the value representation, the form both instances
-- | hand to the generic field conversions.
type StmtTupleVal n dw f = StmtTuple n dw (F f) Boolean

toPackedTuple
  :: forall n dw fv b
   . PackedStepPublicInput n dw fv b
  -> StmtTuple n dw fv b
toPackedTuple (PackedStepPublicInput s) =
  tuple3
    (map perProofToTuple s.proofState.unfinalizedProofs)
    s.proofState.messagesForNextStepProof
    s.messagesForNextWrapProof
  where
  perProofToTuple up =
    let
      dv = up.deferredValues
      p = dv.plonk
    in
      tuple6
        (dv.combinedInnerProduct :< dv.b :< p.zetaToSrsLength :< p.zetaToDomainSize :< p.perm :< Vector.nil)
        up.spongeDigestBeforeEvaluations
        (p.beta :< p.gamma :< Vector.nil)
        (p.alpha :< p.zeta :< dv.xi :< Vector.nil)
        dv.bulletproofChallenges
        up.shouldFinalize

fromPackedTuple
  :: forall n dw fv b
   . StmtTuple n dw fv b
  -> PackedStepPublicInput n dw fv b
fromPackedTuple = uncurry3 \proofs mfnsp mfnwp ->
  PackedStepPublicInput
    { proofState:
        { unfinalizedProofs: map perProofFromTuple proofs
        , messagesForNextStepProof: mfnsp
        }
    , messagesForNextWrapProof: mfnwp
    }
  where
  perProofFromTuple = uncurry6 \fq digest ch sc bpc bool ->
    { deferredValues:
        { plonk:
            { alpha: sc !! unsafeFinite @3 0
            , beta: ch !! unsafeFinite @2 0
            , gamma: ch !! unsafeFinite @2 1
            , zeta: sc !! unsafeFinite @3 1
            , perm: fq !! unsafeFinite @5 4
            , zetaToSrsLength: fq !! unsafeFinite @5 2
            , zetaToDomainSize: fq !! unsafeFinite @5 3
            }
        , combinedInnerProduct: fq !! unsafeFinite @5 0
        , b: fq !! unsafeFinite @5 1
        , xi: sc !! unsafeFinite @3 2
        , bulletproofChallenges: bpc
        }
    , shouldFinalize: bool
    , spongeDigestBeforeEvaluations: digest
    }

instance
  ( PrimeField f
  , CircuitType f (StmtTupleVal n dw f) (StmtTuple n dw (FVar f) (BoolVar f))
  ) =>
  CircuitType f
    (PackedStepPublicInput n dw (F f) Boolean)
    (PackedStepPublicInput n dw (FVar f) (BoolVar f)) where
  sizeInFields pf _ = sizeInFields pf (Proxy @(StmtTupleVal n dw f))
  valueToFields x = valueToFields @f @(StmtTupleVal n dw f) (toPackedTuple x)
  fieldsToValue fs = fromPackedTuple (fieldsToValue @f @(StmtTupleVal n dw f) fs)
  varToFields x = varToFields @f @(StmtTupleVal n dw f) (toPackedTuple x)
  fieldsToVar fs = fromPackedTuple (fieldsToVar @f @(StmtTupleVal n dw f) fs)

instance
  ( PublicInputCommit (StmtTuple n dw (FVar f) (BoolVar f)) f
  ) =>
  PublicInputCommit (PackedStepPublicInput n dw (FVar f) (BoolVar f)) f where
  scalarMuls
    :: forall @stepChunks r
     . PrimeField f
    => Reflectable stepChunks Int
    => CurveParams f
    -> PackedStepPublicInput n dw (FVar f) (BoolVar f)
    -> LagrangeBaseLookup stepChunks f
    -> Int
    -> Snarky f (KimchiConstraint f) r (ScalarMulResult stepChunks f)
  scalarMuls params x lookup idx =
    scalarMuls @(StmtTuple n dw (FVar f) (BoolVar f)) @f params (toPackedTuple x) lookup idx
