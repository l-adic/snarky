-- | Packed Step Statement with OCaml-compatible field ordering.
-- |
-- | OCaml's `Spec.pack` serializes `Per_proof` fields in `to_data` order
-- | (composition_types.ml:1212), not alphabetical. Since the Lagrange MSM
-- | for `x_hat` consumes fields left-to-right, the ordering must match.
-- |
-- | This newtype wraps the Step statement record but its `CircuitType` and
-- | `PublicInputCommit` instances delegate through nested `Data.Tuple.Nested`
-- | shapes that mirror OCaml's per-proof and statement layouts:
-- |
-- |   Per_proof to_data:
-- |     [ fq (5)         — combined_inner_product, b, ztSrs, ztDs, perm
-- |     ; digest         — sponge_digest_before_evaluations
-- |     ; challenge (2)  — beta, gamma
-- |     ; scalar_chal (3)— alpha, zeta, xi
-- |     ; bp_challenges  — bulletproof_challenges
-- |     ; bool           — should_finalize
-- |     ]
-- |
-- |   Statement to_data:
-- |     [ Vector n per_proof
-- |     ; messages_for_next_step_proof
-- |     ; Vector n messages_for_next_wrap_proof
-- |     ]
-- |
-- | Reference: composition_types.ml `Per_proof.In_circuit.to_data` (line 1212),
-- |            `Statement.to_data` (line 1344).
module Pickles.PackedStatement
  ( PackedStepPublicInput(..)
  -- Re-exported for circuit-diffs test wrappers that construct
  -- PackedStepPublicInput from a flat input array. Production code should
  -- prefer the record constructor; the tuple helpers exist purely as a
  -- convenience to keep test wrappers small.
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
import Pickles.PublicInputCommit (class PublicInputCommit, LagrangeBaseLookup, ScalarMulResult, scalarMuls)
import Pickles.Verify.Types (UnfinalizedProof)
import Snarky.Circuit.DSL (class CircuitM, class CircuitType, BoolVar, F, FVar, SizedF, Snarky, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Circuit.Kimchi (SplitField, Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (CurveParams)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | The packed statement newtype
-------------------------------------------------------------------------------

newtype PackedStepPublicInput (n :: Int) (dw :: Int) fv b = PackedStepPublicInput
  { proofState ::
      { unfinalizedProofs :: Vector n (UnfinalizedProof dw fv (Type2 (SplitField fv b)) b)
      , messagesForNextStepProof :: fv
      }
  , messagesForNextWrapProof :: Vector n fv
  }

-------------------------------------------------------------------------------
-- | Internal tuple shapes mirroring OCaml `to_data` order
-------------------------------------------------------------------------------

-- | One per-proof "page" in OCaml `to_data` order. Each component matches
-- | the corresponding `Spec.T.Vector` entry in `Per_proof.In_circuit.spec`.
type PerProofTuple dw fv b =
  Tuple6
    (Vector 5 (Type2 (SplitField fv b))) -- fq: cip, b, ztSrs, ztDs, perm
    fv -- digest: sponge_digest_before_evaluations
    (Vector 2 (SizedF 128 fv)) -- challenge: beta, gamma
    (Vector 3 (SizedF 128 fv)) -- scalar_challenge: alpha, zeta, xi
    (Vector dw (SizedF 128 fv)) -- bp_challenges
    b -- bool: should_finalize

-- | Whole-statement tuple in OCaml `Statement.to_data` order:
-- | (Vector mpv per_proof, msg_for_next_step, Vector mpv msg_for_next_wrap).
type StmtTuple n dw fv b =
  Tuple3
    (Vector n (PerProofTuple dw fv b))
    fv
    (Vector n fv)

-- | Convenience alias used by both instances to drive
-- | `genericValueToFields` / `genericFieldsToValue` etc.
type StmtTupleVal n dw f = StmtTuple n dw (F f) Boolean

-------------------------------------------------------------------------------
-- | Internal conversions (NOT exported — clients construct PackedStepPublicInput
-- | directly via the record constructor and never see the tuple shape).
-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
-- | CircuitType instance — delegates to the tuple, which gives OCaml ordering.
-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
-- | PublicInputCommit instance — same delegation pattern.
-------------------------------------------------------------------------------

instance
  ( PublicInputCommit (StmtTuple n dw (FVar f) (BoolVar f)) f
  ) =>
  PublicInputCommit (PackedStepPublicInput n dw (FVar f) (BoolVar f)) f where
  scalarMuls
    :: forall @stepChunks t m
     . CircuitM f (KimchiConstraint f) t m
    => Reflectable stepChunks Int
    => CurveParams f
    -> PackedStepPublicInput n dw (FVar f) (BoolVar f)
    -> LagrangeBaseLookup stepChunks f
    -> Int
    -> Snarky (KimchiConstraint f) t m (ScalarMulResult stepChunks f)
  scalarMuls params x lookup idx =
    scalarMuls @(StmtTuple n dw (FVar f) (BoolVar f)) @f params (toPackedTuple x) lookup idx
