-- | Packed Step Statement with OCaml-compatible field ordering.
-- |
-- | OCaml's `Spec.pack` serializes Per_proof fields in `to_data` order
-- | (composition_types.ml:1212), not alphabetical.  Since the Lagrange MSM
-- | for x_hat consumes fields left-to-right, the ordering must match.
-- |
-- | This newtype wraps the StepStatement record but delegates CircuitType
-- | and PublicInputCommit to a nested-tuple whose layout matches OCaml:
-- |
-- |   Per_proof → (fq5, digest, challenge2, scalarChal3, bpChals, bool)
-- |     fq order: cip, b, ztSrs, ztDs, perm
-- |
-- |   Statement → (Vector perProof, mfnsp, Vector mfnwp)
-- |
-- | Reference: composition_types.ml Per_proof.In_circuit.to_data (line 1212),
-- |            Statement.to_data (line 1344), Statement.spec (line 1370)
module Pickles.PackedStatement
  ( PackedStepPublicInput(..)
  , toPackedTuple
  , fromPackedTuple
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Pickles.PublicInputCommit (class PublicInputCommit, LagrangeBase, ScalarMulResult, scalarMuls)
import Pickles.Verify.Types (UnfinalizedProof)
import Snarky.Circuit.DSL (class CircuitM, class CircuitType, BoolVar, F, FVar, SizedF, Snarky, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Circuit.Kimchi (SplitField, Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (CurveParams)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Newtype
-------------------------------------------------------------------------------

newtype PackedStepPublicInput (n :: Int) (dw :: Int) fv b = PackedStepPublicInput
  { proofState ::
      { unfinalizedProofs :: Vector n (UnfinalizedProof dw fv (Type2 (SplitField fv b)) b)
      , messagesForNextStepProof :: fv
      }
  , messagesForNextWrapProof :: Vector n fv
  }

-------------------------------------------------------------------------------
-- | CircuitType instance
-------------------------------------------------------------------------------

type StmtTupleVal n dw f = StmtTuple n dw (F f) Boolean

instance
  ( PrimeField f
  , CircuitType f (StmtTupleVal n dw f) (StmtTuple n dw (FVar f) (BoolVar f))
  ) =>
  CircuitType f
    (PackedStepPublicInput n dw (F f) Boolean)
    (PackedStepPublicInput n dw (FVar f) (BoolVar f)) where
  valueToFields x = valueToFields @f @(StmtTupleVal n dw f) (toPackedTuple x)
  fieldsToValue fs = fromPackedTuple (fieldsToValue @f @(StmtTupleVal n dw f) fs)
  sizeInFields _ _ = sizeInFields (Proxy @f) (Proxy @(StmtTupleVal n dw f))
  varToFields x = varToFields @f @(StmtTupleVal n dw f) (toPackedTuple x)
  fieldsToVar fs = fromPackedTuple (fieldsToVar @f @(StmtTupleVal n dw f) fs)

-------------------------------------------------------------------------------
-- | PublicInputCommit instance
-------------------------------------------------------------------------------

instance
  ( PublicInputCommit (StmtTuple n dw (FVar f) (BoolVar f)) f
  ) =>
  PublicInputCommit (PackedStepPublicInput n dw (FVar f) (BoolVar f)) f where
  scalarMuls
    :: forall t m
     . CircuitM f (KimchiConstraint f) t m
    => CurveParams f
    -> PackedStepPublicInput n dw (FVar f) (BoolVar f)
    -> Array (LagrangeBase f)
    -> Snarky (KimchiConstraint f) t m (ScalarMulResult f)
  scalarMuls params x bases =
    scalarMuls @(StmtTuple n dw (FVar f) (BoolVar f)) @f params (toPackedTuple x) bases

-- Boilerplate

-------------------------------------------------------------------------------
-- | Tuple types matching OCaml layout
-------------------------------------------------------------------------------

type PerProofTuple dw fv b =
  Tuple (Vector 5 (Type2 (SplitField fv b))) -- [cip, b, ztSrs, ztDs, perm]
    ( Tuple fv -- sponge_digest
        ( Tuple (Vector 2 (SizedF 128 fv)) -- [beta, gamma]
            ( Tuple (Vector 3 (SizedF 128 fv)) -- [alpha, zeta, xi]
                ( Tuple (Vector dw (SizedF 128 fv)) -- bp_challenges
                    b
                )
            )
        )
    ) -- should_finalize

type StmtTuple n dw fv b =
  Tuple (Vector n (PerProofTuple dw fv b))
    (Tuple fv (Vector n fv))

-------------------------------------------------------------------------------
-- | Conversion (polymorphic in fv/b, works for both value and var level)
-------------------------------------------------------------------------------

toPackedTuple :: forall n dw fv b. PackedStepPublicInput n dw fv b -> StmtTuple n dw fv b
toPackedTuple (PackedStepPublicInput s) =
  Tuple
    (map ppToTuple s.proofState.unfinalizedProofs)
    (Tuple s.proofState.messagesForNextStepProof s.messagesForNextWrapProof)
  where
  ppToTuple up =
    let
      dv = up.deferredValues
      p = dv.plonk
    in
      Tuple (dv.combinedInnerProduct :< dv.b :< p.zetaToSrsLength :< p.zetaToDomainSize :< p.perm :< Vector.nil)
        ( Tuple up.spongeDigestBeforeEvaluations
            ( Tuple (p.beta :< p.gamma :< Vector.nil)
                ( Tuple (p.alpha :< p.zeta :< dv.xi :< Vector.nil)
                    (Tuple dv.bulletproofChallenges up.shouldFinalize)
                )
            )
        )

fromPackedTuple :: forall n dw fv b. StmtTuple n dw fv b -> PackedStepPublicInput n dw fv b
fromPackedTuple (Tuple proofs (Tuple mfnsp mfnwp)) =
  PackedStepPublicInput
    { proofState:
        { unfinalizedProofs: map ppFromTuple proofs
        , messagesForNextStepProof: mfnsp
        }
    , messagesForNextWrapProof: mfnwp
    }
  where
  ppFromTuple :: PerProofTuple dw fv b -> UnfinalizedProof dw fv (Type2 (SplitField fv b)) b
  ppFromTuple (Tuple fq (Tuple digest (Tuple ch (Tuple sc (Tuple bpc bool))))) =
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
