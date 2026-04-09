-- | Wrap circuit: verifies a Step proof via IPA and finalizes deferred values.
-- |
-- | This circuit runs two verification steps:
-- | 1. For each of `mpv` previous proofs: `finalizeOtherProof` + assert finalized
-- | 2. `wrapVerify` — IVP + 4 assertions (wrap_main.ml:78-135)
-- |
-- | The finalize and IVP subcircuits operate on SEPARATE inputs:
-- | - IVP uses the current Step proof's deferred values (cross-field Fp→Fq)
-- | - Finalize uses its own consistently-computed deferred values (same-field Fq)
-- |
-- | Reference: mina/src/lib/pickles/wrap_main.ml
module Pickles.Wrap.Circuit
  ( WrapInput
  , WrapInputVar
  , StepPublicInput
  , WrapParams
  , wrapCircuit
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PublicInputCommit (CorrectionMode, LagrangeBase)
import Pickles.Types (StepStatement, WrapStatement)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, label)
import Snarky.Circuit.Kimchi (GroupMapParams, SplitField, Type1, Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)

-- | Public input for the Wrap circuit (value level).
type WrapInput :: Int -> Type
type WrapInput ds = WrapStatement ds (F Pallas.ScalarField) (Type1 (F Pallas.ScalarField)) Boolean

-- | Public input for the Wrap circuit (variable level).
type WrapInputVar :: Int -> Type
type WrapInputVar ds = WrapStatement ds (FVar Pallas.ScalarField) (Type1 (FVar Pallas.ScalarField)) (BoolVar Pallas.ScalarField)

-- | The Step proof's public input type as seen by the Wrap verifier for x_hat.
type StepPublicInput :: Int -> Int -> Int -> Type -> Type -> Type
type StepPublicInput n ds dw fv b =
  StepStatement n ds dw fv (Type2 (SplitField fv b)) b

-- | Combined parameters for the Wrap circuit.
type WrapParams :: Type -> Type
type WrapParams f =
  { -- IVP params
    curveParams :: CurveParams f
  , lagrangeComms :: Array (LagrangeBase f)
  , blindingH :: AffinePoint (F f)
  , sigmaCommLast :: AffinePoint (F f)
  , columnComms ::
      { index :: Vector 6 (AffinePoint (F f))
      , coeff :: Vector 15 (AffinePoint (F f))
      , sigma :: Vector 6 (AffinePoint (F f))
      }
  , indexDigest :: f
  , groupMapParams :: GroupMapParams f
  -- Finalize params
  , domain :: { generator :: f, shifts :: Vector 7 f }
  , domainLog2 :: Int
  , srsLengthLog2 :: Int
  , linearizationPoly :: LinearizationPoly f
  -- Shared
  , endo :: f
  , correctionMode :: CorrectionMode
  , useOptSponge :: Boolean
  }

-- | The Wrap circuit: finalizes deferred values and verifies IPA opening.
-- |
-- | Type parameters:
-- | - `mpv`: max_proofs_verified (always 2 in Pickles)
-- | - `n`: number of Step proof branches (currently 1)
-- | - `ds`: Step IPA rounds
-- | TODO(phase7): retarget against the new Pickles.Wrap.Advice methods
-- |
-- | The previous body called `getStepIOFields` / `getUnfinalizedProofs` /
-- | `getOldBpChallenges` etc., which no longer exist on the rewritten
-- | WrapWitnessM. Phase 4 disables this body so the package compiles; the
-- | sub-circuit will be either re-targeted at the new advice methods or
-- | deprecated (it's only used by `Test.Pickles.WrapE2E` and a single
-- | TestContext satisfiability check, both of which Phase 7 deals with).
wrapCircuit
  :: forall @mpv @n @ds _l3 t m
   . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
  => Reflectable mpv Int
  => Reflectable ds Int
  => Reflectable n Int
  => Add 1 _l3 ds
  => Compare 0 mpv LT
  => Compare mpv 3 LT
  => WrapParams Pallas.ScalarField
  -> WrapInputVar ds
  -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
wrapCircuit _params _wrapStmt = label "wrap-circuit" do
  pure unit
