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

import Control.Monad.Trans.Class (lift)
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PublicInputCommit (CorrectionMode, LagrangeBase)
import Pickles.Types (StepStatement, WrapIPARounds, WrapStatement)
import Pickles.Verify.Types (toStepDeferredValues)
import Pickles.Wrap.Advice (class WrapWitnessM, getEvals, getMessages, getOldBpChallenges, getOpeningProof, getStepAccs, getStepIOFields, getUnfinalizedProofs)
import Pickles.Wrap.FinalizeOtherProof (pow2PowMul, wrapFinalizeOtherProofCircuit)
import Pickles.Wrap.Verify (wrapVerify)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, UnChecked(..), assert_, const_, exists, fieldsToValue, label, not_, or_, sub_)
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
wrapCircuit
  :: forall @mpv @n @ds _l3 t m
   . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t m
  => WrapWitnessM mpv ds WrapIPARounds m Pallas.ScalarField
  => Reflectable mpv Int
  => Reflectable ds Int
  => Reflectable n Int
  => Add 1 _l3 ds
  => Compare 0 mpv LT
  => Compare mpv 3 LT
  => WrapParams Pallas.ScalarField
  -> WrapInputVar ds
  -> Snarky (KimchiConstraint Pallas.ScalarField) t m Unit
wrapCircuit params wrapStmt = label "wrap-circuit" do
  -- 1. Obtain private witness data via advisory monad
  UnChecked publicInput <- exists $ lift $ do
    fs <- getStepIOFields @mpv @ds @WrapIPARounds @m @Pallas.ScalarField unit
    pure $ UnChecked $ fieldsToValue @_ @(StepPublicInput n ds WrapIPARounds (F Pallas.ScalarField) Boolean) (map unwrap fs)
  evalsAll <- exists $ lift $ getEvals @mpv @ds @WrapIPARounds unit
  messages <- exists $ lift $ getMessages @mpv @ds @WrapIPARounds unit
  openingProof <- exists $ lift $ getOpeningProof @mpv @ds @WrapIPARounds unit
  -- UnChecked: OCaml's exists allocates raw fields without bit-range checks.
  -- The SizedF 128 scalar challenges inside UnfinalizedProof and oldBpChallenges
  -- would otherwise generate ~382 constraints each (unpack + assert high bits zero).
  -- The actual range checking happens later in the FOP via squeezeScalar.
  UnChecked unfinalizedProofs <- exists $ lift $ UnChecked <$> getUnfinalizedProofs @mpv @ds @WrapIPARounds @_ @Pallas.ScalarField unit
  _sgOld <- exists $ lift $ getStepAccs @mpv @ds @WrapIPARounds unit
  UnChecked oldBpChallenges <- exists $ lift $ UnChecked <$> getOldBpChallenges @mpv @ds @WrapIPARounds unit

  -- 2. Finalize each of mpv previous proofs
  -- OCaml: Vector.mapn [unfinalized_proofs; old_bp_chals; evals; wrap_domains]
  --        ~f:(fun [...] -> finalize_other_proof ...)
  let
    fopParams =
      { domain:
          { generator: const_ params.domain.generator
          , shifts: map const_ params.domain.shifts
          }
      , domainLog2: params.domainLog2
      , srsLengthLog2: params.srsLengthLog2
      , linearizationPoly: params.linearizationPoly
      , endo: params.endo
      }
  let
    wrapVanishingPoly z = do
      zetaToN <- pow2PowMul z params.domainLog2
      pure (zetaToN `sub_` const_ one)
  expandedChallengesAll <- for (Vector.zip unfinalizedProofs (Vector.zip evalsAll oldBpChallenges)) \(Tuple unfinalized (Tuple witness prevChallenges)) -> do
    { finalized, expandedChallenges } <-
      wrapFinalizeOtherProofCircuit fopParams wrapVanishingPoly
        { unfinalized, witness, prevChallenges: prevChallenges :< Vector.nil }
    -- Assert finalized || not shouldFinalize
    finalizedOrNotRequired <- or_ finalized (not_ unfinalized.shouldFinalize)
    assert_ finalizedOrNotRequired
    pure expandedChallenges

  -- 3. IVP + assertions (wrap_main.ml:78-135)
  let
    constPt { x: F x', y: F y' } = { x: const_ x', y: const_ y' }
    fullIvpInput =
      { publicInput
      -- TODO: pass real sgOld once oracle/transcript computation includes them
      , sgOld: Vector.nil
      , sgOldMask: Vector.nil
      , deferredValues: toStepDeferredValues wrapStmt.proofState.deferredValues
      , sigmaCommLast: constPt params.sigmaCommLast
      , columnComms:
          { index: map constPt params.columnComms.index
          , coeff: map constPt params.columnComms.coeff
          , sigma: map constPt params.columnComms.sigma
          }
      , wComm: messages.wComm
      , zComm: messages.zComm
      , tComm: messages.tComm
      , opening: openingProof
      }
    verifyInput =
      { spongeDigestBeforeEvaluations: wrapStmt.proofState.spongeDigestBeforeEvaluations
      , messagesForNextWrapProofDigest: wrapStmt.proofState.messagesForNextWrapProof
      , bulletproofChallenges: (toStepDeferredValues wrapStmt.proofState.deferredValues).bulletproofChallenges
      , newBpChallenges: expandedChallengesAll
      , sg: openingProof.sg
      }
  wrapVerify params fullIvpInput verifyInput
