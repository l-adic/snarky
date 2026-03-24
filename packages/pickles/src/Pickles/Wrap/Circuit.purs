-- | Wrap circuit: verifies a Step proof via IPA and finalizes deferred values.
-- |
-- | This circuit runs two verification steps:
-- | 1. For each of `mpv` previous proofs: `finalizeOtherProof` + assert finalized
-- | 2. `verify` (incrementallyVerifyProof) — checks the IPA opening proof
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
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PublicInputCommit (CorrectionMode)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Types (StepStatement, WrapIPARounds, WrapStatement)
import Pickles.Verify (verify)
import Pickles.Verify.Types (toStepDeferredValues)
import Pickles.Wrap.Advice (class WrapWitnessM, getEvals, getMessages, getOldBpChallenges, getOpeningProof, getStepAccs, getStepIOFields, getUnfinalizedProofs)
import Pickles.Wrap.FinalizeOtherProof (wrapFinalizeOtherProofCircuit)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofCircuit)
import Pickles.Wrap.OtherField as WrapOtherField
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, UnChecked(..), assert_, const_, equals_, exists, false_, fieldsToValue, label, not_, or_)
import Snarky.Circuit.Kimchi (GroupMapParams, SplitField, Type1, Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)
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
  , lagrangeComms :: Array (AffinePoint (F f))
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
  expandedChallengesAll <- for (Vector.zip unfinalizedProofs (Vector.zip evalsAll oldBpChallenges)) \(Tuple unfinalized (Tuple witness prevChallenges)) -> do
    { finalized, expandedChallenges } <-
      wrapFinalizeOtherProofCircuit params
        { unfinalized, witness, prevChallenges: prevChallenges :< Vector.nil }
    -- Assert finalized || not shouldFinalize
    finalizedOrNotRequired <- or_ finalized (not_ unfinalized.shouldFinalize)
    assert_ finalizedOrNotRequired
    pure expandedChallenges

  -- 3. Verify the Step proof's IPA opening (uses public input deferred values)
  -- In the Wrap circuit, the Step VK is a compile-time constant (wrap_main.ml:209
  -- Inner_curve.constant). We wrap with constPt to match the FVar leaf type.
  let
    constPt { x: F x', y: F y' } = { x: const_ x', y: const_ y' }
    fullIvpInput =
      { publicInput
      -- TODO: pass real sgOld once oracle/transcript computation includes them
      , sgOld: Vector.nil
      , deferredValues: toStepDeferredValues wrapStmt.proofState.deferredValues
      -- Step VK data (constant in Wrap circuit)
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
  success <- evalSpongeM initialSpongeCircuit $
    verify @VestaG WrapOtherField.ipaScalarOps params fullIvpInput false_
      wrapStmt.proofState.spongeDigestBeforeEvaluations Nothing
  assert_ success

  -- 4. Compute and assert messagesForNextWrapProof hash
  -- TODO: use expandedChallengesAll (all mpv sets) instead of single + dummies
  let expandedChallenges = Vector.head expandedChallengesAll
  computedDigest <- evalSpongeM initialSpongeCircuit $
    hashMessagesForNextWrapProofCircuit
      { sg: openingProof.sg
      , expandedChallenges
      , dummyChallenges: dummyIpaChallenges.wrapExpanded
      }
  assert_ =<< equals_ computedDigest wrapStmt.proofState.messagesForNextWrapProof
