-- | Step circuit combinator for Pickles recursion.
module Pickles.Step.Circuit
  ( AppCircuit
  , AppCircuitInput
  , AppCircuitOutput
  , module Pickles.Types
  , StepParams
  , stepCircuit
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.Linearization.FFI (class LinearizationFFI)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.ProofWitness (ProofWitness)
import Pickles.PublicInputCommit (CorrectionMode)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.Advice (class StepWitnessM, getFopProofStates, getMessages, getOpeningProof, getPrevChallenges, getProofWitnesses, getWrapPublicInputFields, getWrapVerifierIndex)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofOutput, FinalizeOtherProofParams, finalizeOtherProofCircuit)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Types (StepInput, StepStatement)
import Pickles.Verify (verify)
import Pickles.Verify.Types (BulletproofChallenges, UnfinalizedProof)
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, and_, assertEq, assert_, const_, exists, label, not_, or_)
import Snarky.Circuit.Kimchi (GroupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField, fromInt)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)
import Snarky.Types.Shifted (SplitField, Type1, Type2)
import Type.Proxy (Proxy)

type AppCircuitInput n input prevInput =
  { appInput :: input, previousProofInputs :: Vector n prevInput }

type AppCircuitOutput n output aux f =
  { mustVerify :: Vector n (BoolVar f), publicOutput :: output, auxiliaryOutput :: aux }

type AppCircuit n input prevInput output aux f c t m =
  AppCircuitInput n input prevInput -> Snarky c t m (AppCircuitOutput n output aux f)

-- | Combined parameters for the Step circuit.
-- | Merges FinalizeOtherProofParams (FOP) with IncrementallyVerifyProofParams (IVP).
-- | Both are row-polymorphic, so StepParams satisfies both via structural subtyping.
type StepParams :: Type -> Type
type StepParams f =
  { curveParams :: CurveParams f
  , lagrangeComms :: Array (AffinePoint (F f))
  , blindingH :: AffinePoint (F f)
  , groupMapParams :: GroupMapParams f
  , correctionMode :: CorrectionMode
  , useOptSponge :: Boolean
  , domain :: { generator :: f, shifts :: Vector 7 f }
  , domainLog2 :: Int
  , srsLengthLog2 :: Int
  , linearizationPoly :: LinearizationPoly f
  , endo :: f
  }

finalizeOtherProof
  :: forall _d d _n n f f' g t m r2
   . Add 1 _d d => Add 1 _n n => PrimeField f => FieldSizeInBits f 255
  => PoseidonField f => HasEndo f f' => CircuitM f (KimchiConstraint f) t m
  => LinearizationFFI f g => Reflectable d Int
  => FinalizeOtherProofParams f r2
  -> { mask :: Vector n (BoolVar f), prevChallenges :: Vector n (Vector d (FVar f)), domainLog2Var :: FVar f }
  -> UnfinalizedProof d (FVar f) (Type1 (FVar f)) (BoolVar f)
  -> ProofWitness (FVar f)
  -> Snarky (KimchiConstraint f) t m (FinalizeOtherProofOutput d f)
finalizeOtherProof params shared unfinalized witness =
  finalizeOtherProofCircuit StepOtherField.fopShiftOps params
    { unfinalized, witness, mask: shared.mask, prevChallenges: shared.prevChallenges, domainLog2Var: shared.domainLog2Var }

hashMessagesForNextStepProofStub
  :: forall n d f c t m. PrimeField f => CircuitM f c t m
  => Vector n (BulletproofChallenges d (FVar f)) -> Snarky c t m (FVar f)
hashMessagesForNextStepProofStub _ = pure $ const_ zero

computeMessageForNextWrapProofStub
  :: forall d f c t m. PrimeField f => CircuitM f c t m
  => BulletproofChallenges d (FVar f) -> Snarky c t m (FVar f)
computeMessageForNextWrapProofStub _ = pure $ const_ zero

-- | The Step circuit combinator.
-- |
-- | Type parameters:
-- | - `n`: number of previous proofs to verify (0 for base case, 1 for inductive)
-- | - `ds`: Step IPA rounds (for WrapStatement type in fieldsToValue)
-- | - `dw`: Wrap IPA rounds
-- | - `nPublic`: number of public input fields in the Wrap proof
stepCircuit
  :: forall _n n nPublic ds _dw dw input prevInput output aux t m
   . Add 1 _dw dw
  => Add 1 _n n
  => CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
  => StepWitnessM n dw m Vesta.ScalarField
  => Reflectable n Int
  => Reflectable dw Int
  => Reflectable ds Int
  => Reflectable nPublic Int
  => Proxy ds
  -> Proxy nPublic
  -> StepParams Vesta.ScalarField
  -> AppCircuit n input prevInput output aux Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
  -> StepInput n input prevInput ds dw (FVar Vesta.ScalarField) (Type2 (SplitField (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField))) (BoolVar Vesta.ScalarField)
  -> Snarky (KimchiConstraint Vesta.ScalarField) t m (StepStatement n ds dw (FVar Vesta.ScalarField) (Type2 (SplitField (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField))) (BoolVar Vesta.ScalarField))
stepCircuit _ _ params appCircuit { appInput, previousProofInputs, unfinalizedProofs } = label "step-circuit" do
  { mustVerify } <- appCircuit { appInput, previousProofInputs }

  proofWitnesses <- exists $ lift $ getProofWitnesses @_ @dw unit
  prevChallenges <- exists $ lift $ getPrevChallenges @_ @dw unit
  fopProofStates <- exists $ lift $ getFopProofStates @_ @dw unit
  wrapVk <- exists $ lift $ getWrapVerifierIndex @n @dw unit
  messages <- exists $ lift $ getMessages @n @dw unit
  openingProofs <- exists $ lift $ getOpeningProof @n @dw unit
  wrapPublicInputs <- exists $ lift $ do
    fieldArrays <- getWrapPublicInputFields @n @dw unit
    pure $ map (\fs -> unsafePartial fromJust $ Vector.toVector @nPublic fs) fieldArrays

  let
    shared =
      { mask: mustVerify
      , prevChallenges
      , domainLog2Var: const_ (fromInt params.domainLog2)
      }
    proofsWithData = Vector.zip unfinalizedProofs
      (Vector.zip fopProofStates
        (Vector.zip proofWitnesses
          (Vector.zip messages
            (Vector.zip openingProofs
              (Vector.zip wrapPublicInputs mustVerify)))))

  challengesAndDigests <- for proofsWithData \(Tuple unfinalized (Tuple fopState (Tuple witness (Tuple msgs (Tuple opening (Tuple wrapPI mustVerifyFlag)))))) -> do
    let shouldFinalize = unfinalized.shouldFinalize

    assertEq shouldFinalize mustVerifyFlag
    { finalized, challenges } <- finalizeOtherProof params shared fopState witness

    let
      ivpInput =
        { publicInput: wrapPI
        , sgOld: Vector.nil
        , sigmaCommLast: wrapVk.sigmaCommLast
        , columnComms: wrapVk.columnComms
        , deferredValues: unfinalized.deferredValues
        , wComm: msgs.wComm
        , zComm: msgs.zComm
        , tComm: msgs.tComm
        , opening
        }
      isBaseCase = not_ mustVerifyFlag
    verified <- evalSpongeM initialSpongeCircuit $
      verify @PallasG StepOtherField.ipaScalarOps params ivpInput isBaseCase
        unfinalized.spongeDigestBeforeEvaluations

    verifiedAndFinalized <- verified `and_` finalized
    passOrDummy <- verifiedAndFinalized `or_` (not_ shouldFinalize)
    assert_ passOrDummy

    messageForWrap <- computeMessageForNextWrapProofStub challenges
    pure { challenges, messageForWrap }

  let
    allChallenges = map _.challenges challengesAndDigests
    messagesForNextWrapProof = map _.messageForWrap challengesAndDigests

  messagesForNextStepProof <- hashMessagesForNextStepProofStub allChallenges

  pure
    { proofState: { unfinalizedProofs, messagesForNextStepProof }
    , messagesForNextWrapProof
    }
