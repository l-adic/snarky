-- | Verification of one previous proof inside the step circuit:
-- | finalize its deferred values, recompute its
-- | `messages_for_next_step_proof` digest, incrementally verify its wrap
-- | proof, and combine the three into one boolean.
module Pickles.Step.VerifyOne
  ( VerifyOneInput
  , VerifyOneResult
  , verifyOne
  ) where

import Prelude

import Data.Fin (getFinite) as Data.Fin
import Data.FoldableWithIndex (forWithIndex_)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.DeferredValues (BranchData)
import Pickles.Field (StepField)
import Pickles.FinalizeOtherProof (Params) as FOP
import Pickles.IncrementallyVerifyProof (IncrementallyVerifyProofParams, incrementallyVerifyProof, packStatement)
import Pickles.IncrementallyVerifyProof.FqSpongeTranscript (ivpTrace)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.FinalizeOtherProof (finalizeOtherProofCircuit)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofOpt)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Types (ChunkedCommitment, ChunkedEvals, StepIPARounds, WrapIPARounds, WrapVkChunks)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (Bool(..), BoolVar, FVar, Snarky, and_, assertEq, const_, if_, label, not_, or_)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (SplitField, Type1(..), Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Everything `verifyOne` reads for one previous proof: that proof's
-- | witness, the unfinalized proof the step circuit carries for it, the
-- | wrap VK it is checked against, and the masks.
type VerifyOneInput n wrapVkChunks tCommLen d tickD sf fv bv =
  { -- The previous proof's statement, as the field list its own
    -- `varToFields` produces.
    appStateFields :: Array fv
  -- The wrap proof's commitments and opening. `tCommLen` is
  -- `7 * wrapVkChunks`, flattened.
  , wComm :: Vector 15 (ChunkedCommitment wrapVkChunks (AffinePoint fv))
  , zComm :: ChunkedCommitment wrapVkChunks (AffinePoint fv)
  , tComm :: Vector tCommLen (AffinePoint fv)
  , lr :: Vector d { l :: AffinePoint fv, r :: AffinePoint fv }
  , z1 :: sf
  , z2 :: sf
  , delta :: AffinePoint fv
  , sg :: AffinePoint fv
  -- The wrap proof's own deferred values, finalized here.
  , proofState ::
      { plonk ::
          { alpha :: SizedF 128 fv
          , beta :: SizedF 128 fv
          , gamma :: SizedF 128 fv
          , zeta :: SizedF 128 fv
          , perm :: Type1 fv
          , zetaToSrsLength :: Type1 fv
          , zetaToDomainSize :: Type1 fv
          }
      , combinedInnerProduct :: Type1 fv
      , b :: Type1 fv
      , xi :: SizedF 128 fv
      , bulletproofChallenges :: Vector tickD (SizedF 128 fv)
      , spongeDigest :: fv
      }
  , chunkedEvals :: ChunkedEvals fv
  -- Carried over from the proofs this one itself verified.
  , prevChallenges :: Vector n (Vector tickD fv)
  , prevSgs :: Vector n (AffinePoint fv)
  , unfinalized ::
      { deferredValues ::
          { plonk ::
              { alpha :: SizedF 128 fv
              , beta :: SizedF 128 fv
              , gamma :: SizedF 128 fv
              , zeta :: SizedF 128 fv
              , perm :: sf
              , zetaToSrsLength :: sf
              , zetaToDomainSize :: sf
              }
          , combinedInnerProduct :: sf
          , b :: sf
          , xi :: SizedF 128 fv
          , bulletproofChallenges :: Vector d (SizedF 128 fv)
          }
      , shouldFinalize :: bv
      , claimedDigest :: fv
      }
  , messagesForNextWrapProof :: fv
  , mustVerify :: bv
  -- Read by `packStatement` into the wrap public input.
  , branchData :: BranchData fv fv
  -- The proofs-verified mask, trimmed to this slot's width.
  , proofMask :: Vector n bv
  -- The wrap VK the previous proof is verified against. Its
  -- commitments are chunked at `wrapVkChunks`, the chunk count of the
  -- proof being verified.
  , vkComms ::
      { sigma :: Vector 6 (ChunkedCommitment wrapVkChunks (AffinePoint fv))
      , sigmaLast :: ChunkedCommitment wrapVkChunks (AffinePoint fv)
      , coeff :: Vector 15 (ChunkedCommitment wrapVkChunks (AffinePoint fv))
      , index :: Vector 6 (ChunkedCommitment wrapVkChunks (AffinePoint fv))
      }
  -- `prevSgs` widened to `Pickles.Types.PaddedLength`, dummies first.
  , sgOld :: Vector 2 (AffinePoint fv)
  }

type VerifyOneResult tickD fv =
  { challenges :: Vector tickD (SizedF 128 fv) -- as squeezed
  , expandedChallenges :: Vector tickD fv -- the same, through the endo
  , result :: BoolVar StepField
  }

-- | The previous proof's bulletproof challenges, and a verdict that is
-- | true when the proof both verifies and finalizes, or when
-- | `mustVerify` is false.
-- |
-- | Specialized to the step field. The wrap VK is one chunk
-- | (`Pickles.Types.WrapVkChunks`), so the chunked-base layout is
-- | constant here — `tCommLen = 7`, `nonSgBases = 45`,
-- | `totalBases = 47`. The layout itself lives in
-- | `incrementallyVerifyProof`, which stays generic because the wrap
-- | side calls it at `stepChunks`, where chunking is real.
verifyOne
  :: forall nd ndPred n r r1
   . PrimeField StepField
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Reflectable nd Int
  => FOP.Params nd StepField r1
  -> VerifyOneInput n WrapVkChunks 7 WrapIPARounds StepIPARounds (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (FVar StepField) (BoolVar StepField)
  -> IncrementallyVerifyProofParams WrapVkChunks StepField ()
  -> Snarky StepField (KimchiConstraint StepField) r (VerifyOneResult StepIPARounds (FVar StepField))
verifyOne fopParams input ivpParams = do
  label "step1_assert_finalize" $ assertEq input.unfinalized.shouldFinalize input.mustVerify

  let ps = input.proofState
  { finalized, challenges, expandedChallenges, xiCorrect, bCorrect, cipCorrect, plonkOk } <- label "step2_fop" $ finalizeOtherProofCircuit StepOtherField.fopShiftOps fopParams
    { unfinalized:
        { deferredValues:
            { plonk: ps.plonk
            , combinedInnerProduct: ps.combinedInnerProduct
            , b: ps.b
            , xi: ps.xi
            , bulletproofChallenges: ps.bulletproofChallenges
            }
        , shouldFinalize: coerce (const_ one :: FVar StepField)
        , spongeDigestBeforeEvaluations: ps.spongeDigest
        }
    , chunkedEvals: input.chunkedEvals
    , mask: input.proofMask
    , prevChallenges: input.prevChallenges
    , domainLog2Var: input.branchData.domainLog2
    }

  -- Each FOP sub-check traced separately, to localize a downstream
  -- failure.
  ivpTrace "diag.fop.xiCorrect" (coerce xiCorrect)
  ivpTrace "diag.fop.bCorrect" (coerce bCorrect)
  ivpTrace "diag.fop.cipCorrect" (coerce cipCorrect)
  ivpTrace "diag.fop.plonkOk" (coerce plonkOk)
  ivpTrace "diag.fop.finalized" (coerce finalized)

  -- The message hash takes the unpadded `prevSgs`, not `sgOld`.
  let
    msgHashProofs = Vector.zipWith
      (\mask (Tuple sg rawChals) -> { sg, rawChallenges: rawChals, mask })
      input.proofMask
      (Vector.zipWith Tuple input.prevSgs input.prevChallenges)

  { digest: messagesForNextStepProof, spongeAfterIndex } <-
    hashMessagesForNextStepProofOpt
      { vkComms: input.vkComms
      , appStateFields: input.appStateFields
      , proofs: msgHashProofs
      }

  let
    statement =
      { proofState:
          { deferredValues:
              { plonk: input.proofState.plonk
              , combinedInnerProduct: input.proofState.combinedInnerProduct
              , xi: input.proofState.xi
              , bulletproofChallenges: input.proofState.bulletproofChallenges
              , b: input.proofState.b
              , branchData: input.branchData { proofsVerifiedMask = map coerce input.branchData.proofsVerifiedMask }
              }
          , spongeDigestBeforeEvaluations: input.proofState.spongeDigest
          , messagesForNextWrapProof: input.messagesForNextWrapProof
          }
      , messagesForNextStepProof
      }
    publicInput = packStatement statement

  -- The reconstructed wrap public input, traced element by element at
  -- its packed positions, for comparison against `tock_pi`.
  let
    Tuple fpFieldsVec (Tuple chalsVec (Tuple scalarChalsVec (Tuple digestsVec (Tuple bpChalsVec packedBranchData)))) = publicInput
  forWithIndex_ fpFieldsVec \fi (Type1 v) -> do
    let i = Data.Fin.getFinite fi
    ivpTrace ("diag.packed_pi." <> show i) v
  -- beta, gamma
  forWithIndex_ chalsVec \fi s -> do
    let i = Data.Fin.getFinite fi + 5
    ivpTrace ("diag.packed_pi." <> show i) (SizedF.toField s)
  -- alpha, zeta, xi
  forWithIndex_ scalarChalsVec \fi s -> do
    let i = Data.Fin.getFinite fi + 7
    ivpTrace ("diag.packed_pi." <> show i) (SizedF.toField s)
  -- spongeDigest, msgWrap, msgStep
  forWithIndex_ digestsVec \fi v -> do
    let i = Data.Fin.getFinite fi + 10
    ivpTrace ("diag.packed_pi." <> show i) v
  -- bulletproof challenges
  forWithIndex_ bpChalsVec \fi s -> do
    let i = Data.Fin.getFinite fi + 13
    ivpTrace ("diag.packed_pi." <> show i) (SizedF.toField s)
  ivpTrace "diag.packed_pi.28" (SizedF.toField packedBranchData)

  let
    ivpParams' = ivpParams

    ivpInput =
      { publicInput
      , sgOld: input.sgOld
      , sgOldMask: Nothing
      , sigmaCommLast: input.vkComms.sigmaLast
      , columnComms:
          { index: input.vkComms.index
          , coeff: input.vkComms.coeff
          , sigma: input.vkComms.sigma
          }
      , deferredValues: input.unfinalized.deferredValues
      , wComm: input.wComm
      , zComm: input.zComm
      , tComm: input.tComm
      , opening:
          { delta: input.delta
          , sg: input.sg
          , lr: input.lr
          , z1: input.z1
          , z2: input.z2
          }
      }

  output <- label "step6_ivp" $ evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @PallasG StepOtherField.ipaScalarOps ivpParams' ivpInput (Just spongeAfterIndex)

  ivpTrace "diag.ivp.success" (coerce output.success)

  label "step7_assert_digest" $
    assertEq input.unfinalized.claimedDigest output.spongeDigestBeforeEvaluations

  -- In the base case the expected challenge is replaced by the claimed
  -- one, which makes the assertion vacuous.
  let isBaseCase = not_ input.mustVerify
  label "step8_assert_bp" $
    forWithIndex_ (Vector.zip input.unfinalized.deferredValues.bulletproofChallenges output.bulletproofChallenges) \i (Tuple c1 c2) -> do
      let idx = Data.Fin.getFinite i
      c2' <- label ("bp_assert_iter_" <> show idx <> "_if") $ if_ isBaseCase c1 c2
      label ("bp_assert_iter_" <> show idx <> "_eq") $ assertEq c1 c2'

  result <- label "step9_final" do
    verifiedAndFinalized <- and_ output.success finalized
    or_ verifiedAndFinalized (not_ input.mustVerify)

  pure { challenges, expandedChallenges, result }
