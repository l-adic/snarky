-- | Step main verify_one: full verification of one previous proof.
-- |
-- | Combines FOP + message hash (opt_sponge) + IVP + assertions.
-- | Matches OCaml step_main.ml:17-148 verify_one.
-- |
-- | Reference: mina/src/lib/crypto/pickles/step_main.ml
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
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Field (StepField)
import Pickles.FinalizeOtherProof (Params) as FOP
import Pickles.IncrementallyVerifyProof (IncrementallyVerifyProofParams, incrementallyVerifyProof, ivpTrace, packStatement)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.FinalizeOtherProof (finalizeOtherProofCircuit)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofOpt)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Types (StepIPARounds, WrapIPARounds)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, and_, assertEq, const_, if_, label, not_, or_)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (SplitField, Type1(..), Type2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Input to verify_one. All fields from Per_proof_witness + unfinalized + extras.
-- | Specialized to StepField (Vesta scalar field = Fp).
type VerifyOneInput n wrapVkChunks tCommLen d tickD sf fv bv =
  { -- Per_proof_witness.app_state (flattened via CircuitType upstream).
    -- For Input-mode rules with a single `FVar f` this is `[x]`; for
    -- multi-field inputs it's the full field-list produced by the
    -- input type's `varToFields`.
    appStateFields :: Array fv
  -- Per_proof_witness.wrap_proof. `tCommLen = 7 * wrapVkChunks` (flat).
  , wComm :: Vector 15 (Vector wrapVkChunks (AffinePoint fv))
  , zComm :: Vector wrapVkChunks (AffinePoint fv)
  , tComm :: Vector tCommLen (AffinePoint fv)
  , lr :: Vector d { l :: AffinePoint fv, r :: AffinePoint fv }
  , z1 :: sf
  , z2 :: sf
  , delta :: AffinePoint fv
  , sg :: AffinePoint fv
  -- Per_proof_witness.proof_state (Wrap deferred values used by FOP)
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
  -- Per_proof_witness.prev_proof_evals
  , allEvals ::
      { ftEval1 :: fv
      , publicEvals :: { zeta :: fv, omegaTimesZeta :: fv }
      , witnessEvals :: Vector 15 { zeta :: fv, omegaTimesZeta :: fv }
      , coeffEvals :: Vector 15 { zeta :: fv, omegaTimesZeta :: fv }
      , zEvals :: { zeta :: fv, omegaTimesZeta :: fv }
      , sigmaEvals :: Vector 6 { zeta :: fv, omegaTimesZeta :: fv }
      , indexEvals :: Vector 6 { zeta :: fv, omegaTimesZeta :: fv }
      }
  -- Per_proof_witness.prev_challenges + prev_challenge_polynomial_commitments
  , prevChallenges :: Vector n (Vector tickD fv)
  , prevSgs :: Vector n (AffinePoint fv)
  -- Unfinalized proof (Step.Per_proof.In_circuit)
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
  -- Extra inputs
  , messagesForNextWrapProof :: fv
  , mustVerify :: bv
  -- Branch data fields (used by packStatement for publicInput construction)
  , branchData :: { mask0 :: fv, mask1 :: fv, domainLog2Var :: fv }
  -- Mask for this proof (trimmed proofs_verified_mask, Vector n)
  , proofMask :: Vector n bv
  -- VK commitments for sponge_after_index and IVP
  -- VK commitments (wrap VK consumed by step). At wrapVkChunks > 1 each
  -- commitment is `Vector wrapVkChunks (AffinePoint fv)`. From the IVP's
  -- perspective `wrapVkChunks` is the chunks of the proof being verified;
  -- step verifies a wrap proof, so this is the wrap VK's chunks
  -- (Dim 2 / `wrapVkChunks`). OCaml fixes this to 1 at
  -- `step_main.ml:347` but the type stays polymorphic.
  , vkComms ::
      { sigma :: Vector 6 (Vector wrapVkChunks (AffinePoint fv))
      , sigmaLast :: Vector wrapVkChunks (AffinePoint fv)
      , coeff :: Vector 15 (Vector wrapVkChunks (AffinePoint fv))
      , index :: Vector 6 (Vector wrapVkChunks (AffinePoint fv))
      }
  -- Padded sgOld (Wrap_hack.Padded_length = 2, dummy first)
  , sgOld :: Vector 2 (AffinePoint fv)
  }

type VerifyOneResult tickD fv =
  { challenges :: Vector tickD (SizedF 128 fv) -- raw 128-bit challenges
  , expandedChallenges :: Vector tickD fv -- expanded via endo (compound CVar)
  , result :: BoolVar StepField
  }

-- | Full verify_one matching OCaml step_main.ml:17-148.
-- | Specialized to the Step field (Vesta scalar field = Fp).
verifyOne
  :: forall nd ndPred n wrapVkChunks wrapVkChunksPred tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 totalBases totalBasesPred t m r1
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Compare 0 wrapVkChunks LT
  => Add 1 wrapVkChunksPred wrapVkChunks
  => Reflectable nd Int
  => Reflectable wrapVkChunks Int
  => Reflectable tCommLen Int
  => Reflectable nonSgBases Int
  -- Chunked base layout chain (mirrors IVP). sgOldN at the step IVP is
  -- the fixed `PaddedLength` (= 2) baked into the input shape.
  -- Shared `wCoeffN` / `indexSigmaN` mirror the IVP's collapsing
  -- because Mul's fundep would unify same-RHS counts.
  => Mul 7 wrapVkChunks tCommLen
  => Add 1 tCommLenPred tCommLen
  => Mul 15 wrapVkChunks wCoeffN
  => Mul 6 wrapVkChunks indexSigmaN
  => Mul 43 wrapVkChunks chunkBases
  => Add 2 chunkBases nonSgBases
  => Add 2 nonSgBases totalBases
  => Add 2 wrapVkChunks sg1
  => Add sg1 indexSigmaN sg2
  => Add sg2 wCoeffN sg3
  => Add sg3 wCoeffN sg4
  => Add sg4 indexSigmaN nonSgBases
  => Add 1 totalBasesPred totalBases
  => FOP.Params nd StepField r1
  -> VerifyOneInput n wrapVkChunks tCommLen WrapIPARounds StepIPARounds (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (FVar StepField) (BoolVar StepField)
  -> IncrementallyVerifyProofParams StepField ()
  -> Snarky (KimchiConstraint StepField) t m (VerifyOneResult StepIPARounds (FVar StepField))
verifyOne fopParams input ivpParams = do
  -- Step 1: assert should_finalize == must_verify (step_main.ml:28)
  label "step1_assert_finalize" $ assertEq input.unfinalized.shouldFinalize input.mustVerify

  -- Step 2: FOP (step_main.ml:61-73)
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
    , witness: { allEvals: input.allEvals }
    , mask: input.proofMask
    , prevChallenges: input.prevChallenges
    , domainLog2Var: input.branchData.domainLog2Var
    }

  -- DIAG: emit each of the 4 FOP sub-check booleans to identify which
  -- false one causes the "1 != 2" assertion downstream.
  ivpTrace "diag.fop.xiCorrect" (coerce xiCorrect)
  ivpTrace "diag.fop.bCorrect" (coerce bCorrect)
  ivpTrace "diag.fop.cipCorrect" (coerce cipCorrect)
  ivpTrace "diag.fop.plonkOk" (coerce plonkOk)
  ivpTrace "diag.fop.finalized" (coerce finalized)

  -- Steps 3-4: sponge_after_index + message hash (step_main.ml:76-104)
  -- Build per-proof data for the opt_sponge message hash.
  -- OCaml: old_bulletproof_challenges = prev_challenges, masked by proofs_verified_mask
  -- sgOld is padded to Padded_length=2, but the message hash uses the pre-padded sg points.
  -- For N1: trim_front [mask0,mask1] with lte N1 N2 → [mask1], 1 proof
  -- For N2: trim_front [mask0,mask1] with lte N2 N2 → [mask0,mask1], 2 proofs
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

  -- Step 5: Build statement and pack into publicInput (step_main.ml:88-111)
  -- OCaml: Spec.pack(to_data(statement)) inside Step_verifier.verify
  let
    statement =
      { proofState:
          { deferredValues:
              { plonk: input.proofState.plonk
              , combinedInnerProduct: input.proofState.combinedInnerProduct
              , xi: input.proofState.xi
              , bulletproofChallenges: input.proofState.bulletproofChallenges
              , b: input.proofState.b
              , branchData:
                  { domainLog2: input.branchData.domainLog2Var
                  , proofsVerifiedMask: (coerce input.branchData.mask0) :< (coerce input.branchData.mask1) :< Vector.nil
                  }
              }
          , spongeDigestBeforeEvaluations: input.proofState.spongeDigest
          , messagesForNextWrapProof: input.messagesForNextWrapProof
          }
      , messagesForNextStepProof
      }
    publicInput = packStatement statement

  -- DIAG: emit the reconstructed wrap PI element-by-element to compare
  -- against tock_pi.N. Confirmed fp[0..4] match byte-identical; divergence
  -- must be in later positions (5+).
  let
    Tuple fpFieldsVec (Tuple chalsVec (Tuple scalarChalsVec (Tuple digestsVec (Tuple bpChalsVec packedBranchData)))) = publicInput
  forWithIndex_ fpFieldsVec \fi (Type1 v) -> do
    let i = Data.Fin.getFinite fi
    ivpTrace ("diag.packed_pi." <> show i) v
  -- challenges (beta, gamma) at positions 5-6
  forWithIndex_ chalsVec \fi s -> do
    let i = Data.Fin.getFinite fi + 5
    ivpTrace ("diag.packed_pi." <> show i) (SizedF.toField s)
  -- scalarChallenges (alpha, zeta, xi) at positions 7-9
  forWithIndex_ scalarChalsVec \fi s -> do
    let i = Data.Fin.getFinite fi + 7
    ivpTrace ("diag.packed_pi." <> show i) (SizedF.toField s)
  -- digests (spongeDigest, msgWrap, msgStep) at positions 10-12
  forWithIndex_ digestsVec \fi v -> do
    let i = Data.Fin.getFinite fi + 10
    ivpTrace ("diag.packed_pi." <> show i) v
  -- bp chals (Vector 15) at positions 13-27
  forWithIndex_ bpChalsVec \fi s -> do
    let i = Data.Fin.getFinite fi + 13
    ivpTrace ("diag.packed_pi." <> show i) (SizedF.toField s)
  -- packedBranchData at position 28
  ivpTrace "diag.packed_pi.28" (SizedF.toField packedBranchData)

  -- Step 6: IVP (step_main.ml:115-136)
  let
    ivpParams' = ivpParams

    ivpInput =
      { publicInput
      , sgOld: input.sgOld
      , sgOldMask: Vector.replicate ((const_ one))
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

  -- DIAG: emit IVP success for each slot — complements diag.fop.* to
  -- localize the failing sub-check in verify_one's final result.
  ivpTrace "diag.ivp.success" (coerce output.success)

  -- Step 7: Assert sponge digest (step_verifier.ml:1293-1294, unconditional)
  label "step7_assert_digest" $
    assertEq input.unfinalized.claimedDigest output.spongeDigestBeforeEvaluations

  -- Step 8: Assert bp challenges (step_verifier.ml:1296-1311)
  let isBaseCase = not_ input.mustVerify
  label "step8_assert_bp" $
    forWithIndex_ (Vector.zip input.unfinalized.deferredValues.bulletproofChallenges output.bulletproofChallenges) \i (Tuple c1 c2) -> do
      let idx = Data.Fin.getFinite i
      c2' <- label ("bp_assert_iter_" <> show idx <> "_if") $ if_ isBaseCase c1 c2
      label ("bp_assert_iter_" <> show idx <> "_eq") $ assertEq c1 c2'

  -- Step 9: Final result (step_main.ml:148)
  result <- label "step9_final" do
    verifiedAndFinalized <- and_ output.success finalized
    or_ verifiedAndFinalized (not_ input.mustVerify)

  pure { challenges, expandedChallenges, result }
