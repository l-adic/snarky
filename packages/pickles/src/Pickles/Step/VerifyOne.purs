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

import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofParams, finalizeOtherProofCircuit)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofOpt)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Verify (IncrementallyVerifyProofParams, incrementallyVerifyProof)
import Pickles.Types (StepField)
import Data.Fin (getFinite)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, and_, assertEq, const_, if_, label, not_, or_)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Input to verify_one. All fields from Per_proof_witness + unfinalized + extras.
-- | Specialized to StepField (Vesta scalar field = Fp).
type VerifyOneInput d tickD sf fv bv =
  { -- Per_proof_witness.app_state
    appState :: fv
    -- Per_proof_witness.wrap_proof
  , wComm :: Vector 15 (AffinePoint fv)
  , zComm :: AffinePoint fv
  , tComm :: Vector 7 (AffinePoint fv)
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
  , prevChallenges :: Vector 1 (Vector tickD fv)
  , prevSg :: AffinePoint fv
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
    -- Branch data fields (for publicInput construction)
  , branchData :: { mask0 :: fv, mask1 :: fv, domainLog2Var :: fv }
    -- Mask for this proof (trimmed proofs_verified_mask)
  , proofMask :: bv
    -- Statement/publicInput construction helpers
  , publicInput ::
      { fqFields :: Vector 5 fv
      , challengeFields :: Vector 2 (SizedF 128 fv)
      , scalarChallengeFields :: Vector 3 (SizedF 128 fv)
      , packedBranchData :: SizedF 10 fv
      }
    -- VK commitments for sponge_after_index and IVP
  , vkComms ::
      { sigma :: Vector 6 (AffinePoint fv)
      , sigmaLast :: AffinePoint fv
      , coeff :: Vector 15 (AffinePoint fv)
      , index :: Vector 6 (AffinePoint fv)
      }
    -- Padded sgOld (Wrap_hack.Padded_length = 2, dummy first)
  , sgOld :: Vector 2 (AffinePoint fv)
  }

type VerifyOneResult tickD fv =
  { challenges :: Vector 1 (Vector tickD (SizedF 128 fv))
  , result :: BoolVar StepField
  }

-- | Full verify_one matching OCaml step_main.ml:17-148.
-- | Specialized to the Step field (Vesta scalar field = Fp).
verifyOne
  :: forall t m r1
   . CircuitM StepField (KimchiConstraint StepField) t m
  => FinalizeOtherProofParams StepField r1
  -> VerifyOneInput 15 16 (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (FVar StepField) (BoolVar StepField)
  -> IncrementallyVerifyProofParams StepField ()
  -> Snarky (KimchiConstraint StepField) t m (VerifyOneResult 16 (FVar StepField))
verifyOne fopParams input ivpParams = do
  -- Step 1: assert should_finalize == must_verify (step_main.ml:28)
  label "step1_assert_finalize" $ assertEq input.unfinalized.shouldFinalize input.mustVerify

  -- Step 2: FOP (step_main.ml:61-73)
  let ps = input.proofState
  { finalized, challenges } <- label "step2_fop" $ finalizeOtherProofCircuit StepOtherField.fopShiftOps fopParams
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
    , mask: (coerce input.proofMask :: BoolVar StepField) :< Vector.nil
    , prevChallenges: input.prevChallenges
    , domainLog2Var: input.branchData.domainLog2Var
    }

  -- Steps 3-4: sponge_after_index + message hash (step_main.ml:76-104)
  let rawChallenges = Vector.head input.prevChallenges

  { digest: messagesForNextStepProof, spongeAfterIndex } <-
    hashMessagesForNextStepProofOpt
      { vkComms: input.vkComms
      , appState: input.appState
      , prevSg: input.prevSg
      , rawChallenges
      , proofMask: input.proofMask
      }

  -- Step 5: Build publicInput tuple (step_main.ml:88-111)
  let
    publicInput =
      Tuple input.publicInput.fqFields
        ( Tuple input.publicInput.challengeFields
            ( Tuple input.publicInput.scalarChallengeFields
                ( Tuple
                    (( let { spongeDigest, messagesForNextWrapProof: mnwp } =
                            { spongeDigest: input.proofState.spongeDigest
                            , messagesForNextWrapProof: input.messagesForNextWrapProof
                            }
                       in Vector.generate \j ->
                            case getFinite j of
                              0 -> spongeDigest
                              1 -> mnwp
                              _ -> messagesForNextStepProof
                     ) :: Vector 3 (FVar StepField))
                    ( Tuple
                        input.proofState.bulletproofChallenges
                        input.publicInput.packedBranchData
                    )
                )
            )
        )

  -- Step 6: IVP (step_main.ml:115-136)
  let
    ivpParams' = ivpParams

    ivpInput =
      { publicInput
      , sgOld: input.sgOld
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

  -- Step 7: Assert sponge digest (step_verifier.ml:1293-1294, unconditional)
  label "step7_assert_digest" $
    assertEq input.unfinalized.claimedDigest output.spongeDigestBeforeEvaluations

  -- Step 8: Assert bp challenges (step_verifier.ml:1296-1311)
  let isBaseCase = not_ input.mustVerify
  label "step8_assert_bp" $
    for_ (Vector.zip input.unfinalized.deferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) -> do
      c2' <- if_ isBaseCase c1 c2
      assertEq c1 c2'

  -- Step 9: Final result (step_main.ml:148)
  result <- label "step9_final" do
    verifiedAndFinalized <- and_ output.success finalized
    or_ verifiedAndFinalized (not_ input.mustVerify)

  pure { challenges: (\x -> x :< Vector.nil) challenges, result }
