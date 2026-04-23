-- | Minimal Tree_proof_return b0 producer for convergence testing.
-- |
-- | Runs the base-case setup from `Test.Pickles.Prove.TreeProofReturn`:
-- |
-- |   * NRR step + wrap via `produceNoRecursionReturn` (slot-0 real proof)
-- |   * Tree step compile (heterogeneous prevs: N0 NRR, N2 self)
-- |   * Tree wrap compile (Slots2 0 2, override_wrap_domain=N1 → 2^14)
-- |   * Per-slot step advice: slot 0 real-NRR via `buildStepAdviceWithOracles`,
-- |     slot 1 dummy N2 via the same helper with `dummyWrapProof`
-- |   * Tree step prove, Tree wrap prove
-- |
-- | Returns artifacts sufficient for end-to-end `Pickles.verify` of the
-- | resulting wrap proof. Stripped of trace emission, diagnostics, and
-- | the b1 iteration.
module Test.Pickles.Prove.TreeProofReturn.B0Producer
  ( TreeProofReturnB0Artifacts
  , produceTreeProofReturnB0
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles.Dummy as Dummy
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.Proof.Dummy (dummyWrapProof)
import Pickles.ProofFFI as ProofFFI
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, WrapDeferredValuesOutput, assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Prove.Step (StepAdvice(..), StepCompileResult, StepRule, buildStepAdviceWithOracles, dummyWrapTockPublicInput, extractWrapVKCommsAdvice, stepCompile, stepSolveAndProve)
import Pickles.Prove.Wrap (BuildWrapAdviceInput, WrapAdvice, WrapCompileResult, WrapProveResult, buildWrapAdvice, buildWrapMainConfig, wrapCompile, wrapSolveAndProve)
import Pickles.Prove.Wrap (WrapCompileContext) as WP
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (PaddedLength, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, StepIPARounds, WrapField, WrapIPARounds)
import Pickles.Util.Fatal (fromJust')
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Pickles.Wrap.Slots (Slots2, slots2)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..), FVar, SizedF, UnChecked(..), add_, coerceViaBits, const_, exists, if_, not_, true_)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (SplitField, Type2, toFieldPure)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, fromInt, toBigInt)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (fromShifted, toShifted)
import Test.Pickles.Prove.NoRecursionReturn.Producer (produceNoRecursionReturn)

type TreeProofReturnPrevsSpec = PrevsSpecCons 0 (PrevsSpecCons 2 PrevsSpecNil)

type TreeProofReturnB0Artifacts =
  { stepCR :: StepCompileResult
  , wrapCR :: WrapCompileResult
  , wrapDvInput :: WrapDeferredValuesInput 2
  , wrapDv :: WrapDeferredValuesOutput
  , wrapResult :: WrapProveResult
  , stepProofSg :: AffinePoint WrapField
  , messagesForNextStepProofDigest :: StepField
  , messagesForNextWrapProofDigest :: WrapField
  }

-- | Tree_proof_return rule — base-case variant (is_base_case = true).
-- | Verbatim lift from `Test.Pickles.Prove.TreeProofReturn.treeProofReturnRule`.
treeProofReturnRule
  :: { isBaseCase :: Boolean, nrrInputVal :: F StepField, prevInputVal :: F StepField }
  -> StepRule 2
       Unit
       Unit
       (F StepField)
       (FVar StepField)
       (F StepField)
       (FVar StepField)
treeProofReturnRule { isBaseCase, nrrInputVal, prevInputVal } _ = do
  nrrInput <- exists $ lift $ pure nrrInputVal
  prevInput <- exists $ lift $ pure prevInputVal
  isBaseCaseBool <- exists $ lift $ pure isBaseCase
  let proofMustVerifySlot1 = not_ isBaseCaseBool
  let onePlusPrev = add_ (const_ one) prevInput
  self <- if_ isBaseCaseBool (const_ zero) onePlusPrev
  pure
    { prevPublicInputs: nrrInput :< prevInput :< Vector.nil
    , proofMustVerify: true_ :< proofMustVerifySlot1 :< Vector.nil
    , publicOutput: self
    }

produceTreeProofReturnB0
  :: { vestaSrs :: CRS VestaG
     , lagrangeSrs :: CRS PallasG
     , pallasProofCrs :: CRS PallasG
     }
  -> Aff TreeProofReturnB0Artifacts
produceTreeProofReturnB0 { vestaSrs, lagrangeSrs, pallasProofCrs } = do
  -- ===== NRR slot-0 producer =====
  nrr <- produceNoRecursionReturn
    { vestaSrs, lagrangeSrs, pallasProofCrs }
  let nrrWrapVKCommsAdvice = extractWrapVKCommsAdvice nrr.wrapCR.verifierIndex

  let
    bcd = Dummy.baseCaseDummies { maxProofsVerified: 2 }
    dummySgValues = Dummy.computeDummySgValues bcd lagrangeSrs vestaSrs
    nrrWrapSg = dummySgValues.ipa.wrap.sg
    nrrWrapDomainLog2 = nrr.wrapDomainLog2
    treeWrapDomainLog2 = 14

    mkLagrangeAtNrr = mkConstLagrangeBaseLookup \i ->
      (coerce (ProofFFI.vestaSrsLagrangeCommitmentAt lagrangeSrs nrrWrapDomainLog2 i))
        :: AffinePoint (F StepField)
    mkLagrangeAtTree = mkConstLagrangeBaseLookup \i ->
      (coerce (ProofFFI.vestaSrsLagrangeCommitmentAt lagrangeSrs treeWrapDomainLog2 i))
        :: AffinePoint (F StepField)

    nrrStepDomainLog2 = ProofFFI.pallasProverIndexDomainLog2 nrr.stepCR.proverIndex
    treeSelfStepDomainLog2 = 15

    treeSrsData =
      { perSlotLagrangeAt: mkLagrangeAtNrr :< mkLagrangeAtTree :< Vector.nil
      , blindingH:
          (coerce $ ProofFFI.vestaSrsBlindingGenerator lagrangeSrs)
            :: AffinePoint (F StepField)
      , perSlotFopDomainLog2: nrrStepDomainLog2 :< treeSelfStepDomainLog2 :< Vector.nil
      , perSlotKnownWrapKeys: Just nrrWrapVKCommsAdvice :< Nothing :< Vector.nil
      }

    treeCtx =
      { srsData: treeSrsData
      , dummySg: nrrWrapSg
      , crs: vestaSrs
      , debug: false
      }

  let
    baseRuleArgs =
      { isBaseCase: true
      , nrrInputVal: F zero
      , prevInputVal: F (negate one)
      }

  -- ===== Tree step compile =====
  treeStepCR <- liftEffect $
    stepCompile @TreeProofReturnPrevsSpec @67
      @Unit
      @Unit
      @(F StepField)
      @(FVar StepField)
      @(F StepField)
      @(FVar StepField)
      treeCtx
      (treeProofReturnRule baseRuleArgs)

  let treeStepDomainLog2 = ProofFFI.pallasProverIndexDomainLog2 treeStepCR.proverIndex

  -- ===== Tree wrap compile =====
  let
    treeWrapCtx :: WP.WrapCompileContext 1
    treeWrapCtx =
      { wrapMainConfig:
          buildWrapMainConfig vestaSrs treeStepCR.verifierIndex
            { stepWidth: 2, domainLog2: treeStepDomainLog2 }
      , crs: pallasProofCrs
      }
  treeWrapCR <- liftEffect $ wrapCompile @1 @(Slots2 0 2) treeWrapCtx

  -- ===== Slot-0 advice (real NRR) =====
  let
    nrrDv = nrr.wrapDv

    stepEndoScalar :: StepField
    stepEndoScalar = let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

    unF :: SizedF 128 (F StepField) -> SizedF 128 StepField
    unF = SizedF.unwrapF

    wrapPlonkRawFromDv =
      { alpha: unF nrrDv.plonk.alpha
      , beta: unF nrrDv.plonk.beta
      , gamma: unF nrrDv.plonk.gamma
      , zeta: unF nrrDv.plonk.zeta
      }

    stepOraclesNrr = ProofFFI.pallasProofOracles nrr.stepCR.verifierIndex
      { proof: nrr.stepResult.proof
      , publicInput: nrr.stepResult.publicInputs
      , prevChallenges: []
      }

    nrrWrapPrevEvals :: AllEvals StepField
    nrrWrapPrevEvals =
      { ftEval1: stepOraclesNrr.ftEval1
      , publicEvals:
          { zeta: stepOraclesNrr.publicEvalZeta
          , omegaTimesZeta: stepOraclesNrr.publicEvalZetaOmega
          }
      , zEvals: ProofFFI.proofZEvals nrr.stepResult.proof
      , witnessEvals: ProofFFI.proofWitnessEvals nrr.stepResult.proof
      , coeffEvals: ProofFFI.proofCoefficientEvals nrr.stepResult.proof
      , sigmaEvals: ProofFFI.proofSigmaEvals nrr.stepResult.proof
      , indexEvals: ProofFFI.proofIndexEvals nrr.stepResult.proof
      }

    slot0OracleInput =
      { publicInput: unit
      , prevPublicInput: F zero
      , wrapDomainLog2: nrr.wrapDomainLog2
      , stepDomainLog2: nrrStepDomainLog2
      , wrapVK: nrr.wrapCR.verifierIndex
      , stepOpeningSg: ProofFFI.pallasProofOpeningSg nrr.stepResult.proof
      , kimchiPrevSg: ProofFFI.pallasProofOpeningSg nrr.stepResult.proof
      , wrapProof: nrr.wrapResult.proof
      , wrapPublicInput: nrr.wrapPublicInput
      , prevChalPolys:
          let
            dummyEntry = { sg: nrrWrapSg, challenges: Dummy.dummyIpaChallenges.wrapExpanded }
          in
            dummyEntry :< dummyEntry :< Vector.nil :: Vector PaddedLength _
      , wrapPlonkRaw: wrapPlonkRawFromDv
      , wrapPrevEvals: nrrWrapPrevEvals
      , wrapBranchData: nrrDv.branchData
      , wrapSpongeDigest: nrrDv.spongeDigestBeforeEvaluations
      , mustVerify: true
      , wrapOwnPaddedBpChals:
          Dummy.dummyIpaChallenges.wrapExpanded
            :< Dummy.dummyIpaChallenges.wrapExpanded
            :< Vector.nil
      , fopState:
          { deferredValues:
              { plonk: nrrDv.plonk
              , combinedInnerProduct: nrrDv.combinedInnerProduct
              , xi: nrrDv.xi
              , bulletproofChallenges: nrrDv.bulletproofPrechallenges
              , b: nrrDv.b
              }
          , shouldFinalize: false
          , spongeDigestBeforeEvaluations: F nrrDv.spongeDigestBeforeEvaluations
          }
      , stepAdvicePrevEvals: nrrWrapPrevEvals
      , kimchiPrevChallengesExpanded:
          map
            (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
            nrrDv.bulletproofPrechallenges
      , prevChallengesForStepHash: Vector.replicate Dummy.dummyIpaChallenges.stepExpanded
      }

  { advice: slot0Advice, challengePolynomialCommitment: b0Slot0ChalPolyComm } <-
    liftEffect $ buildStepAdviceWithOracles @0 @(PrevsSpecCons 0 PrevsSpecNil) slot0OracleInput

  -- ===== Slot-1 advice (dummy N2) =====
  let
    slot1BaseCaseDummyChalPoly =
      { sg: nrrWrapSg, challenges: Dummy.dummyIpaChallenges.wrapExpanded }
    slot1BaseCaseWrapPI = dummyWrapTockPublicInput @2
      { wrapDomainLog2: treeSelfStepDomainLog2
      , wrapVK: treeWrapCR.verifierIndex
      , prevPublicInput: (F (negate one)) :: F StepField
      , wrapSg: nrrWrapSg
      , stepSg: nrr.stepSg
      , msgWrapDigest: hashMessagesForNextWrapProofPureGeneral
          { sg: nrr.stepSg
          , paddedChallenges:
              Dummy.dummyIpaChallenges.wrapExpanded
                :< Dummy.dummyIpaChallenges.wrapExpanded
                :< Vector.nil
          }
      , fopProofState: Dummy.stepDummyUnfinalizedProof @2 bcd
          { domainLog2: Dummy.wrapDomainLog2ForProofsVerified 2 }
          (map SizedF.wrapF bcd.ipaStepChallenges)
      }
  { advice: slot1Advice, challengePolynomialCommitment: b0Slot1ChalPolyComm } <-
    liftEffect $ buildStepAdviceWithOracles @2 @(PrevsSpecCons 2 PrevsSpecNil)
      { publicInput: unit
      , prevPublicInput: (F (negate one)) :: F StepField
      , wrapDomainLog2: treeWrapDomainLog2
      , stepDomainLog2: treeSelfStepDomainLog2
      , wrapVK: treeWrapCR.verifierIndex
      , stepOpeningSg: nrr.stepSg
      , kimchiPrevSg: nrr.stepSg
      , wrapProof: dummyWrapProof bcd
      , wrapPublicInput: slot1BaseCaseWrapPI
      , prevChalPolys:
          slot1BaseCaseDummyChalPoly
            :< slot1BaseCaseDummyChalPoly
            :< Vector.nil :: Vector PaddedLength _
      , wrapPlonkRaw:
          { alpha: bcd.proofDummy.plonk.alpha
          , beta: bcd.proofDummy.plonk.beta
          , gamma: bcd.proofDummy.plonk.gamma
          , zeta: bcd.proofDummy.plonk.zeta
          }
      , wrapPrevEvals: bcd.proofDummy.prevEvals
      , wrapBranchData:
          { domainLog2: (fromInt treeSelfStepDomainLog2) :: StepField
          , proofsVerifiedMask: true :< true :< Vector.nil
          }
      , wrapSpongeDigest: zero
      , mustVerify: false
      , wrapOwnPaddedBpChals:
          Dummy.dummyIpaChallenges.wrapExpanded
            :< Dummy.dummyIpaChallenges.wrapExpanded
            :< Vector.nil
      , fopState: Dummy.stepDummyUnfinalizedProof @2 bcd
          { domainLog2: Dummy.wrapDomainLog2ForProofsVerified 2 }
          (map SizedF.wrapF bcd.ipaStepChallenges)
      , stepAdvicePrevEvals: bcd.proofDummy.prevEvals
      , kimchiPrevChallengesExpanded: Dummy.dummyIpaChallenges.stepExpanded
      , prevChallengesForStepHash: Vector.replicate Dummy.dummyIpaChallenges.stepExpanded
      }

  -- ===== Compose heterogeneous advice =====
  let
    StepAdvice s0 = slot0Advice
    StepAdvice s1 = slot1Advice
    Tuple slot0Sppw _ = s0.perProofSlotsCarrier
    Tuple slot1Sppw _ = s1.perProofSlotsCarrier

    treeRealAdvice :: StepAdvice TreeProofReturnPrevsSpec StepIPARounds WrapIPARounds Unit 2 _
    treeRealAdvice = StepAdvice
      { perProofSlotsCarrier: Tuple slot0Sppw (Tuple slot1Sppw unit)
      , publicInput: unit
      , publicUnfinalizedProofs:
          Vector.head s0.publicUnfinalizedProofs
            :< Vector.head s1.publicUnfinalizedProofs
            :< Vector.nil
      , messagesForNextWrapProof:
          Vector.head s0.messagesForNextWrapProof
            :< Vector.head s1.messagesForNextWrapProof
            :< Vector.nil
      , wrapVerifierIndex: extractWrapVKCommsAdvice treeWrapCR.verifierIndex
      , kimchiPrevChallenges:
          Vector.head s0.kimchiPrevChallenges
            :< Vector.head s1.kimchiPrevChallenges
            :< Vector.nil
      }

  -- ===== Tree step prove =====
  treeStepRes <- liftEffect $ runExceptT $
    stepSolveAndProve
      @TreeProofReturnPrevsSpec
      @67
      @Unit
      @Unit
      @(F StepField)
      @(FVar StepField)
      @(F StepField)
      @(FVar StepField)
      treeCtx
      (treeProofReturnRule baseRuleArgs)
      treeStepCR
      treeRealAdvice
  treeStepResult <- case treeStepRes of
    Left e -> liftEffect $ Exc.throw ("tree stepSolveAndProve: " <> show e)
    Right r -> pure r

  -- ===== Tree wrap prove =====
  let
    nrrBpChalsExpandedForSlot0 :: Vector StepIPARounds StepField
    nrrBpChalsExpandedForSlot0 =
      map
        (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
        nrr.wrapDv.bulletproofPrechallenges

    nrrStepOpeningSgOracle = ProofFFI.pallasProofOpeningSg nrr.stepResult.proof
    stepOraclesTree = ProofFFI.pallasProofOracles treeStepCR.verifierIndex
      { proof: treeStepResult.proof
      , publicInput: treeStepResult.publicInputs
      , prevChallenges:
          [ { sgX: nrrStepOpeningSgOracle.x
            , sgY: nrrStepOpeningSgOracle.y
            , challenges: Vector.toUnfoldable nrrBpChalsExpandedForSlot0
            }
          , { sgX: nrr.stepSg.x
            , sgY: nrr.stepSg.y
            , challenges: Vector.toUnfoldable Dummy.dummyIpaChallenges.stepExpanded
            }
          ]
      }

    treeStepAllEvals :: AllEvals StepField
    treeStepAllEvals =
      { ftEval1: stepOraclesTree.ftEval1
      , publicEvals:
          { zeta: stepOraclesTree.publicEvalZeta
          , omegaTimesZeta: stepOraclesTree.publicEvalZetaOmega
          }
      , zEvals: ProofFFI.proofZEvals treeStepResult.proof
      , witnessEvals: ProofFFI.proofWitnessEvals treeStepResult.proof
      , coeffEvals: ProofFFI.proofCoefficientEvals treeStepResult.proof
      , sigmaEvals: ProofFFI.proofSigmaEvals treeStepResult.proof
      , indexEvals: ProofFFI.proofIndexEvals treeStepResult.proof
      }

    treeWrapDvInput :: WrapDeferredValuesInput 2
    treeWrapDvInput =
      { proof: treeStepResult.proof
      , verifierIndex: treeStepCR.verifierIndex
      , publicInput: treeStepResult.publicInputs
      , allEvals: treeStepAllEvals
      , pEval0Chunks: [ stepOraclesTree.publicEvalZeta ]
      , domainLog2: treeStepDomainLog2
      , zkRows: 3
      , srsLengthLog2: 16
      , generator: (domainGenerator treeStepDomainLog2 :: StepField)
      , shifts: (domainShifts treeStepDomainLog2 :: Vector 7 StepField)
      , vanishesOnZk: ProofFFI.permutationVanishingPolynomial
          { domainLog2: treeStepDomainLog2, zkRows: 3, pt: stepOraclesTree.zeta }
      , omegaForLagrange: \_ -> one
      , endo: stepEndoScalar
      , linearizationPoly: Linearization.pallas
      , prevSgs: nrrStepOpeningSgOracle :< nrr.stepSg :< Vector.nil
      , prevChallenges:
          nrrBpChalsExpandedForSlot0
            :< Dummy.dummyIpaChallenges.stepExpanded
            :< Vector.nil
      , proofsVerifiedMask: true :< true :< Vector.nil
      }

    treeWrapDv = wrapComputeDeferredValues treeWrapDvInput

    msgForNextStepDigestTree :: StepField
    msgForNextStepDigestTree =
      fromJust'
        "Tree wrap prove: step PI[64] outer hash must exist" $
        Array.index treeStepResult.publicInputs 64

    treeWrapProofSg :: AffinePoint WrapField
    treeWrapProofSg = ProofFFI.pallasProofOpeningSg treeStepResult.proof

    treeWrapEndoScalar :: WrapField
    treeWrapEndoScalar = let EndoScalar e = (endoScalar :: EndoScalar WrapField) in e

    PerProofUnfinalized slot0UnfRec =
      Vector.head (unwrap treeRealAdvice).publicUnfinalizedProofs

    PerProofUnfinalized slot1UnfRec =
      Vector.head (Vector.drop @1 (unwrap treeRealAdvice).publicUnfinalizedProofs)

    slot0RealBpChalsWrap :: Vector WrapIPARounds WrapField
    slot0RealBpChalsWrap =
      map
        (\(UnChecked v) -> toFieldPure (coerceViaBits v :: SizedF 128 WrapField) treeWrapEndoScalar)
        slot0UnfRec.bulletproofChallenges

    slot1RealBpChalsWrap :: Vector WrapIPARounds WrapField
    slot1RealBpChalsWrap =
      map
        (\(UnChecked v) -> toFieldPure (coerceViaBits v :: SizedF 128 WrapField) treeWrapEndoScalar)
        slot1UnfRec.bulletproofChallenges

    msgForNextWrapDigestTree :: WrapField
    msgForNextWrapDigestTree = hashMessagesForNextWrapProofPureGeneral
      { sg: treeWrapProofSg
      , paddedChallenges:
          slot0RealBpChalsWrap
            :< slot1RealBpChalsWrap
            :< Vector.nil
      }

    treeWrapPublicInput = assembleWrapMainInput
      { deferredValues: treeWrapDv
      , messagesForNextStepProofDigest: msgForNextStepDigestTree
      , messagesForNextWrapProofDigest: msgForNextWrapDigestTree
      }

    convertSlotUnf
      :: { combinedInnerProduct :: Type2 (SplitField (F StepField) Boolean)
         , b :: Type2 (SplitField (F StepField) Boolean)
         , zetaToSrsLength :: Type2 (SplitField (F StepField) Boolean)
         , zetaToDomainSize :: Type2 (SplitField (F StepField) Boolean)
         , perm :: Type2 (SplitField (F StepField) Boolean)
         , spongeDigest :: F StepField
         , beta :: UnChecked (SizedF 128 (F StepField))
         , gamma :: UnChecked (SizedF 128 (F StepField))
         , alpha :: UnChecked (SizedF 128 (F StepField))
         , zeta :: UnChecked (SizedF 128 (F StepField))
         , xi :: UnChecked (SizedF 128 (F StepField))
         , bulletproofChallenges ::
             Vector WrapIPARounds (UnChecked (SizedF 128 (F StepField)))
         , shouldFinalize :: Boolean
         }
      -> PerProofUnfinalized WrapIPARounds (Type2 (F WrapField))
           (F WrapField)
           Boolean
    convertSlotUnf r = PerProofUnfinalized
      { combinedInnerProduct: toShifted (fromShifted r.combinedInnerProduct :: F WrapField)
      , b: toShifted (fromShifted r.b :: F WrapField)
      , zetaToSrsLength: toShifted (fromShifted r.zetaToSrsLength :: F WrapField)
      , zetaToDomainSize: toShifted (fromShifted r.zetaToDomainSize :: F WrapField)
      , perm: toShifted (fromShifted r.perm :: F WrapField)
      , spongeDigest: F (fromBigInt (toBigInt (case r.spongeDigest of F x -> x)) :: WrapField)
      , beta: UnChecked (coerceViaBits (case r.beta of UnChecked v -> v))
      , gamma: UnChecked (coerceViaBits (case r.gamma of UnChecked v -> v))
      , alpha: UnChecked (coerceViaBits (case r.alpha of UnChecked v -> v))
      , zeta: UnChecked (coerceViaBits (case r.zeta of UnChecked v -> v))
      , xi: UnChecked (coerceViaBits (case r.xi of UnChecked v -> v))
      , bulletproofChallenges:
          map (\(UnChecked v) -> UnChecked (coerceViaBits v)) r.bulletproofChallenges
      , shouldFinalize: r.shouldFinalize
      }

    slot0PerProof = convertSlotUnf slot0UnfRec
    slot1PerProof = convertSlotUnf slot1UnfRec

    nrrStepOpeningSg = ProofFFI.pallasProofOpeningSg nrr.stepResult.proof

    slot0StepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
    slot0StepAcc = WeierstrassAffinePoint
      { x: F nrrStepOpeningSg.x, y: F nrrStepOpeningSg.y }

    slot1StepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
    slot1StepAcc = WeierstrassAffinePoint
      { x: F nrr.stepSg.x, y: F nrr.stepSg.y }

    dummyWrapBpChalsW :: Vector WrapIPARounds (F WrapField)
    dummyWrapBpChalsW = map F Dummy.dummyIpaChallenges.wrapExpanded

    slot0PrevEvalsW :: StepAllEvals (F WrapField)
    slot0PrevEvalsW =
      let
        o = ProofFFI.vestaProofOracles nrr.wrapCR.verifierIndex
          { proof: nrr.wrapResult.proof
          , publicInput: nrr.wrapPublicInput
          , prevChallenges: []
          }
        mkPE p = { zeta: F p.zeta, omegaTimesZeta: F p.omegaTimesZeta }
      in
        StepAllEvals
          { ftEval1: F o.ftEval1
          , publicEvals: PointEval
              { zeta: F o.publicEvalZeta
              , omegaTimesZeta: F o.publicEvalZetaOmega
              }
          , zEvals: PointEval (mkPE (ProofFFI.proofZEvals nrr.wrapResult.proof))
          , witnessEvals: map (PointEval <<< mkPE) (ProofFFI.proofWitnessEvals nrr.wrapResult.proof)
          , coeffEvals: map (PointEval <<< mkPE) (ProofFFI.proofCoefficientEvals nrr.wrapResult.proof)
          , sigmaEvals: map (PointEval <<< mkPE) (ProofFFI.proofSigmaEvals nrr.wrapResult.proof)
          , indexEvals: map (PointEval <<< mkPE) (ProofFFI.proofIndexEvals nrr.wrapResult.proof)
          }

    slot1PrevEvalsW :: StepAllEvals (F WrapField)
    slot1PrevEvalsW =
      let
        toFFI r = { sgX: r.sg.x, sgY: r.sg.y, challenges: Vector.toUnfoldable r.challenges }
        dummyChalPoly = { sg: nrrWrapSg, challenges: Dummy.dummyIpaChallenges.wrapExpanded }
        o = ProofFFI.vestaProofOracles treeWrapCR.verifierIndex
          { proof: dummyWrapProof bcd
          , publicInput: slot1BaseCaseWrapPI
          , prevChallenges: map toFFI [ dummyChalPoly, dummyChalPoly ]
          }
        de = bcd.dummyEvals
        pe p = PointEval { zeta: F p.zeta, omegaTimesZeta: F p.omegaTimesZeta }
      in
        StepAllEvals
          { ftEval1: F de.ftEval1
          , publicEvals: PointEval
              { zeta: F o.publicEvalZeta
              , omegaTimesZeta: F o.publicEvalZetaOmega
              }
          , zEvals: pe de.zEvals
          , witnessEvals: map pe de.witnessEvals
          , coeffEvals: map pe de.coeffEvals
          , sigmaEvals: map pe de.sigmaEvals
          , indexEvals: map pe de.indexEvals
          }

    treeWrapAdviceInput :: BuildWrapAdviceInput 2 (Slots2 0 2)
    treeWrapAdviceInput =
      { stepProof: treeStepResult.proof
      , whichBranch: F zero
      , prevUnfinalizedProofs: slot0PerProof :< slot1PerProof :< Vector.nil
      , prevMessagesForNextStepProofHash:
          F (fromBigInt (toBigInt msgForNextStepDigestTree) :: WrapField)
      , prevStepAccs: slot0StepAcc :< slot1StepAcc :< Vector.nil
      , prevOldBpChals: slots2 Vector.nil (dummyWrapBpChalsW :< dummyWrapBpChalsW :< Vector.nil)
      , prevEvals: slot0PrevEvalsW :< slot1PrevEvalsW :< Vector.nil
      , prevWrapDomainIndices:
          F (fromInt 0 :: WrapField) :< F (fromInt 1 :: WrapField) :< Vector.nil
      }

    treeWrapAdvice :: WrapAdvice 2 (Slots2 0 2)
    treeWrapAdvice = buildWrapAdvice treeWrapAdviceInput

    treeWrapProveCtx =
      { wrapMainConfig: treeWrapCtx.wrapMainConfig
      , crs: pallasProofCrs
      , publicInput: treeWrapPublicInput
      , advice: treeWrapAdvice
      , debug: false
      , kimchiPrevChallenges:
          { sgX: b0Slot0ChalPolyComm.x
          , sgY: b0Slot0ChalPolyComm.y
          , challenges: slot0RealBpChalsWrap
          }
            :<
              { sgX: b0Slot1ChalPolyComm.x
              , sgY: b0Slot1ChalPolyComm.y
              , challenges: slot1RealBpChalsWrap
              }
            :<
              Vector.nil
      }

  treeWrapRes <- liftEffect $ runExceptT $
    wrapSolveAndProve @1 @(Slots2 0 2) treeWrapProveCtx treeWrapCR
  treeWrapResult <- case treeWrapRes of
    Left e -> liftEffect $ Exc.throw ("tree wrapSolveAndProve: " <> show e)
    Right r -> pure r

  pure
    { stepCR: treeStepCR
    , wrapCR: treeWrapCR
    , wrapDvInput: treeWrapDvInput
    , wrapDv: treeWrapDv
    , wrapResult: treeWrapResult
    , stepProofSg: treeWrapProofSg
    , messagesForNextStepProofDigest: msgForNextStepDigestTree
    , messagesForNextWrapProofDigest: msgForNextWrapDigestTree
    }
