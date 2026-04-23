-- | Minimal Simple_chain b1 producer — inductive case on top of
-- | `produceSimpleChainB0`.
-- |
-- | The b1 iteration takes the real b0 wrap proof as a prev and proves
-- | `self = 1` with `prev = 0`. This is the first iteration where
-- | `oldBulletproofChallenges` carries a real (non-dummy) prev-proof
-- | bp-chal vector, and where `challengePolynomialCommitment` points at
-- | a real step-proof sg rather than a dummy. That exercises stages 2
-- | (accumulator check) and 1 (sub-sponge absorb of real chals) of
-- | `Pickles.verify` with inductive data.
-- |
-- | Lifted from the b1 block in `Test.Pickles.Prove.SimpleChain` with
-- | diagnostic traces and self-verify assertions stripped.
module Test.Pickles.Prove.SimpleChain.B1Producer
  ( SimpleChainB1Artifacts
  , produceSimpleChainB1
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (unwrap)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Partial.Unsafe (unsafePartial)
import Pickles.Dummy (baseCaseDummies, computeDummySgValues, dummyIpaChallenges) as Dummy
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI (OraclesResult)
import Pickles.ProofFFI (pallasProofOpeningSg, pallasProofOracles, pallasProverIndexDomainLog2, permutationVanishingPolynomial, proofCoefficientEvals, proofIndexEvals, proofSigmaEvals, proofWitnessEvals, proofZEvals, vestaProofOracles, vestaSrsBlindingGenerator, vestaSrsLagrangeCommitmentAt) as ProofFFI
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, WrapDeferredValuesOutput, assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Prove.Step (buildStepAdviceWithOracles, stepSolveAndProve)
import Pickles.Prove.Wrap (BuildWrapAdviceInput, WrapAdvice, WrapProveResult, buildWrapAdvice, buildWrapMainConfig, wrapSolveAndProve)
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (PaddedLength, PerProofUnfinalized(..), PointEval(..), StatementIO, StepAllEvals(..), StepField, WrapField, WrapIPARounds)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProof)
import Pickles.Wrap.Slots (Slots1, slots1)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..), FVar, UnChecked(..), coerceViaBits)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (Type2, toFieldPure)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, fromInt, toBigInt)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (fromShifted, toShifted)
import Test.Pickles.Prove.SimpleChain (simpleChainRule)
import Test.Pickles.Prove.SimpleChain.B0Producer (SimpleChainB0Artifacts, produceSimpleChainB0)

type SimpleChainB1Artifacts =
  { b0 :: SimpleChainB0Artifacts
  , wrapDvInput :: WrapDeferredValuesInput 1
  , wrapDv :: WrapDeferredValuesOutput
  , wrapResult :: WrapProveResult
  , stepProofSg :: AffinePoint WrapField
  , messagesForNextStepProofDigest :: StepField
  , messagesForNextWrapProofDigest :: WrapField
  }

produceSimpleChainB1
  :: { vestaSrs :: CRS VestaG
     , lagrangeSrs :: CRS PallasG
     , pallasProofCrs :: CRS PallasG
     }
  -> Aff SimpleChainB1Artifacts
produceSimpleChainB1 srses = do
  b0 <- produceSimpleChainB0 srses
  let
    { vestaSrs, lagrangeSrs, pallasProofCrs } = srses

    stepCR = b0.stepCR
    wrapCR = b0.wrapCR
    stepDomainLog2 = ProofFFI.pallasProverIndexDomainLog2 stepCR.proverIndex
    wrapDomainLog2 = 14

    -- Reconstruct the dummy step sg (used by b1 when computing oracles
    -- over the b0 step proof — same value b0 itself used).
    bcd = Dummy.baseCaseDummies { maxProofsVerified: 1 }
    dummySgValues = Dummy.computeDummySgValues bcd lagrangeSrs vestaSrs

    dummyStepSg :: AffinePoint WrapField
    dummyStepSg = dummySgValues.ipa.step.sg

    lagrangeAtD14 =
      mkConstLagrangeBaseLookup \i ->
        (coerce (ProofFFI.vestaSrsLagrangeCommitmentAt lagrangeSrs wrapDomainLog2 i))
          :: AffinePoint (F StepField)

    ctx =
      { srsData:
          { perSlotLagrangeAt: lagrangeAtD14 :< Vector.nil
          , blindingH:
              (coerce $ ProofFFI.vestaSrsBlindingGenerator lagrangeSrs)
                :: AffinePoint (F StepField)
          , perSlotFopDomainLog2: wrapDomainLog2 :< Vector.nil
          , perSlotKnownWrapKeys: Nothing :< Vector.nil
          }
      , dummySg: b0.wrapSg
      , crs: vestaSrs
      , debug: false
      }

    stepEndoScalar :: StepField
    stepEndoScalar = let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

    msgForNextWrapWrapEndo :: WrapField
    msgForNextWrapWrapEndo =
      let EndoScalar e = (endoScalar :: EndoScalar WrapField) in e

    b0StepSg :: AffinePoint WrapField
    b0StepSg = b0.stepProofSg

    baseCaseDummyChalPoly =
      { sg: b0.wrapSg, challenges: Dummy.dummyIpaChallenges.wrapExpanded }

    -- Oracles on the b0 step proof — needed to reconstruct its evals for
    -- feeding into b1's step FOP.
    b0StepOracles :: OraclesResult StepField
    b0StepOracles = ProofFFI.pallasProofOracles stepCR.verifierIndex
      { proof: b0.stepResult.proof
      , publicInput: b0.stepResult.publicInputs
      , prevChallenges:
          [ { sgX: dummyStepSg.x
            , sgY: dummyStepSg.y
            , challenges:
                Vector.toUnfoldable Dummy.dummyIpaChallenges.stepExpanded
            }
          ]
      }

    b1WrapPrevEvals :: AllEvals StepField
    b1WrapPrevEvals =
      { ftEval1: b0StepOracles.ftEval1
      , publicEvals:
          { zeta: b0StepOracles.publicEvalZeta
          , omegaTimesZeta: b0StepOracles.publicEvalZetaOmega
          }
      , zEvals: ProofFFI.proofZEvals b0.stepResult.proof
      , witnessEvals: ProofFFI.proofWitnessEvals b0.stepResult.proof
      , coeffEvals: ProofFFI.proofCoefficientEvals b0.stepResult.proof
      , sigmaEvals: ProofFFI.proofSigmaEvals b0.stepResult.proof
      , indexEvals: ProofFFI.proofIndexEvals b0.stepResult.proof
      }

    b1PrevChalPolys =
      let
        realEntry = { sg: b0.b0ChalPolyComm, challenges: b0.msgForNextWrapRealChals }
        dummyEntry = baseCaseDummyChalPoly
      in
        dummyEntry :< realEntry :< Vector.nil

    b1WrapOwnPaddedBpChals :: Vector PaddedLength (Vector WrapIPARounds WrapField)
    b1WrapOwnPaddedBpChals =
      Dummy.dummyIpaChallenges.wrapExpanded
        :< b0.msgForNextWrapRealChals
        :< Vector.nil

  -- ===== b1 step advice =====
  { advice: b1Advice, challengePolynomialCommitment: b1ChalPolyComm } <-
    liftEffect $ buildStepAdviceWithOracles @1 @(PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil)
      { publicInput: F one
      , prevPublicInput: F zero
      , wrapDomainLog2
      , stepDomainLog2: wrapDomainLog2
      , wrapVK: wrapCR.verifierIndex
      , stepOpeningSg: b0StepSg
      , kimchiPrevSg: b0StepSg
      , wrapProof: b0.wrapResult.proof
      , wrapPublicInput: b0.wrapResult.publicInputs
      , prevChalPolys: (b1PrevChalPolys :: Vector PaddedLength _)
      , wrapPlonkRaw:
          { alpha: SizedF.unwrapF b0.wrapDv.plonk.alpha
          , beta: SizedF.unwrapF b0.wrapDv.plonk.beta
          , gamma: SizedF.unwrapF b0.wrapDv.plonk.gamma
          , zeta: SizedF.unwrapF b0.wrapDv.plonk.zeta
          }
      , wrapPrevEvals: b1WrapPrevEvals
      , wrapBranchData: b0.wrapDv.branchData
      , wrapSpongeDigest: b0.wrapDv.spongeDigestBeforeEvaluations
      , mustVerify: true
      , wrapOwnPaddedBpChals: b1WrapOwnPaddedBpChals
      , stepAdvicePrevEvals: b1WrapPrevEvals
      , fopState:
          { deferredValues:
              { plonk: b0.wrapDv.plonk
              , combinedInnerProduct: b0.wrapDv.combinedInnerProduct
              , xi: b0.wrapDv.xi
              , bulletproofChallenges: b0.wrapDv.bulletproofPrechallenges
              , b: b0.wrapDv.b
              }
          , shouldFinalize: false
          , spongeDigestBeforeEvaluations: F b0.wrapDv.spongeDigestBeforeEvaluations
          }
      , kimchiPrevChallengesExpanded:
          map
            (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
            b0.wrapDv.bulletproofPrechallenges
      , prevChallengesForStepHash:
          Vector.replicate Dummy.dummyIpaChallenges.stepExpanded
      }

  -- ===== b1 step prove =====
  b1Res <- liftEffect $ runExceptT $
    stepSolveAndProve
      @(PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil)
      @34
      @(F StepField)
      @(FVar StepField)
      @Unit
      @Unit
      @(F StepField)
      @(FVar StepField)
      ctx
      (simpleChainRule (F zero))
      stepCR
      b1Advice
  b1Result <- case b1Res of
    Left e -> liftEffect $ Exc.throw ("b1 stepSolveAndProve: " <> show e)
    Right r -> pure r

  -- ===== b1 wrap compute deferred values =====
  let
    b1StepKimchiPrevChalsExpanded :: Vector _ StepField
    b1StepKimchiPrevChalsExpanded =
      map
        (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
        b0.wrapDv.bulletproofPrechallenges

    b1StepOracles :: OraclesResult StepField
    b1StepOracles = ProofFFI.pallasProofOracles stepCR.verifierIndex
      { proof: b1Result.proof
      , publicInput: b1Result.publicInputs
      , prevChallenges:
          [ { sgX: b0StepSg.x
            , sgY: b0StepSg.y
            , challenges: Vector.toUnfoldable b1StepKimchiPrevChalsExpanded
            }
          ]
      }

    b1StepAllEvals :: AllEvals StepField
    b1StepAllEvals =
      { ftEval1: b1StepOracles.ftEval1
      , publicEvals:
          { zeta: b1StepOracles.publicEvalZeta
          , omegaTimesZeta: b1StepOracles.publicEvalZetaOmega
          }
      , zEvals: ProofFFI.proofZEvals b1Result.proof
      , witnessEvals: ProofFFI.proofWitnessEvals b1Result.proof
      , coeffEvals: ProofFFI.proofCoefficientEvals b1Result.proof
      , sigmaEvals: ProofFFI.proofSigmaEvals b1Result.proof
      , indexEvals: ProofFFI.proofIndexEvals b1Result.proof
      }

    b1WrapDvInput :: WrapDeferredValuesInput 1
    b1WrapDvInput =
      { proof: b1Result.proof
      , verifierIndex: stepCR.verifierIndex
      , publicInput: b1Result.publicInputs
      , allEvals: b1StepAllEvals
      , pEval0Chunks: [ b1StepOracles.publicEvalZeta ]
      , domainLog2: stepDomainLog2
      , zkRows: 3
      , srsLengthLog2: 16
      , generator: (domainGenerator stepDomainLog2 :: StepField)
      , shifts: (domainShifts stepDomainLog2 :: Vector 7 StepField)
      , vanishesOnZk: ProofFFI.permutationVanishingPolynomial
          { domainLog2: stepDomainLog2, zkRows: 3, pt: b1StepOracles.zeta }
      , omegaForLagrange: \_ -> one
      , endo: stepEndoScalar
      , linearizationPoly: Linearization.pallas
      , prevSgs: b0StepSg :< Vector.nil
      , prevChallenges: b1StepKimchiPrevChalsExpanded :< Vector.nil
      , proofsVerifiedMask: false :< true :< Vector.nil
      }

    b1WrapDv = wrapComputeDeferredValues b1WrapDvInput

    b1MsgForNextStepDigest :: StepField
    b1MsgForNextStepDigest = unsafePartial $ fromJust $
      Array.index b1Result.publicInputs 32

    b1WrapProofSg :: AffinePoint WrapField
    b1WrapProofSg = ProofFFI.pallasProofOpeningSg b1Result.proof

    PerProofUnfinalized b1StepUnfRec0 =
      Vector.head (unwrap b1Advice).publicUnfinalizedProofs

    b1MsgForNextWrapRealChals :: Vector WrapIPARounds WrapField
    b1MsgForNextWrapRealChals =
      map
        ( \(UnChecked v) ->
            toFieldPure (coerceViaBits v :: SizedF 128 WrapField)
              msgForNextWrapWrapEndo
        )
        b1StepUnfRec0.bulletproofChallenges

    b1MsgForNextWrapDigest :: WrapField
    b1MsgForNextWrapDigest =
      hashMessagesForNextWrapProof
        { sg: b1WrapProofSg
        , expandedChallenges: b1MsgForNextWrapRealChals
        , dummyChallenges: b0.msgForNextWrapDummyChals
        }

    b1WrapPublicInput = assembleWrapMainInput
      { deferredValues: b1WrapDv
      , messagesForNextStepProofDigest: b1MsgForNextStepDigest
      , messagesForNextWrapProofDigest: b1MsgForNextWrapDigest
      }

    b1StepPerProof
      :: PerProofUnfinalized WrapIPARounds (Type2 (F WrapField))
           (F WrapField)
           Boolean
    b1StepPerProof = PerProofUnfinalized
      { combinedInnerProduct: toShifted (fromShifted b1StepUnfRec0.combinedInnerProduct :: F WrapField)
      , b: toShifted (fromShifted b1StepUnfRec0.b :: F WrapField)
      , zetaToSrsLength: toShifted (fromShifted b1StepUnfRec0.zetaToSrsLength :: F WrapField)
      , zetaToDomainSize: toShifted (fromShifted b1StepUnfRec0.zetaToDomainSize :: F WrapField)
      , perm: toShifted (fromShifted b1StepUnfRec0.perm :: F WrapField)
      , spongeDigest: F (fromBigInt (toBigInt (case b1StepUnfRec0.spongeDigest of F x -> x)) :: WrapField)
      , beta: UnChecked (coerceViaBits (case b1StepUnfRec0.beta of UnChecked v -> v))
      , gamma: UnChecked (coerceViaBits (case b1StepUnfRec0.gamma of UnChecked v -> v))
      , alpha: UnChecked (coerceViaBits (case b1StepUnfRec0.alpha of UnChecked v -> v))
      , zeta: UnChecked (coerceViaBits (case b1StepUnfRec0.zeta of UnChecked v -> v))
      , xi: UnChecked (coerceViaBits (case b1StepUnfRec0.xi of UnChecked v -> v))
      , bulletproofChallenges:
          map (\(UnChecked v) -> UnChecked (coerceViaBits v)) b1StepUnfRec0.bulletproofChallenges
      , shouldFinalize: b1StepUnfRec0.shouldFinalize
      }

    b1WrapB0Oracles :: OraclesResult WrapField
    b1WrapB0Oracles = ProofFFI.vestaProofOracles wrapCR.verifierIndex
      { proof: b0.wrapResult.proof
      , publicInput: b0.wrapResult.publicInputs
      , prevChallenges:
          [ { sgX: b0.wrapSg.x
            , sgY: b0.wrapSg.y
            , challenges:
                Vector.toUnfoldable
                  ( map (fromBigInt <<< toBigInt) Dummy.dummyIpaChallenges.wrapExpanded
                      :: Vector WrapIPARounds WrapField
                  )
            }
          , { sgX: b0.b0ChalPolyComm.x
            , sgY: b0.b0ChalPolyComm.y
            , challenges: Vector.toUnfoldable b0.msgForNextWrapRealChals
            }
          ]
      }

    b1WrapPrevEvalsForAdvice :: StepAllEvals (F WrapField)
    b1WrapPrevEvalsForAdvice =
      let
        peWF pe' = PointEval
          { zeta: F pe'.zeta
          , omegaTimesZeta: F pe'.omegaTimesZeta
          }
      in
        StepAllEvals
          { ftEval1: F b1WrapB0Oracles.ftEval1
          , publicEvals: PointEval
              { zeta: F b1WrapB0Oracles.publicEvalZeta
              , omegaTimesZeta: F b1WrapB0Oracles.publicEvalZetaOmega
              }
          , zEvals: peWF (ProofFFI.proofZEvals b0.wrapResult.proof)
          , witnessEvals: map peWF (ProofFFI.proofWitnessEvals b0.wrapResult.proof)
          , coeffEvals: map peWF (ProofFFI.proofCoefficientEvals b0.wrapResult.proof)
          , sigmaEvals: map peWF (ProofFFI.proofSigmaEvals b0.wrapResult.proof)
          , indexEvals: map peWF (ProofFFI.proofIndexEvals b0.wrapResult.proof)
          }

    b1WrapAdviceInput :: BuildWrapAdviceInput 1 (Slots1 1)
    b1WrapAdviceInput =
      { stepProof: b1Result.proof
      , whichBranch: F zero
      , prevUnfinalizedProofs: b1StepPerProof :< Vector.nil
      , prevMessagesForNextStepProofHash:
          F (fromBigInt (toBigInt b1MsgForNextStepDigest) :: WrapField)
      , prevStepAccs:
          WeierstrassAffinePoint { x: F b0StepSg.x, y: F b0StepSg.y } :< Vector.nil
      , prevOldBpChals: slots1 ((map F b0.msgForNextWrapRealChals) :< Vector.nil)
      , prevEvals: b1WrapPrevEvalsForAdvice :< Vector.nil
      , prevWrapDomainIndices: F (fromInt 1 :: WrapField) :< Vector.nil
      }

    b1WrapAdvice :: WrapAdvice 1 (Slots1 1)
    b1WrapAdvice = buildWrapAdvice b1WrapAdviceInput

    b1WrapProveCtx =
      { wrapMainConfig:
          buildWrapMainConfig vestaSrs stepCR.verifierIndex
            { stepWidth: 1, domainLog2: stepDomainLog2 }
      , crs: pallasProofCrs
      , publicInput: b1WrapPublicInput
      , advice: b1WrapAdvice
      , debug: false
      , kimchiPrevChallenges:
          let
            padEntry =
              { sgX: b0.wrapSg.x
              , sgY: b0.wrapSg.y
              , challenges: map (fromBigInt <<< toBigInt)
                  Dummy.dummyIpaChallenges.wrapExpanded
              }
            realEntry =
              { sgX: b1ChalPolyComm.x
              , sgY: b1ChalPolyComm.y
              , challenges: b1MsgForNextWrapRealChals
              }
          in
            padEntry :< realEntry :< Vector.nil
      }

  b1WrapRes <- liftEffect $ runExceptT $
    wrapSolveAndProve @1 @(Slots1 1) b1WrapProveCtx wrapCR
  b1WrapResult <- case b1WrapRes of
    Left e -> liftEffect $ Exc.throw ("b1 wrapSolveAndProve: " <> show e)
    Right r -> pure r

  pure
    { b0
    , wrapDvInput: b1WrapDvInput
    , wrapDv: b1WrapDv
    , wrapResult: b1WrapResult
    , stepProofSg: b1WrapProofSg
    , messagesForNextStepProofDigest: b1MsgForNextStepDigest
    , messagesForNextWrapProofDigest: b1MsgForNextWrapDigest
    }
