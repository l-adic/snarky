-- | Minimal Simple_chain b0 producer for convergence testing.
-- |
-- | Runs the same base-case setup as `Test.Pickles.Prove.SimpleChain`'s b0
-- | block — step compile, wrap compile, base-case dummies, step advice,
-- | step prove, assemble `WrapDeferredValuesInput 1`, call
-- | `wrapComputeDeferredValues`, build wrap advice, run `wrapSolveAndProve` —
-- | and returns artifacts sufficient for both:
-- |
-- | * `Test.Pickles.Verify.ExpandDeferredEq` (convergence check on the
-- |   stage-1 deferred-values expansion)
-- | * `Test.Pickles.Verify.VerifySmoke` (end-to-end `Pickles.verify` of the
-- |   resulting wrap proof)
-- |
-- | Stripped of trace emission, diagnostics, and the b1..b4 iterations.
-- | All the inductive rule and domain-log2 constants are copied from the
-- | main SimpleChain spec; kept in sync by sharing `simpleChainRule`.
module Test.Pickles.Prove.SimpleChain.B0Producer
  ( SimpleChainB0Artifacts
  , produceSimpleChainB0
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (unwrap)
import Data.Tuple (Tuple)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Partial.Unsafe (unsafePartial)
import Pickles.Dummy (baseCaseDummies, computeDummySgValues, dummyIpaChallenges, stepDummyUnfinalizedProof, wrapDomainLog2ForProofsVerified) as Dummy
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.Proof.Dummy (dummyWrapProof)
import Pickles.ProofFFI (OraclesResult)
import Pickles.ProofFFI (pallasProofOpeningSg, pallasProofOracles, pallasProverIndexDomainLog2, permutationVanishingPolynomial, proofCoefficientEvals, proofIndexEvals, proofSigmaEvals, proofWitnessEvals, proofZEvals, vestaProofOracles, vestaSrsBlindingGenerator, vestaSrsLagrangeCommitmentAt) as ProofFFI
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, WrapDeferredValuesOutput, assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Prove.Step (StepCompileResult, StepProveResult, buildStepAdviceWithOracles, dummyWrapTockPublicInput, stepCompile, stepSolveAndProve)
import Pickles.Prove.Wrap (BuildWrapAdviceInput, WrapAdvice, WrapCompileResult, WrapProveResult, buildWrapAdvice, buildWrapMainConfig, wrapCompile, wrapSolveAndProve)
import Pickles.Prove.Wrap (WrapCompileContext) as WP
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (PaddedLength, PerProofUnfinalized(..), PointEval(..), StatementIO(..), StepAllEvals(..), StepField, WrapField, WrapIPARounds)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProof, hashMessagesForNextWrapProofPureGeneral)
import Pickles.Wrap.Slots (Slots1, slots1)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..), FVar, UnChecked(..), coerceViaBits)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (Type2, fromShifted, toShifted)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, fromInt, toBigInt)
import Snarky.Curves.Class as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Test.Pickles.Prove.SimpleChain (simpleChainRule)

type SimpleChainB0Artifacts =
  { stepCR :: StepCompileResult
  , wrapCR :: WrapCompileResult
  -- | Inputs handed to `wrapComputeDeferredValues` — for the
  -- | `expandDeferredForVerify` convergence test.
  , wrapDvInput :: WrapDeferredValuesInput 1
  -- | Output of `wrapComputeDeferredValues`.
  , wrapDv :: WrapDeferredValuesOutput
  -- | The finished wrap proof + flattened public-input array.
  , wrapResult :: WrapProveResult
  -- | The step proof's IPA opening sg (Vesta point, Fq coords) =
  -- | `messages_for_next_wrap_proof.challenge_polynomial_commitment`.
  , stepProofSg :: AffinePoint WrapField
  -- | Pre-hashed `messages_for_next_step_proof` digest.
  , messagesForNextStepProofDigest :: StepField
  -- | Pre-hashed `messages_for_next_wrap_proof` digest.
  , messagesForNextWrapProofDigest :: WrapField
  -- | The b0 step-proof result (the proof + public-input array).
  -- | Exposed for downstream iterations (b1) that need to read the
  -- | full step proof the b0 wrap wrapped. `outputSize = 34` for
  -- | Simple_chain N=1: 32 unfinalized slots + 1 outer hash + 1 width.
  , stepResult :: StepProveResult 34
  -- | `challengePolynomialCommitment` from `buildStepAdviceWithOracles`
  -- | — used by b1's kimchi `prev_challenges` slot-1 entry. Coords
  -- | are in `StepField` (= `Vesta.ScalarField`), matching the
  -- | `vestaCreateProofWithPrev` FFI's `sgX / sgY` expectation.
  , b0ChalPolyComm :: AffinePoint StepField
  -- | b0's real unfinalized bp-challenges, wrap-endo-expanded (= what
  -- | wrap_b0 absorbed into its `messages_for_next_wrap_proof` hash
  -- | real slot). Used by b1's kimchi `prev_challenges` slot-1 entry
  -- | + as step_b1's `prev_challenges` value.
  , msgForNextWrapRealChals :: Vector WrapIPARounds WrapField
  -- | Dummy wrap-expanded IPA challenges for `wrap_hack` padding slot
  -- | in any hash of `messages_for_next_wrap_proof`.
  , msgForNextWrapDummyChals :: Vector WrapIPARounds WrapField
  -- | Dummy Pallas sg (Wrap.Ipa sg). Used by b1's kimchi-prev-chal
  -- | padding slot.
  , wrapSg :: AffinePoint StepField
  }

produceSimpleChainB0
  :: { vestaSrs :: CRS VestaG
     , lagrangeSrs :: CRS PallasG
     , pallasProofCrs :: CRS PallasG
     }
  -> Aff SimpleChainB0Artifacts
produceSimpleChainB0 { vestaSrs, lagrangeSrs, pallasProofCrs } = do
  let
    bcd = Dummy.baseCaseDummies { maxProofsVerified: 1 }
    dummySgValues = Dummy.computeDummySgValues bcd lagrangeSrs vestaSrs
    wrapSg = dummySgValues.ipa.wrap.sg
    stepSg = dummySgValues.ipa.step.sg

    wrapDomainLog2 = 14

    lagrangeAtD14 =
      mkConstLagrangeBaseLookup \i ->
        (coerce (ProofFFI.vestaSrsLagrangeCommitmentAt lagrangeSrs wrapDomainLog2 i))
          :: AffinePoint (F StepField)

    srsData =
      { perSlotLagrangeAt: lagrangeAtD14 :< Vector.nil
      , blindingH:
          (coerce $ ProofFFI.vestaSrsBlindingGenerator lagrangeSrs)
            :: AffinePoint (F StepField)
      , perSlotFopDomainLog2: wrapDomainLog2 :< Vector.nil
      , perSlotKnownWrapKeys: Nothing :< Vector.nil
      }

    dummySg :: AffinePoint StepField
    dummySg = wrapSg

    ctx = { srsData, dummySg, crs: vestaSrs, debug: false }

  -- Step compile.
  stepCR <- liftEffect $
    stepCompile @(PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil) @34
      @(Tuple (StatementIO (F StepField) Unit) Unit)
      @(F StepField)
      @(FVar StepField)
      @Unit
      @Unit
      @(F StepField)
      @(FVar StepField)
      ctx
      (simpleChainRule)

  let stepDomainLog2 = ProofFFI.pallasProverIndexDomainLog2 stepCR.proverIndex

  -- Wrap compile.
  let
    wrapCtx :: WP.WrapCompileContext 1
    wrapCtx =
      { wrapMainConfig:
          buildWrapMainConfig vestaSrs stepCR.verifierIndex
            { stepWidth: 1, domainLog2: stepDomainLog2 }
      , crs: pallasProofCrs
      }
  wrapCR <- liftEffect $ wrapCompile @1 @(Slots1 1) wrapCtx

  -- Step advice for the base case.
  let
    baseCaseDummyChalPoly =
      { sg: wrapSg, challenges: Dummy.dummyIpaChallenges.wrapExpanded }
    baseCaseWrapPI = dummyWrapTockPublicInput @1
      { stepDomainLog2: wrapDomainLog2
      , wrapVK: wrapCR.verifierIndex
      , prevStatement: StatementIO { input: F (negate one), output: unit }
      , wrapSg
      , stepSg
      , msgWrapDigest: hashMessagesForNextWrapProofPureGeneral
          { sg: stepSg
          , paddedChallenges:
              Dummy.dummyIpaChallenges.wrapExpanded
                :< Dummy.dummyIpaChallenges.wrapExpanded
                :< Vector.nil
          }
      , fopProofState: Dummy.stepDummyUnfinalizedProof @1 bcd
          { domainLog2: Dummy.wrapDomainLog2ForProofsVerified 1 }
          (map SizedF.wrapF bcd.ipaStepChallenges)
      }
  { advice: realAdvice, challengePolynomialCommitment: b0ChalPolyComm } <-
    liftEffect $
      buildStepAdviceWithOracles @1 @(PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil)
        { publicInput: F zero
        , prevStatement: StatementIO { input: F (negate one), output: unit }
        , wrapDomainLog2
        , stepDomainLog2: wrapDomainLog2
        , wrapVK: wrapCR.verifierIndex
        , stepOpeningSg: stepSg
        , kimchiPrevSg: stepSg
        , wrapProof: dummyWrapProof bcd
        , wrapPublicInput: baseCaseWrapPI
        , prevChalPolys:
            baseCaseDummyChalPoly :< baseCaseDummyChalPoly :< Vector.nil
              :: Vector PaddedLength _
        , wrapPlonkRaw:
            { alpha: bcd.proofDummy.plonk.alpha
            , beta: bcd.proofDummy.plonk.beta
            , gamma: bcd.proofDummy.plonk.gamma
            , zeta: bcd.proofDummy.plonk.zeta
            }
        , wrapPrevEvals: bcd.proofDummy.prevEvals
        , wrapBranchData:
            { domainLog2: fromInt wrapDomainLog2 :: StepField
            , proofsVerifiedMask: false :< true :< Vector.nil
            }
        , wrapSpongeDigest: zero
        , mustVerify: false
        , wrapOwnPaddedBpChals:
            Dummy.dummyIpaChallenges.wrapExpanded
              :< Dummy.dummyIpaChallenges.wrapExpanded
              :< Vector.nil
        , fopState: Dummy.stepDummyUnfinalizedProof @1 bcd
            { domainLog2: Dummy.wrapDomainLog2ForProofsVerified 1 }
            (map SizedF.wrapF bcd.ipaStepChallenges)
        , stepAdvicePrevEvals: bcd.proofDummy.prevEvals
        , kimchiPrevChallengesExpanded: Dummy.dummyIpaChallenges.stepExpanded
        , prevChallengesForStepHash: Vector.replicate Dummy.dummyIpaChallenges.stepExpanded
        }

  -- Step prove.
  stepRes <- liftEffect $ runExceptT $
    stepSolveAndProve @(PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil) @34
      @(Tuple (StatementIO (F StepField) Unit) Unit)
      @(F StepField)
      @(FVar StepField)
      @Unit
      @Unit
      @(F StepField)
      @(FVar StepField)
      ctx
      (simpleChainRule)
      stepCR
      realAdvice
  result <- case stepRes of
    Left e -> liftEffect $ Exc.throw ("stepSolveAndProve: " <> show e)
    Right r -> pure r

  -- Build wrapDvInput (N=1) and run wrapComputeDeferredValues.
  let
    stepOracles :: OraclesResult StepField
    stepOracles = ProofFFI.pallasProofOracles stepCR.verifierIndex
      { proof: result.proof
      , publicInput: result.publicInputs
      , prevChallenges:
          [ { sgX: stepSg.x
            , sgY: stepSg.y
            , challenges: Vector.toUnfoldable Dummy.dummyIpaChallenges.stepExpanded
            }
          ]
      }

    stepAllEvals :: AllEvals StepField
    stepAllEvals =
      { ftEval1: stepOracles.ftEval1
      , publicEvals:
          { zeta: stepOracles.publicEvalZeta
          , omegaTimesZeta: stepOracles.publicEvalZetaOmega
          }
      , zEvals: ProofFFI.proofZEvals result.proof
      , witnessEvals: ProofFFI.proofWitnessEvals result.proof
      , coeffEvals: ProofFFI.proofCoefficientEvals result.proof
      , sigmaEvals: ProofFFI.proofSigmaEvals result.proof
      , indexEvals: ProofFFI.proofIndexEvals result.proof
      }

    stepEndoScalar :: StepField
    stepEndoScalar =
      let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

    wrapDvInput :: WrapDeferredValuesInput 1
    wrapDvInput =
      { proof: result.proof
      , verifierIndex: stepCR.verifierIndex
      , publicInput: result.publicInputs
      , allEvals: stepAllEvals
      , pEval0Chunks: [ stepOracles.publicEvalZeta ]
      , domainLog2: stepDomainLog2
      , zkRows: 3
      , srsLengthLog2: 16
      , generator: (domainGenerator stepDomainLog2 :: StepField)
      , shifts: (domainShifts stepDomainLog2 :: Vector 7 StepField)
      , vanishesOnZk: ProofFFI.permutationVanishingPolynomial
          { domainLog2: stepDomainLog2, zkRows: 3, pt: stepOracles.zeta }
      , omegaForLagrange: \_ -> one
      , endo: stepEndoScalar
      , linearizationPoly: Linearization.pallas
      , prevSgs: stepSg :< Vector.nil
      , prevChallenges: Dummy.dummyIpaChallenges.stepExpanded :< Vector.nil
      , proofsVerifiedMask: false :< true :< Vector.nil
      }

    wrapDv = wrapComputeDeferredValues wrapDvInput

  -- Message digests for the wrap statement.
  let
    -- OCaml `messages_for_next_step_proof` digest = step PI[32] (in-circuit
    -- hash_messages_for_next_step_proof result).
    msgForNextStepDigest :: StepField
    msgForNextStepDigest = unsafePartial $ fromJust $
      Array.index result.publicInputs 32

    wrapProofSg :: AffinePoint WrapField
    wrapProofSg = ProofFFI.pallasProofOpeningSg result.proof

    msgForNextWrapDummyChals :: Vector WrapIPARounds WrapField
    msgForNextWrapDummyChals =
      map (fromBigInt <<< toBigInt) Dummy.dummyIpaChallenges.wrapExpanded

    PerProofUnfinalized stepUnfRec0 =
      Vector.head (unwrap realAdvice).publicUnfinalizedProofs

    msgForNextWrapWrapEndo :: WrapField
    msgForNextWrapWrapEndo =
      let
        Curves.EndoScalar e = Curves.endoScalar @Pallas.BaseField @WrapField
      in
        e

    msgForNextWrapRealChals :: Vector WrapIPARounds WrapField
    msgForNextWrapRealChals =
      map
        ( \(UnChecked v) ->
            toFieldPure (coerceViaBits v :: SizedF.SizedF 128 WrapField)
              msgForNextWrapWrapEndo
        )
        stepUnfRec0.bulletproofChallenges

    msgForNextWrapDigest :: WrapField
    msgForNextWrapDigest =
      hashMessagesForNextWrapProof
        { sg: wrapProofSg
        , expandedChallenges: msgForNextWrapRealChals
        , dummyChallenges: msgForNextWrapDummyChals
        }

  -- Build WrapAdvice for base case.
  let
    wrapPublicInput = assembleWrapMainInput
      { deferredValues: wrapDv
      , messagesForNextStepProofDigest: msgForNextStepDigest
      , messagesForNextWrapProofDigest: msgForNextWrapDigest
      }

    PerProofUnfinalized stepUnfRec = Vector.head (unwrap realAdvice).publicUnfinalizedProofs

    stepPerProof
      :: PerProofUnfinalized WrapIPARounds (Type2 (F WrapField))
           (F WrapField)
           Boolean
    stepPerProof = PerProofUnfinalized
      { combinedInnerProduct: toShifted (fromShifted stepUnfRec.combinedInnerProduct :: F WrapField)
      , b: toShifted (fromShifted stepUnfRec.b :: F WrapField)
      , zetaToSrsLength: toShifted (fromShifted stepUnfRec.zetaToSrsLength :: F WrapField)
      , zetaToDomainSize: toShifted (fromShifted stepUnfRec.zetaToDomainSize :: F WrapField)
      , perm: toShifted (fromShifted stepUnfRec.perm :: F WrapField)
      , spongeDigest: F (fromBigInt (toBigInt (case stepUnfRec.spongeDigest of F x -> x)) :: WrapField)
      , beta: UnChecked (coerceViaBits (case stepUnfRec.beta of UnChecked v -> v))
      , gamma: UnChecked (coerceViaBits (case stepUnfRec.gamma of UnChecked v -> v))
      , alpha: UnChecked (coerceViaBits (case stepUnfRec.alpha of UnChecked v -> v))
      , zeta: UnChecked (coerceViaBits (case stepUnfRec.zeta of UnChecked v -> v))
      , xi: UnChecked (coerceViaBits (case stepUnfRec.xi of UnChecked v -> v))
      , bulletproofChallenges:
          map (\(UnChecked v) -> UnChecked (coerceViaBits v)) stepUnfRec.bulletproofChallenges
      , shouldFinalize: stepUnfRec.shouldFinalize
      }

    dummyStepAccPoint :: WeierstrassAffinePoint VestaG (F WrapField)
    dummyStepAccPoint = WeierstrassAffinePoint
      { x: F stepSg.x, y: F stepSg.y }

    dummyWrapBpChals :: Vector WrapIPARounds (F WrapField)
    dummyWrapBpChals =
      map (F <<< fromBigInt <<< toBigInt) Dummy.dummyIpaChallenges.wrapExpanded

    dummyWrapXhat :: { zeta :: WrapField, omegaTimesZeta :: WrapField }
    dummyWrapXhat =
      let
        toFFI r = { sgX: r.sg.x, sgY: r.sg.y, challenges: Vector.toUnfoldable r.challenges }
        o = ProofFFI.vestaProofOracles wrapCR.verifierIndex
          { proof: dummyWrapProof bcd
          , publicInput: baseCaseWrapPI
          , prevChallenges: map toFFI [ baseCaseDummyChalPoly, baseCaseDummyChalPoly ]
          }
      in
        { zeta: o.publicEvalZeta, omegaTimesZeta: o.publicEvalZetaOmega }

    realPrevEvalsW :: StepAllEvals (F WrapField)
    realPrevEvalsW =
      let
        de = bcd.dummyEvals
        pe pe' = PointEval { zeta: F pe'.zeta, omegaTimesZeta: F pe'.omegaTimesZeta }
      in
        StepAllEvals
          { ftEval1: F de.ftEval1
          , publicEvals: PointEval
              { zeta: F dummyWrapXhat.zeta
              , omegaTimesZeta: F dummyWrapXhat.omegaTimesZeta
              }
          , zEvals: pe de.zEvals
          , witnessEvals: map pe de.witnessEvals
          , coeffEvals: map pe de.coeffEvals
          , sigmaEvals: map pe de.sigmaEvals
          , indexEvals: map pe de.indexEvals
          }

    wrapAdviceInput :: BuildWrapAdviceInput 1 (Slots1 1)
    wrapAdviceInput =
      { stepProof: result.proof
      , whichBranch: F zero
      , prevUnfinalizedProofs: stepPerProof :< Vector.nil
      , prevMessagesForNextStepProofHash:
          F (fromBigInt (toBigInt msgForNextStepDigest) :: WrapField)
      , prevStepAccs: dummyStepAccPoint :< Vector.nil
      , prevOldBpChals: slots1 (dummyWrapBpChals :< Vector.nil)
      , prevEvals: realPrevEvalsW :< Vector.nil
      , prevWrapDomainIndices: F (fromInt 1 :: WrapField) :< Vector.nil
      }

    wrapAdvice :: WrapAdvice 1 (Slots1 1)
    wrapAdvice = buildWrapAdvice wrapAdviceInput

    wrapProveCtx =
      { wrapMainConfig: wrapCtx.wrapMainConfig
      , crs: pallasProofCrs
      , publicInput: wrapPublicInput
      , advice: wrapAdvice
      , debug: false
      , kimchiPrevChallenges:
          let
            padEntry =
              { sgX: wrapSg.x
              , sgY: wrapSg.y
              , challenges: map (fromBigInt <<< toBigInt)
                  Dummy.dummyIpaChallenges.wrapExpanded
              }
            realEntry =
              { sgX: b0ChalPolyComm.x
              , sgY: b0ChalPolyComm.y
              , challenges: msgForNextWrapRealChals
              }
          in
            padEntry :< realEntry :< Vector.nil
      }

  wrapRes <- liftEffect $ runExceptT $
    wrapSolveAndProve @1 @(Slots1 1) wrapProveCtx wrapCR
  wrapResult <- case wrapRes of
    Left e -> liftEffect $ Exc.throw ("wrapSolveAndProve: " <> show e)
    Right r -> pure r

  pure
    { stepCR
    , wrapCR
    , wrapDvInput
    , wrapDv
    , wrapResult
    , stepProofSg: wrapProofSg
    , messagesForNextStepProofDigest: msgForNextStepDigest
    , messagesForNextWrapProofDigest: msgForNextWrapDigest
    , stepResult: result
    , b0ChalPolyComm
    , msgForNextWrapRealChals
    , msgForNextWrapDummyChals
    , wrapSg
    }
