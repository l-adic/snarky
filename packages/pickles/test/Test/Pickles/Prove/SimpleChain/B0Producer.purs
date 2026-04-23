-- | Minimal Simple_chain b0 producer for convergence testing.
-- |
-- | Runs the same base-case setup as `Test.Pickles.Prove.SimpleChain`'s b0
-- | block — step compile, wrap compile, base-case dummies, step advice,
-- | step prove, assemble `WrapDeferredValuesInput 1`, call
-- | `wrapComputeDeferredValues` — and returns both the input and the output
-- | for downstream convergence checks.
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
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles.Dummy (baseCaseDummies, computeDummySgValues, dummyIpaChallenges, stepDummyUnfinalizedProof, wrapDomainLog2ForProofsVerified) as Dummy
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.Proof.Dummy (dummyWrapProof)
import Pickles.ProofFFI (OraclesResult)
import Pickles.ProofFFI (pallasProofOracles, pallasProverIndexDomainLog2, permutationVanishingPolynomial, proofCoefficientEvals, proofIndexEvals, proofSigmaEvals, proofWitnessEvals, proofZEvals, vestaSrsBlindingGenerator, vestaSrsLagrangeCommitmentAt) as ProofFFI
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, WrapDeferredValuesOutput, wrapComputeDeferredValues)
import Pickles.Prove.Step (buildStepAdviceWithOracles, dummyWrapTockPublicInput, stepCompile, stepSolveAndProve)
import Pickles.Prove.Wrap (WrapCompileContext) as WP
import Pickles.Prove.Wrap (buildWrapMainConfig, wrapCompile)
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (PaddedLength, StepField)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Pickles.Wrap.Slots (Slots1)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..), FVar)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromInt)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.Prove.SimpleChain (simpleChainRule)

type SimpleChainB0Artifacts =
  { wrapDvInput :: WrapDeferredValuesInput 1
  , wrapDv :: WrapDeferredValuesOutput
  }

-- | Run the Simple_chain base-case (b0) up through the wrapComputeDeferredValues
-- | call, return both the input and the output so downstream tests can run a
-- | verifier-side `expandDeferredForVerify` against them.
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
    stepCompile @(PrevsSpecCons 1 PrevsSpecNil) @34
      @(F StepField)
      @(FVar StepField)
      @Unit
      @Unit
      @(F StepField)
      @(FVar StepField)
      ctx
      (simpleChainRule (F (negate one)))

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
      { wrapDomainLog2
      , wrapVK: wrapCR.verifierIndex
      , prevPublicInput: F (negate one)
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
  { advice: realAdvice } <- liftEffect $
    buildStepAdviceWithOracles @1 @(PrevsSpecCons 1 PrevsSpecNil)
      { publicInput: F zero
      , prevPublicInput: F (negate one)
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
    stepSolveAndProve @(PrevsSpecCons 1 PrevsSpecNil) @34
      @(F StepField)
      @(FVar StepField)
      @Unit
      @Unit
      @(F StepField)
      @(FVar StepField)
      ctx
      (simpleChainRule (F (negate one)))
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

  pure { wrapDvInput, wrapDv }
