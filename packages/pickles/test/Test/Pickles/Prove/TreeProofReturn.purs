-- | PureScript-side analog of OCaml's `Tree_proof_return` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:315-429` +
-- |  `mina/src/lib/crypto/pickles/dump_tree_proof_return/dump_tree_proof_return.ml`).
-- |
-- | Tree_proof_return is the first heterogeneous-prevs target in our
-- | convergence loop:
-- |
-- |   prevs = [No_recursion_return.tag; self]
-- |   max_proofs_verified = N2
-- |   per-slot widths      = [0, 2]
-- |   override_wrap_domain = N1  → wrap_domains.h = 2^13
-- |   public_input         = Output Field
-- |
-- | The base case (`is_base_case = true`):
-- |   slot 0: real No_recursion_return proof (always verified)
-- |   slot 1: dummy N2 proof at domain_log2=15 (NOT verified)
-- |
-- | Iteration ladder (matching convention from the NoRecursionReturn
-- | and Simple_chain tests):
-- |
-- |   iter 1: compile No_recursion_return step+wrap (reuse via helper)
-- |           compile Tree_proof_return step+wrap
-- |   iter 2: No_recursion_return step+wrap prove (slot 0 input)
-- |           Tree_proof_return step+wrap prove (base case)
-- |   iter 3: witness-matrix diff vs OCaml at Rust boundary
-- |
-- | Optional env vars at runtime:
-- | - `KIMCHI_DETERMINISTIC_SEED` — override the kimchi RNG seed
-- |   (defaults to 42 in crypto-provider's `deterministic_rng.rs`).
-- | - `KIMCHI_WITNESS_DUMP` — path template for witness dump.
-- | - `PICKLES_TRACE_FILE` — trace log path.
module Test.Pickles.Prove.TreeProofReturn
  ( spec
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Foldable (for_)
import Data.Int.Bits as Int
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
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Prove.Step (StepAdvice(..), StepRule, buildStepAdviceWithOracles, dummyWrapTockPublicInput, extractWrapVKCommsAdvice, extractWrapVKForStepHash, stepCompile, stepSolveAndProve)
import Pickles.Prove.Wrap (BuildWrapAdviceInput, WrapAdvice, buildWrapAdvice, buildWrapMainConfig, extractStepVKComms, wrapCompile, wrapSolveAndProve)
import Pickles.Prove.Wrap (WrapCompileContext) as WP
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Trace as Trace
import Pickles.Types (PaddedLength, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, StepIPARounds, WrapField, WrapIPARounds)
import Pickles.Util.Fatal (fromJust')
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Pickles.Wrap.Slots (Slots2, slots2)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F(..), FVar, SizedF, UnChecked(..), add_, coerceViaBits, const_, exists, if_, not_, true_)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (SplitField, Type2, toFieldPure)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, fromInt, toBigInt)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (fromShifted, toShifted)
import Test.Pickles.Prove.NoRecursionReturn.Producer (produceNoRecursionReturn)
import Test.Spec (SpecT, describe, it)

-- | Tree_proof_return prev-spec: slot 0 has width 0 (No_recursion_return
-- | proof), slot 1 has width 2 (self).
type TreeProofReturnPrevsSpec = PrevsSpecCons 0 (PrevsSpecCons 2 PrevsSpecNil)

-- | Tree_proof_return rule — N=2 Output mode with heterogeneous prevs.
-- | Mirrors OCaml test_no_sideloaded.ml:336-386 and the identical
-- | structure in dump_tree_proof_return.ml:130-170.
-- |
-- | Prev slots:
-- |   slot 0 (width 0): No_recursion_return proof, always verified
-- |   slot 1 (width 2): self proof, verified iff not base case
-- |
-- | Output: `if is_base_case then 0 else 1 + prev`
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
  -- Prev input witnesses: slot-0 (No_recursion_return) input value,
  -- slot-1 (self) input value. Threaded in as constants via `exists`
  -- in the same pattern `simpleChainRule` uses for its prev value.
  nrrInput <- exists $ lift $ pure nrrInputVal
  prevInput <- exists $ lift $ pure prevInputVal
  isBaseCaseBool <- exists $ lift $ pure isBaseCase
  let proofMustVerifySlot1 = not_ isBaseCaseBool
  -- self = if is_base_case then 0 else 1 + prev
  let onePlusPrev = add_ (const_ one) prevInput
  self <- if_ isBaseCaseBool (const_ zero) onePlusPrev
  pure
    { prevPublicInputs: nrrInput :< prevInput :< Vector.nil
    , proofMustVerify: true_ :< proofMustVerifySlot1 :< Vector.nil
    , publicOutput: self
    }

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.TreeProofReturn" do
  it "Tree_proof_return base case (step0 + wrap0) compiles" \_ -> do
    -- ===== SRS setup (same depths as NoRecursionReturn / Simple_chain) =====
    let pallasWrapSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    let lagrangeSrs = pallasWrapSrs
    vestaSrs <- liftEffect $ createCRS @StepField

    -- ===== Phase 1: NRR step + wrap via the producer =====
    -- Produces real NRR step + wrap proofs (counter=0, counter=1 in
    -- KIMCHI_WITNESS_DUMP), emits the NRR trace-block prefix the
    -- Tree fixture expects at lines 1-326 (compile.stepVK.*,
    -- compile.wrapVK.*, step_main_outer.*, step.proof.public_input.*,
    -- wrap.witness.*, wrap.proof.opening.*).
    nrr <- produceNoRecursionReturn
      { vestaSrs, lagrangeSrs, pallasProofCrs: pallasWrapSrs }
    let nrrWrapVKCommsAdvice = extractWrapVKCommsAdvice nrr.wrapCR.verifierIndex

    liftEffect $ Trace.string "tree_proof_return.begin" "base_case"

    let
      -- Single source of truth for Tree's base-case dummies (N=2 →
      -- Unfinalized.Constant.dummy is forced first in the Ro sequence).
      bcd = Dummy.baseCaseDummies { maxProofsVerified: 2 }
      dummySgValues = Dummy.computeDummySgValues bcd lagrangeSrs vestaSrs
      nrrWrapSg = dummySgValues.ipa.wrap.sg
      nrrWrapDomainLog2 = nrr.wrapDomainLog2
      -- `override_wrap_domain:N1` → wrap_domains.h = 2^14 per
      -- `Common.wrap_domains` (common.ml:25-29 maps N1 → 14). This
      -- is emitted as `compile.wrap_domains.h.log2` trace — the
      -- wrap circuit's OWN domain, distinct from the STEP proof's
      -- domain-log2 that `buildWrapMainConfig` passes downstream.
      treeWrapDomainLog2 = 14

    -- ===== Phase 2: compile Tree_proof_return step =====
    -- Heterogeneous prev-slot config:
    --   slot 0: lagrange @ NRR wrap domain (2^13), FOP log2=13,
    --           known VK = NRR's wrap VK (Just)
    --   slot 1: lagrange @ self wrap domain (2^13), FOP log2=13,
    --           known VK = Nothing (self — placeholder, patched post-compile)
    let
      -- Slot 0 lagrange is at NRR's wrap domain 2^13.
      -- Slot 1 lagrange is at Tree's own wrap domain 2^14.
      mkLagrangeAtNrr = mkConstLagrangeBaseLookup \i ->
        (coerce (ProofFFI.vestaSrsLagrangeCommitmentAt pallasWrapSrs nrrWrapDomainLog2 i))
          :: AffinePoint (F StepField)
      mkLagrangeAtTree = mkConstLagrangeBaseLookup \i ->
        (coerce (ProofFFI.vestaSrsLagrangeCommitmentAt pallasWrapSrs treeWrapDomainLog2 i))
          :: AffinePoint (F StepField)

      -- `perSlotFopDomainLog2` is each slot's STEP-DOMAIN log2 (used by
      -- `finalize_other_proof` for omega/vanishing-poly constants). NOT
      -- the wrap domain — wrap domain drives lagrange only.
      --   slot 0: NRR step domain = log_size_of_group of NRR step prover
      --           index (= 9 per trace; read dynamically).
      --   slot 1: self = Tree step domain. Chicken-and-egg: we don't have
      --           Tree's compiled step domain until AFTER this compile.
      --           OCaml fixture line 328 confirms Tree step domain = 2^15;
      --           pin at 15 as a "production-known" placeholder (same
      --           pattern OCaml dump uses with hardcoded 16).
      nrrStepDomainLog2 = ProofFFI.pallasProverIndexDomainLog2 nrr.stepCR.proverIndex
      treeSelfStepDomainLog2 = 15

      treeSrsData =
        { perSlotLagrangeAt: mkLagrangeAtNrr :< mkLagrangeAtTree :< Vector.nil
        , blindingH:
            (coerce $ ProofFFI.vestaSrsBlindingGenerator lagrangeSrs)
              :: AffinePoint (F StepField)
        , perSlotFopDomainLog2: nrrStepDomainLog2 :< treeSelfStepDomainLog2 :< Vector.nil
        -- slot 0 carries the real NRR wrap VK; slot 1 is Nothing (self).
        , perSlotKnownWrapKeys: Just nrrWrapVKCommsAdvice :< Nothing :< Vector.nil
        }

      treeCtx =
        { srsData: treeSrsData
        , dummySg: nrrWrapSg
        , crs: vestaSrs
        , debug: true
        }

    -- outputSize = len*32 + 1 + len = 2*32 + 1 + 2 = 67 for N=2.
    -- Base case: is_base_case=true; NRR's output is zero (see
    -- assertion in OCaml dump_tree_proof_return.ml:78); prev=s_neg_one
    -- per dump_tree_proof_return.ml:178 (negate one, unused at base).
    let
      baseRuleArgs =
        { isBaseCase: true
        , nrrInputVal: F zero
        , prevInputVal: F (negate one)
        }
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

    -- Emit Tree step VK + compile metadata (same shape as NRR Producer).
    let treeStepDomainLog2 = ProofFFI.pallasProverIndexDomainLog2 treeStepCR.proverIndex
    let treeStepVkComms = extractStepVKComms treeStepCR.verifierIndex
    liftEffect do
      Trace.int "compile.stepVK.0.log_size_of_group" treeStepDomainLog2
      Trace.int "compile.step_domains.0.h.log2" treeStepDomainLog2
      Trace.int "compile.wrap_domains.h.log2" treeWrapDomainLog2
      for_ (Array.mapWithIndex Tuple (Vector.toUnfoldable treeStepVkComms.sigmaComm)) \(Tuple i pt) -> do
        Trace.field ("compile.stepVK.sigma." <> show i <> ".x") (coerce pt.x :: F WrapField)
        Trace.field ("compile.stepVK.sigma." <> show i <> ".y") (coerce pt.y :: F WrapField)
      for_ (Array.mapWithIndex Tuple (Vector.toUnfoldable treeStepVkComms.coefficientsComm)) \(Tuple i pt) -> do
        Trace.field ("compile.stepVK.coeff." <> show i <> ".x") (coerce pt.x :: F WrapField)
        Trace.field ("compile.stepVK.coeff." <> show i <> ".y") (coerce pt.y :: F WrapField)
      Trace.field "compile.stepVK.generic.x" (coerce treeStepVkComms.genericComm.x :: F WrapField)
      Trace.field "compile.stepVK.generic.y" (coerce treeStepVkComms.genericComm.y :: F WrapField)
      Trace.field "compile.stepVK.psm.x" (coerce treeStepVkComms.psmComm.x :: F WrapField)
      Trace.field "compile.stepVK.psm.y" (coerce treeStepVkComms.psmComm.y :: F WrapField)
      Trace.field "compile.stepVK.complete_add.x" (coerce treeStepVkComms.completeAddComm.x :: F WrapField)
      Trace.field "compile.stepVK.complete_add.y" (coerce treeStepVkComms.completeAddComm.y :: F WrapField)
      Trace.field "compile.stepVK.mul.x" (coerce treeStepVkComms.mulComm.x :: F WrapField)
      Trace.field "compile.stepVK.mul.y" (coerce treeStepVkComms.mulComm.y :: F WrapField)
      Trace.field "compile.stepVK.emul.x" (coerce treeStepVkComms.emulComm.x :: F WrapField)
      Trace.field "compile.stepVK.emul.y" (coerce treeStepVkComms.emulComm.y :: F WrapField)
      Trace.field "compile.stepVK.endomul_scalar.x" (coerce treeStepVkComms.endomulScalarComm.x :: F WrapField)
      Trace.field "compile.stepVK.endomul_scalar.y" (coerce treeStepVkComms.endomulScalarComm.y :: F WrapField)

    -- ===== Phase 3: compile Tree_proof_return wrap =====
    let
      treeWrapCtx :: WP.WrapCompileContext 1
      treeWrapCtx =
        { wrapMainConfig:
            buildWrapMainConfig vestaSrs treeStepCR.verifierIndex
              { stepWidth: 2, domainLog2: treeStepDomainLog2 }
        , crs: pallasWrapSrs
        }
    treeWrapCR <- liftEffect $
      wrapCompile @1 @(Slots2 0 2) treeWrapCtx

    -- Emit Tree wrap CS + VK traces.
    let treeWrapCSDomainLog2 = ProofFFI.vestaProverIndexDomainLog2 treeWrapCR.proverIndex
    let treeWrapVkComms = extractWrapVKForStepHash treeWrapCR.verifierIndex
    liftEffect do
      Trace.int "compile.wrapCS.domain_log2" treeWrapCSDomainLog2
      Trace.int "compile.wrapCS.public_input_size" (Array.length treeWrapCR.builtState.publicInputs)
      for_ (Array.mapWithIndex Tuple (Vector.toUnfoldable treeWrapVkComms.sigmaComm)) \(Tuple i pt) -> do
        Trace.field ("compile.wrapVK.sigma." <> show i <> ".x") pt.x
        Trace.field ("compile.wrapVK.sigma." <> show i <> ".y") pt.y
      for_ (Array.mapWithIndex Tuple (Vector.toUnfoldable treeWrapVkComms.coefficientsComm)) \(Tuple i pt) -> do
        Trace.field ("compile.wrapVK.coeff." <> show i <> ".x") pt.x
        Trace.field ("compile.wrapVK.coeff." <> show i <> ".y") pt.y
      Trace.field "compile.wrapVK.generic.x" treeWrapVkComms.genericComm.x
      Trace.field "compile.wrapVK.generic.y" treeWrapVkComms.genericComm.y
      Trace.field "compile.wrapVK.psm.x" treeWrapVkComms.psmComm.x
      Trace.field "compile.wrapVK.psm.y" treeWrapVkComms.psmComm.y
      Trace.field "compile.wrapVK.complete_add.x" treeWrapVkComms.completeAddComm.x
      Trace.field "compile.wrapVK.complete_add.y" treeWrapVkComms.completeAddComm.y
      Trace.field "compile.wrapVK.mul.x" treeWrapVkComms.mulComm.x
      Trace.field "compile.wrapVK.mul.y" treeWrapVkComms.mulComm.y
      Trace.field "compile.wrapVK.emul.x" treeWrapVkComms.emulComm.x
      Trace.field "compile.wrapVK.emul.y" treeWrapVkComms.emulComm.y
      Trace.field "compile.wrapVK.endomul_scalar.x" treeWrapVkComms.endomulScalarComm.x
      Trace.field "compile.wrapVK.endomul_scalar.y" treeWrapVkComms.endomulScalarComm.y

    -- ===== Phase B: Tree step prove with REAL NRR at slot 0 =====
    -- Use the refactored `buildStepAdviceWithOracles` (2026-04-NN
    -- split own/prev inputVal into separate type params) with
    -- @inputVal=Unit and @prevInputVal=F StepField.
    --
    -- The helper replicates one slot template to ALL slots. With
    -- PrevsSpecCons 0 (PrevsSpecCons 2 PrevsSpecNil), slot 0 (n=0)
    -- specializes prevChallenges/prevSgs to `Vector.nil`, slot 1
    -- (n=2) to two copies of the NRR-derived value. Slot-1 sppw
    -- fields end up with NRR's values rather than a dummy N2 — not
    -- production-faithful, but slot-1 must_verify=false so the step
    -- finalize check passes. We'll revisit if a later assertion
    -- catches the slot-1 fakery.
    let
      nrrDv = nrr.wrapDv

      stepEndoScalar :: StepField
      stepEndoScalar =
        let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

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

    let
      oracleInput
        :: { publicInput :: Unit
           , prevPublicInput :: F StepField
           , wrapDomainLog2 :: Int
           , stepDomainLog2 :: Int
           , wrapVK :: _
           , stepOpeningSg :: _
           , kimchiPrevSg :: _
           , wrapProof :: _
           , wrapPublicInput :: _
           , prevChalPolys :: _
           , wrapPlonkRaw :: _
           , wrapPrevEvals :: _
           , wrapBranchData :: _
           , wrapSpongeDigest :: _
           , mustVerify :: _
           , wrapOwnPaddedBpChals :: _
           , fopState :: _
           , stepAdvicePrevEvals :: _
           , kimchiPrevChallengesExpanded :: _
           , prevChallengesForStepHash :: _
           }
      oracleInput =
        { publicInput: unit
        , prevPublicInput: F zero -- NRR's output
        , wrapDomainLog2: nrr.wrapDomainLog2
        -- Step domain of the NRR proof being verified. NRR's step domain
        -- log2 = 9 (from its prover index), distinct from wrap VK domain 13.
        -- OCaml `expand_deferred` uses `Branch_data.domain branch_data` for
        -- `step_domain`; branch_data.domain_log2 of NRR's wrap statement
        -- equals NRR step log2 = 9.
        , stepDomainLog2: nrrStepDomainLog2
        , wrapVK: nrr.wrapCR.verifierIndex
        -- Split of previously-conflated `stepSg`:
        --   stepOpeningSg = real NRR step proof's opening sg. Fed into
        --     msgForNextWrap hash + expandProof's wrapChallengePoly
        --     commitment. OCaml wrap.ml:541-556 stores this into NRR's
        --     wrap statement, so advice.messagesForNextWrapProof needs
        --     to see the REAL value to match what step_main recomputes.
        --   kimchiPrevSg = Dummy.Ipa.Step.sg, the compile-time constant.
        --     Fed into the advice's kimchiPrevChallenges[_].sg entries
        --     (what the step prover's pallasCreateProofWithPrev sees as
        --     the prev IPA fold reference). Base case = dummy.
        , stepOpeningSg: ProofFFI.pallasProofOpeningSg nrr.stepResult.proof
        -- Iter 2ad: per OCaml step.ml:907-909, kimchi step prev_challenges[i].sg =
        -- prev_wrap_proof[i].statement.proof_state.messages_for_next_wrap_proof
        -- .challenge_polynomial_commitment. NRR wrap stored stepOpeningSg
        -- at that field (per wrap.ml:541-556), so the kimchi prev_challenges
        -- for slot 0 uses the same value.
        , kimchiPrevSg: ProofFFI.pallasProofOpeningSg nrr.stepResult.proof
        , wrapProof: nrr.wrapResult.proof
        , wrapPublicInput: nrr.wrapPublicInput
        , prevChalPolys:
            -- NRR is N=0: both padded slots are dummy.
            let
              dummyEntry =
                { sg: nrrWrapSg
                , challenges: Dummy.dummyIpaChallenges.wrapExpanded
                }
            in
              dummyEntry :< dummyEntry :< Vector.nil
        , wrapPlonkRaw: wrapPlonkRawFromDv
        , wrapPrevEvals: nrrWrapPrevEvals
        , wrapBranchData: nrrDv.branchData
        , wrapSpongeDigest: nrrDv.spongeDigestBeforeEvaluations
        , mustVerify: true -- slot 0 always verifies
        , wrapOwnPaddedBpChals:
            -- NRR wrap has no real prev-bp-chal input (N=0); both
            -- slots dummy. TODO(iter 2f): extract real own-bp-chals
            -- from NRR wrap proof via vestaProofOpeningPrechallenges
            -- once we hit the inevitable mismatch here.
            Dummy.dummyIpaChallenges.wrapExpanded
              :< Dummy.dummyIpaChallenges.wrapExpanded
              :< Vector.nil
        -- Slot 0 is a REAL NRR wrap proof: fopState MUST come from
        -- nrr.wrapDv (what NRR wrap statement's deferred_values
        -- store), not `stepDummyFopProofState`. The DivisionByZero at
        -- `step2_fop [finalize-other-proof]` on iter 2e came from
        -- using the dummy fopState — its zero plonk/cip/bp_chals
        -- broke the finalize math.
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
        -- kimchiPrevChallengesExpanded: expand nrr.wrapDv.bulletproofPrechallenges
        -- via Vesta.ScalarField endo (step endo_scalar). Same pattern
        -- as SimpleChain b1 at Prove/SimpleChain.purs:1039.
        , kimchiPrevChallengesExpanded:
            map
              (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
              nrrDv.bulletproofPrechallenges
        , prevChallengesForStepHash: Vector.replicate Dummy.dummyIpaChallenges.stepExpanded
        }

    -- Single-slot advice builds: slot 0 from buildStepAdviceWithOracles
    -- (real NRR data), slot 1 from buildStepAdvice (dummy N=2).
    -- We splice their carriers into Tree's heterogeneous
    -- `PrevsSpecCons 0 (PrevsSpecCons 2 PrevsSpecNil)` shape.
    { advice: slot0Advice, challengePolynomialCommitment: b0Slot0ChalPolyComm } <- liftEffect $
      buildStepAdviceWithOracles @0 @(PrevsSpecCons 0 PrevsSpecNil) oracleInput

    -- Iter 2s: slot 1 dummy now built via `buildStepAdviceWithOracles`
    -- over `Pickles.Proof.Dummy.dummyWrapProof`. OCaml's `expand_proof`
    -- (step.ml:406-418,637-645) returns Unfinalized with plonk.{α,β,γ,ζ}
    -- = oracle outputs (NOT stored Ro-derived values). The previous
    -- `buildStepAdvice`-based dummy stored Ro-derived plonk into the
    -- advice, which diverged from the in-circuit sponge squeeze (which
    -- reproduces oracle-style values) → ivp_assert_plonk_beta failure.
    -- Template: `Test.Pickles.Prove.SimpleChain` base case (lines 355-414).
    let
      slot1BaseCaseDummyChalPoly =
        { sg: nrrWrapSg, challenges: Dummy.dummyIpaChallenges.wrapExpanded }
      slot1BaseCaseWrapPI = dummyWrapTockPublicInput @2
        -- branchData.domainLog2 for OCaml Proof.dummy N2 N2 ~domain_log2:15.
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
    { advice: slot1Advice, challengePolynomialCommitment: b0Slot1ChalPolyComm } <- liftEffect $
      buildStepAdviceWithOracles @2 @(PrevsSpecCons 2 PrevsSpecNil)
        { publicInput: unit
        , prevPublicInput: (F (negate one)) :: F StepField
        -- Iter 2ah: for slot 1 wrap-side derive_plonk, domain = Tree
        -- wrap VK's domain (log2=14 via override_wrap_domain=N1), NOT
        -- Tree's step domain (log2=15). Per OCaml step.ml:533-538
        -- tock_domain uses `dlog_vk.domain.log_size_of_group`.
        , wrapDomainLog2: treeWrapDomainLog2
        -- Step domain of the dummy self-proof being verified. OCaml
        -- `Proof.dummy N2 N2 ~domain_log2:15` stores 15 in
        -- `branch_data.domain_log2`; `expand_deferred` uses that as
        -- `step_domain`, which controls zetaToDomainSize, perm, omega.
        -- Distinct from Tree wrap VK domain (14).
        , stepDomainLog2: treeSelfStepDomainLog2
        , wrapVK: treeWrapCR.verifierIndex
        , stepOpeningSg: nrr.stepSg
        , kimchiPrevSg: nrr.stepSg
        -- Slot 1 (Tree self dummy): Proof.dummy is called at runtime AFTER
        -- Tree compile, so its Ro counter is past module-init. Everything
        -- flows from `bcd.proofDummy` — the compile's
        -- N=2 force order gives Proof.dummy's z1/z2 at fq 92/93 (OCaml RTL)
        -- and plonk.{alpha,beta,gamma,zeta} at chals 36-39.
        , wrapProof: dummyWrapProof bcd
        , wrapPublicInput: slot1BaseCaseWrapPI
        , prevChalPolys:
            slot1BaseCaseDummyChalPoly
              :< slot1BaseCaseDummyChalPoly
              :< Vector.nil
              :: Vector PaddedLength _
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

    liftEffect $ for_ (Array.mapWithIndex Tuple treeStepResult.publicInputs) \(Tuple i x) ->
      Trace.field ("step.proof.public_input." <> show i) x

    -- iter 2ab diag: kimchi-native x_hat for Tree's step proof.
    -- Compare to circuit's `ivp.trace.wrap.xhat.{x,y}` to verify
    -- public_comm computation matches.
    liftEffect do
      let kimchiXhats = ProofFFI.pallasPublicComm treeStepCR.verifierIndex treeStepResult.publicInputs
      case Array.head kimchiXhats of
        Just pt -> do
          Trace.field "diag.kimchi.xhat.x" pt.x
          Trace.field "diag.kimchi.xhat.y" pt.y
        Nothing -> pure unit
    -- iter 2x diag: kimchi-native step VK digest (what the oracle absorbs
    -- as index_digest). Compare to ivp.trace.wrap.index_digest (circuit).
    liftEffect $ Trace.field "diag.kimchi.step_vk_digest"
      (ProofFFI.pallasVerifierIndexDigest treeStepCR.verifierIndex)
    -- Kimchi's post-absorb sponge state (before beta squeeze) — gives us
    -- ground truth for what the circuit's sponge state should be.
    liftEffect do
      let
        kimchiCheckpoint = ProofFFI.pallasSpongeCheckpointBeforeChallenges
          treeStepCR.verifierIndex
          { proof: treeStepResult.proof, publicInput: treeStepResult.publicInputs }
      Trace.field "diag.kimchi.sponge_post.s0"
        (Vector.index kimchiCheckpoint.state (unsafeFinite @3 0))
      Trace.field "diag.kimchi.sponge_post.s1"
        (Vector.index kimchiCheckpoint.state (unsafeFinite @3 1))
      Trace.field "diag.kimchi.sponge_post.s2"
        (Vector.index kimchiCheckpoint.state (unsafeFinite @3 2))
      Trace.string "diag.kimchi.sponge_post.mode" kimchiCheckpoint.spongeMode
      Trace.int "diag.kimchi.sponge_post.mode_count" kimchiCheckpoint.modeCount

    -- ===== Phase C: Tree wrap prove (iter 2t) =====
    -- Analogous to SimpleChain's base-case wrap prove (SimpleChain.purs:480-866)
    -- but for `mpv=2` / `Slots2 0 2` — slot 0 is a real NRR wrap proof,
    -- slot 1 is a dummy N2.
    let
      -- Slot-0 kimchi prev_challenges: NRR's REAL wrap bp_chals expanded
      -- via Vesta.ScalarField endo (step endo_scalar). Mirrors what
      -- buildStepAdviceWithOracles wrote into slot 0's kimchiPrevChallenges
      -- via `input.kimchiPrevChallengesExpanded = toFieldPure <$>
      -- nrrDv.bulletproofPrechallenges`.
      nrrBpChalsExpandedForSlot0 :: Vector StepIPARounds StepField
      nrrBpChalsExpandedForSlot0 =
        map
          (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
          nrr.wrapDv.bulletproofPrechallenges

      nrrStepOpeningSgOracle = ProofFFI.pallasProofOpeningSg nrr.stepResult.proof
      stepOraclesTree = ProofFFI.pallasProofOracles treeStepCR.verifierIndex
        { proof: treeStepResult.proof
        , publicInput: treeStepResult.publicInputs
        -- Iter 2ad: must match what the step prover fed to
        -- pallasCreateProofWithPrev via advice.kimchiPrevChallenges
        -- (per-slot sg = prev_wrap_proof[i].messages_for_next_wrap_proof.cpc).
        -- Slot 0: NRR step opening sg. Slot 1: nrr.stepSg (dummy).
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
        -- Iter 2ad: match step prover's kimchiPrevChallenges sgs —
        -- slot 0 = NRR step opening sg, slot 1 = nrr.stepSg.
        , prevSgs: nrrStepOpeningSgOracle :< nrr.stepSg :< Vector.nil
        -- slot 0 (NRR verified): NRR's real bp_chals expanded;
        -- slot 1 (dummy N2): dummy step-IPA challenges.
        , prevChallenges:
            nrrBpChalsExpandedForSlot0
              :< Dummy.dummyIpaChallenges.stepExpanded
              :< Vector.nil
        -- Tree proofs_verified = 2 → N2 mask = [T, T].
        , proofsVerifiedMask: true :< true :< Vector.nil
        }

      treeWrapDv = wrapComputeDeferredValues treeWrapDvInput

      -- msg_for_next_step_proof digest: read from the step proof's PI.
      -- Tree outputSize=67 layout: 2*32 unfinalizeds (indices 0-63) +
      -- 1 outer hash (index 64) + 2 widths (indices 65-66). Index 64
      -- holds the outer `hash_messages_for_next_step_proof` digest.
      msgForNextStepDigestTree :: StepField
      msgForNextStepDigestTree =
        fromJust'
          "Tree wrap prove: step PI[64] outer hash must exist" $
          Array.index treeStepResult.publicInputs 64

      treeWrapProofSg :: AffinePoint WrapField
      treeWrapProofSg = ProofFFI.pallasProofOpeningSg treeStepResult.proof

      treeWrapEndoScalar :: WrapField
      treeWrapEndoScalar =
        let EndoScalar e = (endoScalar :: EndoScalar WrapField) in e

      -- For slot-0 (real NRR prev), extract raw bp chals from the step
      -- advice's publicUnfinalizedProofs[0] and expand via wrap endo.
      PerProofUnfinalized slot0UnfRec =
        Vector.head (unwrap treeRealAdvice).publicUnfinalizedProofs

      PerProofUnfinalized slot1UnfRec =
        Vector.head (Vector.drop @1 (unwrap treeRealAdvice).publicUnfinalizedProofs)

      slot0RealBpChalsWrap :: Vector WrapIPARounds WrapField
      slot0RealBpChalsWrap =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF 128 WrapField)
                treeWrapEndoScalar
          )
          slot0UnfRec.bulletproofChallenges

      -- slot 1's bp chals: from advice.publicUnfinalizedProofs[1]
      -- (= dummy N2 wrap's stored bp_chals, which are
      -- dummyIpaChallenges.wrapExpanded per Proof.dummy N2 N2).
      slot1RealBpChalsWrap :: Vector WrapIPARounds WrapField
      slot1RealBpChalsWrap =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF 128 WrapField)
                treeWrapEndoScalar
          )
          slot1UnfRec.bulletproofChallenges

      -- Iter 2ae: OCaml wrap_main.ml:117-125 hashes per-slot
      -- NEW bp chals (from FOP), no padding dummy — for mpv=2
      -- Tree both slots are real (slot 0 = NRR real, slot 1 =
      -- dummy N2 real). Previously had [dummy, slot0] which was
      -- wrong padding order for mpv=2.
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

      -- Convert each slot's advice unfinalized (Type2 SplitField F StepField)
      -- into wrap-field form (Type2 F WrapField). Same pattern as
      -- SimpleChain.purs:662-681.
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

      -- Iter 2ad: prev_step_accs[i] = prev_wrap_proof[i]'s
      -- messages_for_next_wrap_proof.challenge_polynomial_commitment
      -- (per OCaml wrap.ml:371 Step_accs responder). Must equal the
      -- step prover's kimchi prev_challenges[i].sg (both derived from
      -- the same source).
      -- slot 0: NRR wrap stored NRR step proof's opening sg.
      -- slot 1: Proof.dummy N2 N2 stored Dummy.Ipa.Step.sg = nrr.stepSg.
      nrrStepOpeningSg = ProofFFI.pallasProofOpeningSg nrr.stepResult.proof

      slot0StepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
      slot0StepAcc = WeierstrassAffinePoint
        { x: F nrrStepOpeningSg.x, y: F nrrStepOpeningSg.y }

      slot1StepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
      slot1StepAcc = WeierstrassAffinePoint
        { x: F nrr.stepSg.x, y: F nrr.stepSg.y }

      -- Slot 1 (width 2) gets two copies of dummyWrapBpChals.
      dummyWrapBpChalsW :: Vector WrapIPARounds (F WrapField)
      dummyWrapBpChalsW = map F Dummy.dummyIpaChallenges.wrapExpanded

      -- Slot 0: real NRR wrap proof's evals (wrap-field, for the wrap
      -- IVP's prevEvals). xhat comes from oracles over NRR's wrap proof.
      slot0PrevEvalsW :: StepAllEvals (F WrapField)
      slot0PrevEvalsW =
        let
          o = ProofFFI.vestaProofOracles nrr.wrapCR.verifierIndex
            { proof: nrr.wrapResult.proof
            , publicInput: nrr.wrapPublicInput
            , prevChallenges: [] -- NRR wrap mpv=0
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

      -- Slot 1: dummy N2 wrap proof's evals. Dummy evals for non-xhat
      -- fields, plus oracle-derived xhat from vestaProofOracles on
      -- dummyWrapProof + Tree's wrap VK.
      slot1PrevEvalsW :: StepAllEvals (F WrapField)
      slot1PrevEvalsW =
        let
          toFFI r = { sgX: r.sg.x, sgY: r.sg.y, challenges: Vector.toUnfoldable r.challenges }
          dummyChalPoly =
            { sg: nrrWrapSg, challenges: Dummy.dummyIpaChallenges.wrapExpanded }
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
        -- Slots2 0 2: slot 0 width 0 (empty), slot 1 width 2 (two dummy chals).
        , prevOldBpChals: slots2 Vector.nil (dummyWrapBpChalsW :< dummyWrapBpChalsW :< Vector.nil)
        , prevEvals: slot0PrevEvalsW :< slot1PrevEvalsW :< Vector.nil
        -- Indices into `allPossibleDomainLog2s = [13, 14, 15]`:
        -- slot 0 verifies NRR wrap (mpv=0 → wrap_domain 2^13 → index 0).
        -- slot 1 verifies Tree self wrap (override_wrap_domain=N1 → 2^14 → index 1).
        , prevWrapDomainIndices:
            F (fromInt 0 :: WrapField) :< F (fromInt 1 :: WrapField) :< Vector.nil
        }

      treeWrapAdvice :: WrapAdvice 2 (Slots2 0 2)
      treeWrapAdvice = buildWrapAdvice treeWrapAdviceInput

      treeWrapProveCtx =
        { wrapMainConfig: treeWrapCtx.wrapMainConfig
        , crs: pallasWrapSrs
        , publicInput: treeWrapPublicInput
        , advice: treeWrapAdvice
        , debug: true
        , kimchiPrevChallenges:
            -- Per OCaml wrap.ml:496-507: wrap's kimchi prev_challenges
            -- are per-slot (step_b0's stored sg + step_b0's new bp_chals
            -- wrap-expanded). For Tree N=2 b0: slot 0 = NRR real
            -- prev (step_b0's IVP over NRR wrap → slot0RealBpChalsWrap
            -- already computed); slot 1 = dummy wrap verify (step_b0's
            -- IVP over dummy → slot1RealBpChalsWrap). The sg points are
            -- step_b0.msg_for_next_step_proof.cpc[i] = b0Slot{0,1}
            -- ChalPolyComm (already captured).
            --
            -- Previously used `[dummy, dummy]` which matched at witness
            -- level (kimchi's witness dump is deterministic wrt CS+PI
            -- and independent of prev_challenges in the sponge phase)
            -- but diverged in the OPENING phase (opening.sg depends on
            -- IPA's sponge state which absorbs prev_challenges).
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

    -- Iter 2z: kimchi-native sponge state right BEFORE beta squeeze.
    -- Compare to wrap circuit's OptSponge state at the equivalent
    -- point (after absorbing index_digest + sg_old + x_hat + w_comm).
    liftEffect do
      let
        kimchiBetaState = ProofFFI.pallasSpongeStateBeforeBeta
          treeStepCR.verifierIndex
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
      Trace.field "diag.kimchi.before_beta.s0"
        (Vector.index kimchiBetaState.state (unsafeFinite @3 0))
      Trace.field "diag.kimchi.before_beta.s1"
        (Vector.index kimchiBetaState.state (unsafeFinite @3 1))
      Trace.field "diag.kimchi.before_beta.s2"
        (Vector.index kimchiBetaState.state (unsafeFinite @3 2))
      Trace.string "diag.kimchi.before_beta.mode" kimchiBetaState.spongeMode
      Trace.int "diag.kimchi.before_beta.mode_count" kimchiBetaState.modeCount

    treeWrapRes <- liftEffect $ runExceptT $
      wrapSolveAndProve @1 @(Slots2 0 2) treeWrapProveCtx treeWrapCR
    treeWrapResult <- case treeWrapRes of
      Left e -> liftEffect $ Exc.throw ("tree wrapSolveAndProve b0: " <> show e)
      Right r -> pure r

    liftEffect $ for_ (Array.mapWithIndex Tuple treeWrapResult.publicInputs) \(Tuple i x) ->
      Trace.field ("wrap.proof.public_input." <> show i) x

    -- DIAG: emit Tree b0 wrap proof's opening values for comparison
    -- against ipa.dbg.* during b1 slot 1's IPA check. Iter 2bd confirmed
    -- sg matches byte-identical. Now check delta, z1, z2.
    let treeB0WrapOpeningSg = ProofFFI.vestaProofOpeningSg treeWrapResult.proof
    let treeB0WrapOpeningDelta = ProofFFI.vestaProofOpeningDelta treeWrapResult.proof
    let treeB0WrapOpeningZ1 = ProofFFI.vestaProofOpeningZ1 treeWrapResult.proof
    let treeB0WrapOpeningZ2 = ProofFFI.vestaProofOpeningZ2 treeWrapResult.proof
    liftEffect do
      Trace.field "diag.b0wrap.opening.sg.x" treeB0WrapOpeningSg.x
      Trace.field "diag.b0wrap.opening.sg.y" treeB0WrapOpeningSg.y
      Trace.field "diag.b0wrap.opening.delta.x" treeB0WrapOpeningDelta.x
      Trace.field "diag.b0wrap.opening.delta.y" treeB0WrapOpeningDelta.y
      Trace.field "diag.b0wrap.opening.z1" treeB0WrapOpeningZ1
      Trace.field "diag.b0wrap.opening.z2" treeB0WrapOpeningZ2

    liftEffect $ Trace.string "tree_proof_return.end" "base_case_proved"

    -- =====================================================================
    -- INDUCTIVE CASE (b1): slot 0 = NRR (unchanged), slot 1 = REAL Tree b0
    -- wrap proof replacing the dummy N2. Expected public_output = 1
    -- (= 1 + prev with prev=0). Mirrors SimpleChain b1 (lines 907-1333)
    -- adapted for Tree's heterogeneous [N0, N2] slots.
    -- =====================================================================
    liftEffect $ Trace.string "tree_proof_return.begin" "inductive_case"

    let
      b1RuleArgs =
        { isBaseCase: false
        , nrrInputVal: F zero -- NRR's output is always 0
        , prevInputVal: F zero -- b0's output was 0
        }

      -- b0's Tree step proof opening sg: what b1 slot-1's oracleInput
      -- feeds as stepOpeningSg (i.e. the sg field stored in wrap_b0's
      -- messages_for_next_wrap_proof, per wrap.ml:541-556).
      b0StepOpeningSg :: AffinePoint WrapField
      b0StepOpeningSg = ProofFFI.pallasProofOpeningSg treeStepResult.proof

      -- b0's Tree step proof's unfinalized bp chals (slot 0 and slot 1),
      -- expanded via the wrap endo. These are what Tree b0 wrap hashed
      -- into its msg_for_next_wrap_proof digest (see line 744-750).
      b0MsgForNextWrapChalsSlot0Wrap :: Vector WrapIPARounds WrapField
      b0MsgForNextWrapChalsSlot0Wrap = slot0RealBpChalsWrap

      b0MsgForNextWrapChalsSlot1Wrap :: Vector WrapIPARounds WrapField
      b0MsgForNextWrapChalsSlot1Wrap = slot1RealBpChalsWrap

      -- b1 slot-1 wrap-prev-evals: oracles over Tree b0 STEP proof's
      -- polynomial evaluations + oracle outputs. Per step.ml:1023-1036
      -- applied to step_b1 verifying wrap_b0: prev_evals = step_b0's
      -- eval vectors + x_hat from oracles. PS has `stepOraclesTree`
      -- (from line 621) + treeStepResult.proof already computed.
      b1Slot1WrapPrevEvals :: AllEvals StepField
      b1Slot1WrapPrevEvals =
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

      -- b1 slot-1 prevChalPolys (Padded_length=2 for Tree's width-2
      -- slot, n=2=PaddedLength so NO front-padding required).
      --
      -- Per OCaml step.ml:513-517, these are extend_front of wrap_b0
      -- .statement.msg_for_next_step_proof.challenge_polynomial_commitments
      -- to Local_max_proofs_verified.n=2 with Dummy.Ipa.Wrap.sg. Since
      -- wrap_b0.stmt.msg_for_next_step.cpc already has length 2 (Tree's
      -- own max_proofs_verified), extend_front is identity.
      --
      -- Each entry's sg is what step_b0's own per-slot circuit computed
      -- for `challenge_polynomial_commitment` (step.ml:502-504):
      --   slot 0 (NRR, must_verify=true): real NRR wrap opening sg,
      --     captured here as b0Slot0ChalPolyComm (= expandProofResult.sg
      --     from b0's slot-0 buildStepAdviceWithOracles call).
      --   slot 1 (dummy N2, must_verify=false): Ipa.Wrap.compute_sg
      --     (new_bp_chals), captured as b0Slot1ChalPolyComm.
      --
      -- Each entry's challenges = expanded new bp chals of the
      -- corresponding slot from b0 (= slot0RealBpChalsWrap,
      -- slot1RealBpChalsWrap lifted from wrap endo).
      b1Slot1PrevChalPolys =
        { sg: b0Slot0ChalPolyComm, challenges: slot0RealBpChalsWrap }
          :< { sg: b0Slot1ChalPolyComm, challenges: slot1RealBpChalsWrap }
          :< Vector.nil

    -- b1 slot-0 advice: NRR is unchanged from b0, so the oracleInput
    -- is identical (same NRR wrap proof, same prevPublicInput, etc).
    -- Just call buildStepAdviceWithOracles again with the SAME input.
    { advice: b1Slot0Advice, challengePolynomialCommitment: b1Slot0ChalPolyComm } <- liftEffect $
      buildStepAdviceWithOracles @0 @(PrevsSpecCons 0 PrevsSpecNil) oracleInput

    -- b1 slot-1 advice: NEW — verifying REAL Tree b0 wrap proof.
    { advice: b1Slot1Advice, challengePolynomialCommitment: b1Slot1ChalPolyComm } <- liftEffect $
      buildStepAdviceWithOracles @2 @(PrevsSpecCons 2 PrevsSpecNil)
        { publicInput: unit
        , prevPublicInput: (F zero) :: F StepField -- b0 output was 0
        , wrapDomainLog2: treeWrapDomainLog2
        , stepDomainLog2: treeSelfStepDomainLog2
        , wrapVK: treeWrapCR.verifierIndex
        , stepOpeningSg: b0StepOpeningSg
        , kimchiPrevSg: b0StepOpeningSg
        , wrapProof: treeWrapResult.proof
        , wrapPublicInput: treeWrapResult.publicInputs
        , prevChalPolys: b1Slot1PrevChalPolys
        , wrapPlonkRaw:
            { alpha: SizedF.unwrapF treeWrapDv.plonk.alpha
            , beta: SizedF.unwrapF treeWrapDv.plonk.beta
            , gamma: SizedF.unwrapF treeWrapDv.plonk.gamma
            , zeta: SizedF.unwrapF treeWrapDv.plonk.zeta
            }
        , wrapPrevEvals: b1Slot1WrapPrevEvals
        , wrapBranchData: treeWrapDv.branchData
        , wrapSpongeDigest: treeWrapDv.spongeDigestBeforeEvaluations
        , mustVerify: true
        -- wrapOwnPaddedBpChals: per wrap.ml:46-59 +:463-465 this is
        -- what wrap_b0 hashed into its msg_for_next_wrap_proof digest.
        -- Tree b0 hashed [slot0RealBpChalsWrap, slot1RealBpChalsWrap]
        -- (line 746-749). Same values here.
        , wrapOwnPaddedBpChals:
            b0MsgForNextWrapChalsSlot0Wrap
              :< b0MsgForNextWrapChalsSlot1Wrap
              :< Vector.nil
        , fopState:
            { deferredValues:
                { plonk: treeWrapDv.plonk
                , combinedInnerProduct: treeWrapDv.combinedInnerProduct
                , xi: treeWrapDv.xi
                , bulletproofChallenges: treeWrapDv.bulletproofPrechallenges
                , b: treeWrapDv.b
                }
            , shouldFinalize: false
            , spongeDigestBeforeEvaluations: F treeWrapDv.spongeDigestBeforeEvaluations
            }
        , stepAdvicePrevEvals: b1Slot1WrapPrevEvals
        -- kimchi prev_challenges for b1 slot 1: expand wrap_b0's
        -- own bp_chals via step endo (per step.ml:913-920 +
        -- reduced_messages_for_next_proof_over_same_field.ml:41).
        , kimchiPrevChallengesExpanded:
            map
              (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
              treeWrapDv.bulletproofPrechallenges
        -- prevChallengesForStepHash: wrap_b0.stmt.msg_for_next_step
        -- .old_bulletproof_challenges expanded via step_endo. This is
        -- what step_b0 stored as its own msg.old_bp_chals (forwarded
        -- by wrap_b0 into its statement). For Tree b0:
        --   slot 0 (NRR verify): step_b0 stored the step-expansion of
        --     NRR wrap's deferred.bp_chals (= nrr.wrapDv
        --     .bulletproofPrechallenges raw → step_expand).
        --   slot 1 (dummy verify): step_b0 stored the step-expansion
        --     of the dummy wrap's deferred.bp_chals (= Dummy.Ipa.Step
        --     .challenges_computed, which is dummyIpaChallenges
        --     .stepExpanded already step-expanded).
        -- These HETEROGENEOUS per-slot values match the byte-identical
        -- step_main_outer.proof.i.bp_chal.j trace (slot 0: 24243814...,
        -- slot 1: 7495663189...). Dimension: Vector PaddedLength=2 of
        -- Vector StepIPARounds=16 StepField.
        , prevChallengesForStepHash:
            map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
              nrr.wrapDv.bulletproofPrechallenges
              :< Dummy.dummyIpaChallenges.stepExpanded
              :< Vector.nil
        }

    -- Splice b1 slot-0 + slot-1 advices into the heterogeneous carrier.
    let
      StepAdvice b1s0 = b1Slot0Advice
      StepAdvice b1s1 = b1Slot1Advice
      Tuple b1Slot0Sppw _ = b1s0.perProofSlotsCarrier
      Tuple b1Slot1Sppw _ = b1s1.perProofSlotsCarrier

      treeB1Advice :: StepAdvice TreeProofReturnPrevsSpec StepIPARounds WrapIPARounds Unit 2 _
      treeB1Advice = StepAdvice
        { perProofSlotsCarrier: Tuple b1Slot0Sppw (Tuple b1Slot1Sppw unit)
        , publicInput: unit
        , publicUnfinalizedProofs:
            Vector.head b1s0.publicUnfinalizedProofs
              :< Vector.head b1s1.publicUnfinalizedProofs
              :< Vector.nil
        , messagesForNextWrapProof:
            Vector.head b1s0.messagesForNextWrapProof
              :< Vector.head b1s1.messagesForNextWrapProof
              :< Vector.nil
        , wrapVerifierIndex: extractWrapVKCommsAdvice treeWrapCR.verifierIndex
        , kimchiPrevChallenges:
            Vector.head b1s0.kimchiPrevChallenges
              :< Vector.head b1s1.kimchiPrevChallenges
              :< Vector.nil
        }

    b1StepRes <- liftEffect $ runExceptT $
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
        (treeProofReturnRule b1RuleArgs)
        treeStepCR
        treeB1Advice
    b1StepResult <- case b1StepRes of
      Left e -> liftEffect $ Exc.throw ("b1 stepSolveAndProve: " <> show e)
      Right r -> pure r

    liftEffect $ for_ (Array.mapWithIndex Tuple b1StepResult.publicInputs) \(Tuple i x) ->
      Trace.field ("b1.step.proof.public_input." <> show i) x

    -- =====================================================================
    -- b1 WRAP: wrap step_b1 (the inductive-case step proof above). Mirror
    -- of the b0 wrap block with b0 → b1 substitutions. Per-slot kimchi
    -- prev_challenges use step_b1's slot{0,1}ChalPolyComm + wrap-expanded
    -- b1StepResult's per-slot new bp_chals — same pattern as the iter 2bf
    -- breakthrough fix for b0 wrap.
    -- =====================================================================
    let
      -- Oracles over step_b1 proof (for x_hat via publicEvals + ftEval1).
      -- step_b1 verified 2 prev wrap proofs: slot 0 = real NRR wrap,
      -- slot 1 = real Tree b0 wrap. kimchi prev_challenges for step_b1
      -- came from the splice in treeB1Advice.kimchiPrevChallenges (via
      -- each slot's buildStepAdviceWithOracles setting
      -- `kimchiPrevSg = stepOpeningSg of the prev step proof`).
      b0TreeStepOpeningSgOracle = ProofFFI.pallasProofOpeningSg treeStepResult.proof

      b1StepKimchiPrevChalsSlot0 :: Vector StepIPARounds StepField
      b1StepKimchiPrevChalsSlot0 = nrrBpChalsExpandedForSlot0

      b1StepKimchiPrevChalsSlot1 :: Vector StepIPARounds StepField
      b1StepKimchiPrevChalsSlot1 =
        map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
          treeWrapDv.bulletproofPrechallenges

      b1StepOraclesTree = ProofFFI.pallasProofOracles treeStepCR.verifierIndex
        { proof: b1StepResult.proof
        , publicInput: b1StepResult.publicInputs
        , prevChallenges:
            [ { sgX: nrrStepOpeningSgOracle.x
              , sgY: nrrStepOpeningSgOracle.y
              , challenges: Vector.toUnfoldable b1StepKimchiPrevChalsSlot0
              }
            , { sgX: b0TreeStepOpeningSgOracle.x
              , sgY: b0TreeStepOpeningSgOracle.y
              , challenges: Vector.toUnfoldable b1StepKimchiPrevChalsSlot1
              }
            ]
        }

      b1StepAllEvals :: AllEvals StepField
      b1StepAllEvals =
        { ftEval1: b1StepOraclesTree.ftEval1
        , publicEvals:
            { zeta: b1StepOraclesTree.publicEvalZeta
            , omegaTimesZeta: b1StepOraclesTree.publicEvalZetaOmega
            }
        , zEvals: ProofFFI.proofZEvals b1StepResult.proof
        , witnessEvals: ProofFFI.proofWitnessEvals b1StepResult.proof
        , coeffEvals: ProofFFI.proofCoefficientEvals b1StepResult.proof
        , sigmaEvals: ProofFFI.proofSigmaEvals b1StepResult.proof
        , indexEvals: ProofFFI.proofIndexEvals b1StepResult.proof
        }

      b1TreeWrapDvInput :: WrapDeferredValuesInput 2
      b1TreeWrapDvInput =
        { proof: b1StepResult.proof
        , verifierIndex: treeStepCR.verifierIndex
        , publicInput: b1StepResult.publicInputs
        , allEvals: b1StepAllEvals
        , pEval0Chunks: [ b1StepOraclesTree.publicEvalZeta ]
        , domainLog2: treeStepDomainLog2
        , zkRows: 3
        , srsLengthLog2: 16
        , generator: (domainGenerator treeStepDomainLog2 :: StepField)
        , shifts: (domainShifts treeStepDomainLog2 :: Vector 7 StepField)
        , vanishesOnZk: ProofFFI.permutationVanishingPolynomial
            { domainLog2: treeStepDomainLog2, zkRows: 3, pt: b1StepOraclesTree.zeta }
        , omegaForLagrange: \_ -> one
        , endo: stepEndoScalar
        , linearizationPoly: Linearization.pallas
        , prevSgs: nrrStepOpeningSgOracle :< b0TreeStepOpeningSgOracle :< Vector.nil
        , prevChallenges:
            b1StepKimchiPrevChalsSlot0
              :< b1StepKimchiPrevChalsSlot1
              :< Vector.nil
        , proofsVerifiedMask: true :< true :< Vector.nil
        }

      b1TreeWrapDv = wrapComputeDeferredValues b1TreeWrapDvInput

      b1MsgForNextStepDigestTree :: StepField
      b1MsgForNextStepDigestTree =
        fromJust'
          "b1 wrap prove: step PI[64] outer hash must exist" $
          Array.index b1StepResult.publicInputs 64

      b1TreeWrapProofSg :: AffinePoint WrapField
      b1TreeWrapProofSg = ProofFFI.pallasProofOpeningSg b1StepResult.proof

      -- b1 step's slot0/1 new bp_chals wrap-expanded (for kimchi
      -- prev_challenges + msg_for_next_wrap hash).
      PerProofUnfinalized b1Slot0UnfRec =
        Vector.head (unwrap treeB1Advice).publicUnfinalizedProofs

      PerProofUnfinalized b1Slot1UnfRec =
        Vector.head (Vector.drop @1 (unwrap treeB1Advice).publicUnfinalizedProofs)

      b1Slot0RealBpChalsWrap :: Vector WrapIPARounds WrapField
      b1Slot0RealBpChalsWrap =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF 128 WrapField)
                treeWrapEndoScalar
          )
          b1Slot0UnfRec.bulletproofChallenges

      b1Slot1RealBpChalsWrap :: Vector WrapIPARounds WrapField
      b1Slot1RealBpChalsWrap =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF 128 WrapField)
                treeWrapEndoScalar
          )
          b1Slot1UnfRec.bulletproofChallenges

      b1MsgForNextWrapDigestTree :: WrapField
      b1MsgForNextWrapDigestTree = hashMessagesForNextWrapProofPureGeneral
        { sg: b1TreeWrapProofSg
        , paddedChallenges:
            b1Slot0RealBpChalsWrap
              :< b1Slot1RealBpChalsWrap
              :< Vector.nil
        }

      b1TreeWrapPublicInput = assembleWrapMainInput
        { deferredValues: b1TreeWrapDv
        , messagesForNextStepProofDigest: b1MsgForNextStepDigestTree
        , messagesForNextWrapProofDigest: b1MsgForNextWrapDigestTree
        }

      b1Slot0PerProof = convertSlotUnf b1Slot0UnfRec
      b1Slot1PerProof = convertSlotUnf b1Slot1UnfRec

      -- prev_step_accs: each slot's prev wrap proof's msg_for_next_wrap
      -- .challenge_polynomial_commitment. Slot 0 = NRR wrap stored NRR step
      -- opening sg. Slot 1 = Tree b0 wrap stored Tree b0 step opening sg.
      b1Slot0StepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
      b1Slot0StepAcc = WeierstrassAffinePoint
        { x: F nrrStepOpeningSg.x, y: F nrrStepOpeningSg.y }

      b1Slot1StepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
      b1Slot1StepAcc = WeierstrassAffinePoint
        { x: F b0TreeStepOpeningSgOracle.x, y: F b0TreeStepOpeningSgOracle.y }

      -- Per-slot old_bp_chals: what wrap_b0's msg_for_next_wrap stored
      -- for each of step_b0's 2 slots. These were step_b0's per-slot
      -- unfinalized.bp_chals wrap-expanded, = slot{0,1}RealBpChalsWrap
      -- (already computed for b0 wrap prove's msg hash).
      -- Structure mirrors `slots2 Vector.nil (... :< Vector.nil)` for
      -- Tree's [N=0, N=2] shape: slot 0 width 0 is empty, slot 1 width
      -- 2 carries Tree b0 wrap's forwarded step_b0 bp_chals.

      -- Slot 0 (NRR wrap): real NRR wrap evals + oracle xhat.
      b1Slot0PrevEvalsW :: StepAllEvals (F WrapField)
      b1Slot0PrevEvalsW = slot0PrevEvalsW -- reuse b0's NRR eval computation

      -- Slot 1 (Tree b0 wrap, real): oracles + evals over treeWrapResult.proof
      -- with b0's actual kimchi prev_challenges (iter 2bf fix).
      b1Slot1PrevEvalsW :: StepAllEvals (F WrapField)
      b1Slot1PrevEvalsW =
        let
          o = ProofFFI.vestaProofOracles treeWrapCR.verifierIndex
            { proof: treeWrapResult.proof
            , publicInput: treeWrapResult.publicInputs
            , prevChallenges:
                [ { sgX: b0Slot0ChalPolyComm.x
                  , sgY: b0Slot0ChalPolyComm.y
                  , challenges: Vector.toUnfoldable slot0RealBpChalsWrap
                  }
                , { sgX: b0Slot1ChalPolyComm.x
                  , sgY: b0Slot1ChalPolyComm.y
                  , challenges: Vector.toUnfoldable slot1RealBpChalsWrap
                  }
                ]
            }
          mkPE p = { zeta: F p.zeta, omegaTimesZeta: F p.omegaTimesZeta }
        in
          StepAllEvals
            { ftEval1: F o.ftEval1
            , publicEvals: PointEval
                { zeta: F o.publicEvalZeta
                , omegaTimesZeta: F o.publicEvalZetaOmega
                }
            , zEvals: PointEval (mkPE (ProofFFI.proofZEvals treeWrapResult.proof))
            , witnessEvals: map (PointEval <<< mkPE) (ProofFFI.proofWitnessEvals treeWrapResult.proof)
            , coeffEvals: map (PointEval <<< mkPE) (ProofFFI.proofCoefficientEvals treeWrapResult.proof)
            , sigmaEvals: map (PointEval <<< mkPE) (ProofFFI.proofSigmaEvals treeWrapResult.proof)
            , indexEvals: map (PointEval <<< mkPE) (ProofFFI.proofIndexEvals treeWrapResult.proof)
            }

      b1TreeWrapAdviceInput :: BuildWrapAdviceInput 2 (Slots2 0 2)
      b1TreeWrapAdviceInput =
        { stepProof: b1StepResult.proof
        , whichBranch: F zero
        , prevUnfinalizedProofs: b1Slot0PerProof :< b1Slot1PerProof :< Vector.nil
        , prevMessagesForNextStepProofHash:
            F (fromBigInt (toBigInt b1MsgForNextStepDigestTree) :: WrapField)
        , prevStepAccs: b1Slot0StepAcc :< b1Slot1StepAcc :< Vector.nil
        -- Slots2 0 2: slot 0 width 0 (empty), slot 1 width 2 carrying
        -- the two wrap-expanded bp_chals step_b0 stored (which
        -- wrap_b0 forwarded into its msg_for_next_wrap_proof).
        , prevOldBpChals: slots2 Vector.nil
            ( map F slot0RealBpChalsWrap
                :< map F slot1RealBpChalsWrap
                :< Vector.nil
            )
        , prevEvals: b1Slot0PrevEvalsW :< b1Slot1PrevEvalsW :< Vector.nil
        , prevWrapDomainIndices:
            F (fromInt 0 :: WrapField) :< F (fromInt 1 :: WrapField) :< Vector.nil
        }

      b1TreeWrapAdvice :: WrapAdvice 2 (Slots2 0 2)
      b1TreeWrapAdvice = buildWrapAdvice b1TreeWrapAdviceInput

      b1TreeWrapProveCtx =
        { wrapMainConfig: treeWrapCtx.wrapMainConfig
        , crs: pallasWrapSrs
        , publicInput: b1TreeWrapPublicInput
        , advice: b1TreeWrapAdvice
        , debug: true
        , kimchiPrevChallenges:
            -- Per OCaml wrap.ml:496-507, per-slot from step_b1's stored cpc
            -- + step_b1's per-slot new bp_chals wrap-expanded. For Tree b1
            -- step the cpcs are b1Slot{0,1}ChalPolyComm (captured from the
            -- slot's buildStepAdviceWithOracles call); the challenges are
            -- b1Slot{0,1}RealBpChalsWrap from treeB1Advice's unfinalized.
            { sgX: b1Slot0ChalPolyComm.x
            , sgY: b1Slot0ChalPolyComm.y
            , challenges: b1Slot0RealBpChalsWrap
            }
              :<
                { sgX: b1Slot1ChalPolyComm.x
                , sgY: b1Slot1ChalPolyComm.y
                , challenges: b1Slot1RealBpChalsWrap
                }
              :<
                Vector.nil
        }

    b1TreeWrapRes <- liftEffect $ runExceptT $
      wrapSolveAndProve @1 @(Slots2 0 2) b1TreeWrapProveCtx treeWrapCR
    b1TreeWrapResult <- case b1TreeWrapRes of
      Left e -> liftEffect $ Exc.throw ("b1 tree wrapSolveAndProve: " <> show e)
      Right r -> pure r

    liftEffect $ for_ (Array.mapWithIndex Tuple b1TreeWrapResult.publicInputs) \(Tuple i x) ->
      Trace.field ("b1.wrap.proof.public_input." <> show i) x

    liftEffect $ Trace.string "tree_proof_return.end" "inductive_case_proved"

    -- =====================================================================
    -- INDUCTIVE CASE (b2): slot 0 = NRR (unchanged), slot 1 = REAL Tree b1
    -- wrap proof replacing b0 wrap. Expected public_output = 2 (= 1 + prev
    -- with prev=1). Mirror of b1 with b0→b1 substitutions.
    --
    -- User guidance: "complete the step side first". This block only adds
    -- b2 step prove; b2 wrap is deferred to a separate block.
    -- =====================================================================
    liftEffect $ Trace.string "tree_proof_return.begin" "inductive_case_2"

    let
      b2RuleArgs =
        { isBaseCase: false
        , nrrInputVal: F zero -- NRR's output is always 0
        , prevInputVal: F one -- b1's output was 1
        }

      -- b1's Tree step proof opening sg: reuse b1TreeWrapProofSg from the
      -- b1 wrap block (= pallasProofOpeningSg b1StepResult.proof).
      b1StepOpeningSg :: AffinePoint WrapField
      b1StepOpeningSg = b1TreeWrapProofSg

      -- Reuse b1StepOraclesTree / b1StepAllEvals / b1TreeWrapDv from the
      -- b1 wrap block: same data (oracles + AllEvals + wrap DV over b1
      -- step proof), already computed there for wrap_b1's FOP.

      -- b2 slot-1 wrap-prev-evals: evaluations over b1 step proof.
      b2Slot1WrapPrevEvals :: AllEvals StepField
      b2Slot1WrapPrevEvals = b1StepAllEvals

      -- b2 slot-1 prevChalPolys: b1 step's per-slot cpc (captured during
      -- b1 step's buildStepAdviceWithOracles) paired with b1 slot's new
      -- bp_chals wrap-expanded.
      b2Slot1PrevChalPolys =
        { sg: b1Slot0ChalPolyComm, challenges: b1Slot0RealBpChalsWrap }
          :< { sg: b1Slot1ChalPolyComm, challenges: b1Slot1RealBpChalsWrap }
          :< Vector.nil

    -- b2 slot-0 advice: reuse oracleInput (NRR identical across b0/b1/b2).
    { advice: b2Slot0Advice, challengePolynomialCommitment: b2Slot0ChalPolyComm } <- liftEffect $
      buildStepAdviceWithOracles @0 @(PrevsSpecCons 0 PrevsSpecNil) oracleInput

    -- b2 slot-1 advice: verify REAL Tree b1 wrap proof.
    { advice: b2Slot1Advice, challengePolynomialCommitment: b2Slot1ChalPolyComm } <- liftEffect $
      buildStepAdviceWithOracles @2 @(PrevsSpecCons 2 PrevsSpecNil)
        { publicInput: unit
        , prevPublicInput: (F one) :: F StepField -- b1 output was 1
        , wrapDomainLog2: treeWrapDomainLog2
        , stepDomainLog2: treeSelfStepDomainLog2
        , wrapVK: treeWrapCR.verifierIndex
        , stepOpeningSg: b1StepOpeningSg
        , kimchiPrevSg: b1StepOpeningSg
        , wrapProof: b1TreeWrapResult.proof
        , wrapPublicInput: b1TreeWrapResult.publicInputs
        , prevChalPolys: b2Slot1PrevChalPolys
        , wrapPlonkRaw:
            { alpha: SizedF.unwrapF b1TreeWrapDv.plonk.alpha
            , beta: SizedF.unwrapF b1TreeWrapDv.plonk.beta
            , gamma: SizedF.unwrapF b1TreeWrapDv.plonk.gamma
            , zeta: SizedF.unwrapF b1TreeWrapDv.plonk.zeta
            }
        , wrapPrevEvals: b2Slot1WrapPrevEvals
        , wrapBranchData: b1TreeWrapDv.branchData
        , wrapSpongeDigest: b1TreeWrapDv.spongeDigestBeforeEvaluations
        , mustVerify: true
        -- wrap_b1 hashed [b1Slot0RealBpChalsWrap, b1Slot1RealBpChalsWrap]
        -- into its own msg_for_next_wrap_proof digest.
        , wrapOwnPaddedBpChals:
            b1Slot0RealBpChalsWrap
              :< b1Slot1RealBpChalsWrap
              :< Vector.nil
        , fopState:
            { deferredValues:
                { plonk: b1TreeWrapDv.plonk
                , combinedInnerProduct: b1TreeWrapDv.combinedInnerProduct
                , xi: b1TreeWrapDv.xi
                , bulletproofChallenges: b1TreeWrapDv.bulletproofPrechallenges
                , b: b1TreeWrapDv.b
                }
            , shouldFinalize: false
            , spongeDigestBeforeEvaluations: F b1TreeWrapDv.spongeDigestBeforeEvaluations
            }
        , stepAdvicePrevEvals: b2Slot1WrapPrevEvals
        -- kimchi prev_challenges for b2 slot 1: wrap_b1's own bp_chals
        -- expanded via step endo.
        , kimchiPrevChallengesExpanded:
            map
              (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
              b1TreeWrapDv.bulletproofPrechallenges
        -- prevChallengesForStepHash: wrap_b1.stmt.msg_for_next_step
        -- .old_bulletproof_challenges step-expanded. b1 step stored these
        -- (one per slot of its own two-slot prev):
        --   slot 0 (NRR verify): step-expansion of NRR wrap's bp_chals.
        --   slot 1 (real b0 wrap verify): step-expansion of b0 wrap's
        --          bp_chals = treeWrapDv.bulletproofPrechallenges
        --          step-expanded (NOT dummy — b1 step verified the REAL
        --          b0 wrap, not dummy like b0 step did).
        , prevChallengesForStepHash:
            map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
              nrr.wrapDv.bulletproofPrechallenges
              :< map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
                treeWrapDv.bulletproofPrechallenges
              :< Vector.nil
        }

    -- Splice b2 slot-0 + slot-1 advices into the heterogeneous carrier.
    let
      StepAdvice b2s0 = b2Slot0Advice
      StepAdvice b2s1 = b2Slot1Advice
      Tuple b2Slot0Sppw _ = b2s0.perProofSlotsCarrier
      Tuple b2Slot1Sppw _ = b2s1.perProofSlotsCarrier

      treeB2Advice :: StepAdvice TreeProofReturnPrevsSpec StepIPARounds WrapIPARounds Unit 2 _
      treeB2Advice = StepAdvice
        { perProofSlotsCarrier: Tuple b2Slot0Sppw (Tuple b2Slot1Sppw unit)
        , publicInput: unit
        , publicUnfinalizedProofs:
            Vector.head b2s0.publicUnfinalizedProofs
              :< Vector.head b2s1.publicUnfinalizedProofs
              :< Vector.nil
        , messagesForNextWrapProof:
            Vector.head b2s0.messagesForNextWrapProof
              :< Vector.head b2s1.messagesForNextWrapProof
              :< Vector.nil
        , wrapVerifierIndex: extractWrapVKCommsAdvice treeWrapCR.verifierIndex
        , kimchiPrevChallenges:
            Vector.head b2s0.kimchiPrevChallenges
              :< Vector.head b2s1.kimchiPrevChallenges
              :< Vector.nil
        }

    b2StepRes <- liftEffect $ runExceptT $
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
        (treeProofReturnRule b2RuleArgs)
        treeStepCR
        treeB2Advice
    b2StepResult <- case b2StepRes of
      Left e -> liftEffect $ Exc.throw ("b2 stepSolveAndProve: " <> show e)
      Right r -> pure r

    liftEffect $ for_ (Array.mapWithIndex Tuple b2StepResult.publicInputs) \(Tuple i x) ->
      Trace.field ("b2.step.proof.public_input." <> show i) x

    liftEffect $ Trace.string "tree_proof_return.end" "inductive_case_2_step_proved"

    -- =====================================================================
    -- b2 WRAP: wrap step_b2. Mirror of b1 wrap with b1→b2 (new) and
    -- b0→b1 (prev) substitutions. Per-slot kimchi prev_challenges use
    -- step_b2's slot{0,1}ChalPolyComm + wrap-expanded b2StepResult's
    -- per-slot new bp_chals (iter 2bf pattern).
    -- =====================================================================
    let
      -- b1 step opening sg: kimchi prev sg for step_b2 slot 1 (= wrap_b1
      -- stored this into its msg_for_next_wrap_proof.cpc).
      b1TreeStepOpeningSgOracle :: AffinePoint WrapField
      b1TreeStepOpeningSgOracle = b1TreeWrapProofSg

      -- kimchi prev_challenges absorbed by step_b2 per treeB2Advice:
      --   slot 0 (NRR): nrrBpChalsExpandedForSlot0 (same as all other bN)
      --   slot 1 (real wrap_b1): b1TreeWrapDv.bulletproofPrechallenges
      --                          step-expanded
      b2StepKimchiPrevChalsSlot0 :: Vector StepIPARounds StepField
      b2StepKimchiPrevChalsSlot0 = nrrBpChalsExpandedForSlot0

      b2StepKimchiPrevChalsSlot1 :: Vector StepIPARounds StepField
      b2StepKimchiPrevChalsSlot1 =
        map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
          b1TreeWrapDv.bulletproofPrechallenges

      b2StepOraclesTree = ProofFFI.pallasProofOracles treeStepCR.verifierIndex
        { proof: b2StepResult.proof
        , publicInput: b2StepResult.publicInputs
        , prevChallenges:
            [ { sgX: nrrStepOpeningSgOracle.x
              , sgY: nrrStepOpeningSgOracle.y
              , challenges: Vector.toUnfoldable b2StepKimchiPrevChalsSlot0
              }
            , { sgX: b1TreeStepOpeningSgOracle.x
              , sgY: b1TreeStepOpeningSgOracle.y
              , challenges: Vector.toUnfoldable b2StepKimchiPrevChalsSlot1
              }
            ]
        }

      b2StepAllEvals :: AllEvals StepField
      b2StepAllEvals =
        { ftEval1: b2StepOraclesTree.ftEval1
        , publicEvals:
            { zeta: b2StepOraclesTree.publicEvalZeta
            , omegaTimesZeta: b2StepOraclesTree.publicEvalZetaOmega
            }
        , zEvals: ProofFFI.proofZEvals b2StepResult.proof
        , witnessEvals: ProofFFI.proofWitnessEvals b2StepResult.proof
        , coeffEvals: ProofFFI.proofCoefficientEvals b2StepResult.proof
        , sigmaEvals: ProofFFI.proofSigmaEvals b2StepResult.proof
        , indexEvals: ProofFFI.proofIndexEvals b2StepResult.proof
        }

      b2TreeWrapDvInput :: WrapDeferredValuesInput 2
      b2TreeWrapDvInput =
        { proof: b2StepResult.proof
        , verifierIndex: treeStepCR.verifierIndex
        , publicInput: b2StepResult.publicInputs
        , allEvals: b2StepAllEvals
        , pEval0Chunks: [ b2StepOraclesTree.publicEvalZeta ]
        , domainLog2: treeStepDomainLog2
        , zkRows: 3
        , srsLengthLog2: 16
        , generator: (domainGenerator treeStepDomainLog2 :: StepField)
        , shifts: (domainShifts treeStepDomainLog2 :: Vector 7 StepField)
        , vanishesOnZk: ProofFFI.permutationVanishingPolynomial
            { domainLog2: treeStepDomainLog2, zkRows: 3, pt: b2StepOraclesTree.zeta }
        , omegaForLagrange: \_ -> one
        , endo: stepEndoScalar
        , linearizationPoly: Linearization.pallas
        , prevSgs: nrrStepOpeningSgOracle :< b1TreeStepOpeningSgOracle :< Vector.nil
        , prevChallenges:
            b2StepKimchiPrevChalsSlot0
              :< b2StepKimchiPrevChalsSlot1
              :< Vector.nil
        , proofsVerifiedMask: true :< true :< Vector.nil
        }

      b2TreeWrapDv = wrapComputeDeferredValues b2TreeWrapDvInput

      b2MsgForNextStepDigestTree :: StepField
      b2MsgForNextStepDigestTree =
        fromJust'
          "b2 wrap prove: step PI[64] outer hash must exist" $
          Array.index b2StepResult.publicInputs 64

      b2TreeWrapProofSg :: AffinePoint WrapField
      b2TreeWrapProofSg = ProofFFI.pallasProofOpeningSg b2StepResult.proof

      PerProofUnfinalized b2Slot0UnfRec =
        Vector.head (unwrap treeB2Advice).publicUnfinalizedProofs

      PerProofUnfinalized b2Slot1UnfRec =
        Vector.head (Vector.drop @1 (unwrap treeB2Advice).publicUnfinalizedProofs)

      b2Slot0RealBpChalsWrap :: Vector WrapIPARounds WrapField
      b2Slot0RealBpChalsWrap =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF 128 WrapField)
                treeWrapEndoScalar
          )
          b2Slot0UnfRec.bulletproofChallenges

      b2Slot1RealBpChalsWrap :: Vector WrapIPARounds WrapField
      b2Slot1RealBpChalsWrap =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF 128 WrapField)
                treeWrapEndoScalar
          )
          b2Slot1UnfRec.bulletproofChallenges

      b2MsgForNextWrapDigestTree :: WrapField
      b2MsgForNextWrapDigestTree = hashMessagesForNextWrapProofPureGeneral
        { sg: b2TreeWrapProofSg
        , paddedChallenges:
            b2Slot0RealBpChalsWrap
              :< b2Slot1RealBpChalsWrap
              :< Vector.nil
        }

      b2TreeWrapPublicInput = assembleWrapMainInput
        { deferredValues: b2TreeWrapDv
        , messagesForNextStepProofDigest: b2MsgForNextStepDigestTree
        , messagesForNextWrapProofDigest: b2MsgForNextWrapDigestTree
        }

      b2Slot0PerProof = convertSlotUnf b2Slot0UnfRec
      b2Slot1PerProof = convertSlotUnf b2Slot1UnfRec

      -- prev_step_accs: slot 0 = NRR wrap's stored sg (nrrStepOpeningSg),
      -- slot 1 = b1 wrap's stored sg (= b1 step opening sg).
      b2Slot0StepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
      b2Slot0StepAcc = WeierstrassAffinePoint
        { x: F nrrStepOpeningSg.x, y: F nrrStepOpeningSg.y }

      b2Slot1StepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
      b2Slot1StepAcc = WeierstrassAffinePoint
        { x: F b1TreeStepOpeningSgOracle.x, y: F b1TreeStepOpeningSgOracle.y }

      -- Slot 0 (NRR wrap): reuse b0's NRR eval computation.
      b2Slot0PrevEvalsW :: StepAllEvals (F WrapField)
      b2Slot0PrevEvalsW = slot0PrevEvalsW

      -- Slot 1 (Tree b1 wrap, real): oracles + evals over b1TreeWrapResult
      -- .proof with b1 wrap's actual kimchi prev_challenges (iter 2bf
      -- pattern: per-slot cpc = b1Slot{0,1}ChalPolyComm, per-slot chals
      -- = b1Slot{0,1}RealBpChalsWrap).
      b2Slot1PrevEvalsW :: StepAllEvals (F WrapField)
      b2Slot1PrevEvalsW =
        let
          o = ProofFFI.vestaProofOracles treeWrapCR.verifierIndex
            { proof: b1TreeWrapResult.proof
            , publicInput: b1TreeWrapResult.publicInputs
            , prevChallenges:
                [ { sgX: b1Slot0ChalPolyComm.x
                  , sgY: b1Slot0ChalPolyComm.y
                  , challenges: Vector.toUnfoldable b1Slot0RealBpChalsWrap
                  }
                , { sgX: b1Slot1ChalPolyComm.x
                  , sgY: b1Slot1ChalPolyComm.y
                  , challenges: Vector.toUnfoldable b1Slot1RealBpChalsWrap
                  }
                ]
            }
          mkPE p = { zeta: F p.zeta, omegaTimesZeta: F p.omegaTimesZeta }
        in
          StepAllEvals
            { ftEval1: F o.ftEval1
            , publicEvals: PointEval
                { zeta: F o.publicEvalZeta
                , omegaTimesZeta: F o.publicEvalZetaOmega
                }
            , zEvals: PointEval (mkPE (ProofFFI.proofZEvals b1TreeWrapResult.proof))
            , witnessEvals: map (PointEval <<< mkPE) (ProofFFI.proofWitnessEvals b1TreeWrapResult.proof)
            , coeffEvals: map (PointEval <<< mkPE) (ProofFFI.proofCoefficientEvals b1TreeWrapResult.proof)
            , sigmaEvals: map (PointEval <<< mkPE) (ProofFFI.proofSigmaEvals b1TreeWrapResult.proof)
            , indexEvals: map (PointEval <<< mkPE) (ProofFFI.proofIndexEvals b1TreeWrapResult.proof)
            }

      b2TreeWrapAdviceInput :: BuildWrapAdviceInput 2 (Slots2 0 2)
      b2TreeWrapAdviceInput =
        { stepProof: b2StepResult.proof
        , whichBranch: F zero
        , prevUnfinalizedProofs: b2Slot0PerProof :< b2Slot1PerProof :< Vector.nil
        , prevMessagesForNextStepProofHash:
            F (fromBigInt (toBigInt b2MsgForNextStepDigestTree) :: WrapField)
        , prevStepAccs: b2Slot0StepAcc :< b2Slot1StepAcc :< Vector.nil
        -- wrap_b1 forwarded step_b1's per-slot bp_chals wrap-expanded
        -- into its msg_for_next_wrap_proof → b1Slot{0,1}RealBpChalsWrap.
        , prevOldBpChals: slots2 Vector.nil
            ( map F b1Slot0RealBpChalsWrap
                :< map F b1Slot1RealBpChalsWrap
                :< Vector.nil
            )
        , prevEvals: b2Slot0PrevEvalsW :< b2Slot1PrevEvalsW :< Vector.nil
        , prevWrapDomainIndices:
            F (fromInt 0 :: WrapField) :< F (fromInt 1 :: WrapField) :< Vector.nil
        }

      b2TreeWrapAdvice :: WrapAdvice 2 (Slots2 0 2)
      b2TreeWrapAdvice = buildWrapAdvice b2TreeWrapAdviceInput

      b2TreeWrapProveCtx =
        { wrapMainConfig: treeWrapCtx.wrapMainConfig
        , crs: pallasWrapSrs
        , publicInput: b2TreeWrapPublicInput
        , advice: b2TreeWrapAdvice
        , debug: true
        , kimchiPrevChallenges:
            { sgX: b2Slot0ChalPolyComm.x
            , sgY: b2Slot0ChalPolyComm.y
            , challenges: b2Slot0RealBpChalsWrap
            }
              :<
                { sgX: b2Slot1ChalPolyComm.x
                , sgY: b2Slot1ChalPolyComm.y
                , challenges: b2Slot1RealBpChalsWrap
                }
              :<
                Vector.nil
        }

    b2TreeWrapRes <- liftEffect $ runExceptT $
      wrapSolveAndProve @1 @(Slots2 0 2) b2TreeWrapProveCtx treeWrapCR
    b2TreeWrapResult <- case b2TreeWrapRes of
      Left e -> liftEffect $ Exc.throw ("b2 tree wrapSolveAndProve: " <> show e)
      Right r -> pure r

    liftEffect $ for_ (Array.mapWithIndex Tuple b2TreeWrapResult.publicInputs) \(Tuple i x) ->
      Trace.field ("b2.wrap.proof.public_input." <> show i) x

    liftEffect $ Trace.string "tree_proof_return.end" "inductive_case_2_proved"

    -- =====================================================================
    -- INDUCTIVE CASE (b3): slot 0 = NRR (unchanged), slot 1 = REAL Tree b2
    -- wrap proof replacing b1. Expected public_output = 3 (= 1 + s2 with
    -- s2=2). Mirror of b2 step with b1→b2 (prev) and b2→b3 (new)
    -- substitutions.
    --
    -- Step-only block; b3 wrap is deferred to a separate block.
    -- =====================================================================
    liftEffect $ Trace.string "tree_proof_return.begin" "inductive_case_3"

    let
      b3RuleArgs =
        { isBaseCase: false
        , nrrInputVal: F zero -- NRR's output is always 0
        , prevInputVal: F (fromInt 2 :: StepField) -- b2's output was 2
        }

      -- b2's Tree step proof opening sg: reuse b2TreeWrapProofSg from the
      -- b2 wrap block (= pallasProofOpeningSg b2StepResult.proof).
      b2StepOpeningSg :: AffinePoint WrapField
      b2StepOpeningSg = b2TreeWrapProofSg

      -- Reuse b2StepOraclesTree / b2StepAllEvals / b2TreeWrapDv from the
      -- b2 wrap block: same data (oracles + AllEvals + wrap DV over b2
      -- step proof), already computed there for wrap_b2's FOP.

      -- b3 slot-1 wrap-prev-evals: evaluations over b2 step proof.
      b3Slot1WrapPrevEvals :: AllEvals StepField
      b3Slot1WrapPrevEvals = b2StepAllEvals

      -- b3 slot-1 prevChalPolys: b2 step's per-slot cpc paired with b2
      -- slot's new bp_chals wrap-expanded.
      b3Slot1PrevChalPolys =
        { sg: b2Slot0ChalPolyComm, challenges: b2Slot0RealBpChalsWrap }
          :< { sg: b2Slot1ChalPolyComm, challenges: b2Slot1RealBpChalsWrap }
          :< Vector.nil

    -- b3 slot-0 advice: reuse oracleInput (NRR identical across all bN).
    { advice: b3Slot0Advice, challengePolynomialCommitment: b3Slot0ChalPolyComm } <- liftEffect $
      buildStepAdviceWithOracles @0 @(PrevsSpecCons 0 PrevsSpecNil) oracleInput

    -- b3 slot-1 advice: verify REAL Tree b2 wrap proof.
    { advice: b3Slot1Advice, challengePolynomialCommitment: b3Slot1ChalPolyComm } <- liftEffect $
      buildStepAdviceWithOracles @2 @(PrevsSpecCons 2 PrevsSpecNil)
        { publicInput: unit
        , prevPublicInput: (F (fromInt 2 :: StepField)) -- b2 output = 2
        , wrapDomainLog2: treeWrapDomainLog2
        , stepDomainLog2: treeSelfStepDomainLog2
        , wrapVK: treeWrapCR.verifierIndex
        , stepOpeningSg: b2StepOpeningSg
        , kimchiPrevSg: b2StepOpeningSg
        , wrapProof: b2TreeWrapResult.proof
        , wrapPublicInput: b2TreeWrapResult.publicInputs
        , prevChalPolys: b3Slot1PrevChalPolys
        , wrapPlonkRaw:
            { alpha: SizedF.unwrapF b2TreeWrapDv.plonk.alpha
            , beta: SizedF.unwrapF b2TreeWrapDv.plonk.beta
            , gamma: SizedF.unwrapF b2TreeWrapDv.plonk.gamma
            , zeta: SizedF.unwrapF b2TreeWrapDv.plonk.zeta
            }
        , wrapPrevEvals: b3Slot1WrapPrevEvals
        , wrapBranchData: b2TreeWrapDv.branchData
        , wrapSpongeDigest: b2TreeWrapDv.spongeDigestBeforeEvaluations
        , mustVerify: true
        -- wrap_b2 hashed [b2Slot0RealBpChalsWrap, b2Slot1RealBpChalsWrap]
        -- into its own msg_for_next_wrap_proof digest.
        , wrapOwnPaddedBpChals:
            b2Slot0RealBpChalsWrap
              :< b2Slot1RealBpChalsWrap
              :< Vector.nil
        , fopState:
            { deferredValues:
                { plonk: b2TreeWrapDv.plonk
                , combinedInnerProduct: b2TreeWrapDv.combinedInnerProduct
                , xi: b2TreeWrapDv.xi
                , bulletproofChallenges: b2TreeWrapDv.bulletproofPrechallenges
                , b: b2TreeWrapDv.b
                }
            , shouldFinalize: false
            , spongeDigestBeforeEvaluations: F b2TreeWrapDv.spongeDigestBeforeEvaluations
            }
        , stepAdvicePrevEvals: b3Slot1WrapPrevEvals
        -- kimchi prev_challenges for b3 slot 1: wrap_b2's own bp_chals
        -- expanded via step endo.
        , kimchiPrevChallengesExpanded:
            map
              (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
              b2TreeWrapDv.bulletproofPrechallenges
        -- prevChallengesForStepHash: wrap_b2.stmt.msg_for_next_step
        -- .old_bulletproof_challenges step-expanded. b2 step stored:
        --   slot 0 (NRR verify): step-expansion of NRR wrap's bp_chals.
        --   slot 1 (real wrap_b1 verify): step-expansion of wrap_b1's
        --          bp_chals = b1TreeWrapDv.bulletproofPrechallenges
        --          step-expanded.
        , prevChallengesForStepHash:
            map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
              nrr.wrapDv.bulletproofPrechallenges
              :< map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
                b1TreeWrapDv.bulletproofPrechallenges
              :< Vector.nil
        }

    -- Splice b3 slot-0 + slot-1 advices into the heterogeneous carrier.
    let
      StepAdvice b3s0 = b3Slot0Advice
      StepAdvice b3s1 = b3Slot1Advice
      Tuple b3Slot0Sppw _ = b3s0.perProofSlotsCarrier
      Tuple b3Slot1Sppw _ = b3s1.perProofSlotsCarrier

      treeB3Advice :: StepAdvice TreeProofReturnPrevsSpec StepIPARounds WrapIPARounds Unit 2 _
      treeB3Advice = StepAdvice
        { perProofSlotsCarrier: Tuple b3Slot0Sppw (Tuple b3Slot1Sppw unit)
        , publicInput: unit
        , publicUnfinalizedProofs:
            Vector.head b3s0.publicUnfinalizedProofs
              :< Vector.head b3s1.publicUnfinalizedProofs
              :< Vector.nil
        , messagesForNextWrapProof:
            Vector.head b3s0.messagesForNextWrapProof
              :< Vector.head b3s1.messagesForNextWrapProof
              :< Vector.nil
        , wrapVerifierIndex: extractWrapVKCommsAdvice treeWrapCR.verifierIndex
        , kimchiPrevChallenges:
            Vector.head b3s0.kimchiPrevChallenges
              :< Vector.head b3s1.kimchiPrevChallenges
              :< Vector.nil
        }

    b3StepRes <- liftEffect $ runExceptT $
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
        (treeProofReturnRule b3RuleArgs)
        treeStepCR
        treeB3Advice
    b3StepResult <- case b3StepRes of
      Left e -> liftEffect $ Exc.throw ("b3 stepSolveAndProve: " <> show e)
      Right r -> pure r

    liftEffect $ for_ (Array.mapWithIndex Tuple b3StepResult.publicInputs) \(Tuple i x) ->
      Trace.field ("b3.step.proof.public_input." <> show i) x

    liftEffect $ Trace.string "tree_proof_return.end" "inductive_case_3_step_proved"

    -- =====================================================================
    -- b3 WRAP: wrap step_b3. Mirror of b2 wrap with b2→b3 (new) and
    -- b1→b2 (prev) substitutions. Per-slot kimchi prev_challenges use
    -- step_b3's slot{0,1}ChalPolyComm + wrap-expanded b3StepResult's
    -- per-slot new bp_chals (iter 2bf pattern).
    -- =====================================================================
    let
      -- b2 step opening sg: kimchi prev sg for step_b3 slot 1 (= wrap_b2
      -- stored this into its msg_for_next_wrap_proof.cpc).
      b2TreeStepOpeningSgOracle :: AffinePoint WrapField
      b2TreeStepOpeningSgOracle = b2TreeWrapProofSg

      -- kimchi prev_challenges absorbed by step_b3 per treeB3Advice:
      --   slot 0 (NRR): nrrBpChalsExpandedForSlot0 (same as all other bN)
      --   slot 1 (real wrap_b2): b2TreeWrapDv.bulletproofPrechallenges
      --                          step-expanded
      b3StepKimchiPrevChalsSlot0 :: Vector StepIPARounds StepField
      b3StepKimchiPrevChalsSlot0 = nrrBpChalsExpandedForSlot0

      b3StepKimchiPrevChalsSlot1 :: Vector StepIPARounds StepField
      b3StepKimchiPrevChalsSlot1 =
        map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
          b2TreeWrapDv.bulletproofPrechallenges

      b3StepOraclesTree = ProofFFI.pallasProofOracles treeStepCR.verifierIndex
        { proof: b3StepResult.proof
        , publicInput: b3StepResult.publicInputs
        , prevChallenges:
            [ { sgX: nrrStepOpeningSgOracle.x
              , sgY: nrrStepOpeningSgOracle.y
              , challenges: Vector.toUnfoldable b3StepKimchiPrevChalsSlot0
              }
            , { sgX: b2TreeStepOpeningSgOracle.x
              , sgY: b2TreeStepOpeningSgOracle.y
              , challenges: Vector.toUnfoldable b3StepKimchiPrevChalsSlot1
              }
            ]
        }

      b3StepAllEvals :: AllEvals StepField
      b3StepAllEvals =
        { ftEval1: b3StepOraclesTree.ftEval1
        , publicEvals:
            { zeta: b3StepOraclesTree.publicEvalZeta
            , omegaTimesZeta: b3StepOraclesTree.publicEvalZetaOmega
            }
        , zEvals: ProofFFI.proofZEvals b3StepResult.proof
        , witnessEvals: ProofFFI.proofWitnessEvals b3StepResult.proof
        , coeffEvals: ProofFFI.proofCoefficientEvals b3StepResult.proof
        , sigmaEvals: ProofFFI.proofSigmaEvals b3StepResult.proof
        , indexEvals: ProofFFI.proofIndexEvals b3StepResult.proof
        }

      b3TreeWrapDvInput :: WrapDeferredValuesInput 2
      b3TreeWrapDvInput =
        { proof: b3StepResult.proof
        , verifierIndex: treeStepCR.verifierIndex
        , publicInput: b3StepResult.publicInputs
        , allEvals: b3StepAllEvals
        , pEval0Chunks: [ b3StepOraclesTree.publicEvalZeta ]
        , domainLog2: treeStepDomainLog2
        , zkRows: 3
        , srsLengthLog2: 16
        , generator: (domainGenerator treeStepDomainLog2 :: StepField)
        , shifts: (domainShifts treeStepDomainLog2 :: Vector 7 StepField)
        , vanishesOnZk: ProofFFI.permutationVanishingPolynomial
            { domainLog2: treeStepDomainLog2, zkRows: 3, pt: b3StepOraclesTree.zeta }
        , omegaForLagrange: \_ -> one
        , endo: stepEndoScalar
        , linearizationPoly: Linearization.pallas
        , prevSgs: nrrStepOpeningSgOracle :< b2TreeStepOpeningSgOracle :< Vector.nil
        , prevChallenges:
            b3StepKimchiPrevChalsSlot0
              :< b3StepKimchiPrevChalsSlot1
              :< Vector.nil
        , proofsVerifiedMask: true :< true :< Vector.nil
        }

      b3TreeWrapDv = wrapComputeDeferredValues b3TreeWrapDvInput

      b3MsgForNextStepDigestTree :: StepField
      b3MsgForNextStepDigestTree =
        fromJust'
          "b3 wrap prove: step PI[64] outer hash must exist" $
          Array.index b3StepResult.publicInputs 64

      b3TreeWrapProofSg :: AffinePoint WrapField
      b3TreeWrapProofSg = ProofFFI.pallasProofOpeningSg b3StepResult.proof

      PerProofUnfinalized b3Slot0UnfRec =
        Vector.head (unwrap treeB3Advice).publicUnfinalizedProofs

      PerProofUnfinalized b3Slot1UnfRec =
        Vector.head (Vector.drop @1 (unwrap treeB3Advice).publicUnfinalizedProofs)

      b3Slot0RealBpChalsWrap :: Vector WrapIPARounds WrapField
      b3Slot0RealBpChalsWrap =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF 128 WrapField)
                treeWrapEndoScalar
          )
          b3Slot0UnfRec.bulletproofChallenges

      b3Slot1RealBpChalsWrap :: Vector WrapIPARounds WrapField
      b3Slot1RealBpChalsWrap =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF 128 WrapField)
                treeWrapEndoScalar
          )
          b3Slot1UnfRec.bulletproofChallenges

      b3MsgForNextWrapDigestTree :: WrapField
      b3MsgForNextWrapDigestTree = hashMessagesForNextWrapProofPureGeneral
        { sg: b3TreeWrapProofSg
        , paddedChallenges:
            b3Slot0RealBpChalsWrap
              :< b3Slot1RealBpChalsWrap
              :< Vector.nil
        }

      b3TreeWrapPublicInput = assembleWrapMainInput
        { deferredValues: b3TreeWrapDv
        , messagesForNextStepProofDigest: b3MsgForNextStepDigestTree
        , messagesForNextWrapProofDigest: b3MsgForNextWrapDigestTree
        }

      b3Slot0PerProof = convertSlotUnf b3Slot0UnfRec
      b3Slot1PerProof = convertSlotUnf b3Slot1UnfRec

      -- prev_step_accs: slot 0 = NRR wrap's stored sg, slot 1 = b2 wrap's
      -- stored sg (= b2 step opening sg).
      b3Slot0StepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
      b3Slot0StepAcc = WeierstrassAffinePoint
        { x: F nrrStepOpeningSg.x, y: F nrrStepOpeningSg.y }

      b3Slot1StepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
      b3Slot1StepAcc = WeierstrassAffinePoint
        { x: F b2TreeStepOpeningSgOracle.x, y: F b2TreeStepOpeningSgOracle.y }

      -- Slot 0 (NRR wrap): reuse b0's NRR eval computation.
      b3Slot0PrevEvalsW :: StepAllEvals (F WrapField)
      b3Slot0PrevEvalsW = slot0PrevEvalsW

      -- Slot 1 (Tree b2 wrap, real): oracles + evals over b2TreeWrapResult
      -- .proof with b2 wrap's actual kimchi prev_challenges (iter 2bf
      -- pattern: per-slot cpc = b2Slot{0,1}ChalPolyComm, per-slot chals
      -- = b2Slot{0,1}RealBpChalsWrap).
      b3Slot1PrevEvalsW :: StepAllEvals (F WrapField)
      b3Slot1PrevEvalsW =
        let
          o = ProofFFI.vestaProofOracles treeWrapCR.verifierIndex
            { proof: b2TreeWrapResult.proof
            , publicInput: b2TreeWrapResult.publicInputs
            , prevChallenges:
                [ { sgX: b2Slot0ChalPolyComm.x
                  , sgY: b2Slot0ChalPolyComm.y
                  , challenges: Vector.toUnfoldable b2Slot0RealBpChalsWrap
                  }
                , { sgX: b2Slot1ChalPolyComm.x
                  , sgY: b2Slot1ChalPolyComm.y
                  , challenges: Vector.toUnfoldable b2Slot1RealBpChalsWrap
                  }
                ]
            }
          mkPE p = { zeta: F p.zeta, omegaTimesZeta: F p.omegaTimesZeta }
        in
          StepAllEvals
            { ftEval1: F o.ftEval1
            , publicEvals: PointEval
                { zeta: F o.publicEvalZeta
                , omegaTimesZeta: F o.publicEvalZetaOmega
                }
            , zEvals: PointEval (mkPE (ProofFFI.proofZEvals b2TreeWrapResult.proof))
            , witnessEvals: map (PointEval <<< mkPE) (ProofFFI.proofWitnessEvals b2TreeWrapResult.proof)
            , coeffEvals: map (PointEval <<< mkPE) (ProofFFI.proofCoefficientEvals b2TreeWrapResult.proof)
            , sigmaEvals: map (PointEval <<< mkPE) (ProofFFI.proofSigmaEvals b2TreeWrapResult.proof)
            , indexEvals: map (PointEval <<< mkPE) (ProofFFI.proofIndexEvals b2TreeWrapResult.proof)
            }

      b3TreeWrapAdviceInput :: BuildWrapAdviceInput 2 (Slots2 0 2)
      b3TreeWrapAdviceInput =
        { stepProof: b3StepResult.proof
        , whichBranch: F zero
        , prevUnfinalizedProofs: b3Slot0PerProof :< b3Slot1PerProof :< Vector.nil
        , prevMessagesForNextStepProofHash:
            F (fromBigInt (toBigInt b3MsgForNextStepDigestTree) :: WrapField)
        , prevStepAccs: b3Slot0StepAcc :< b3Slot1StepAcc :< Vector.nil
        -- wrap_b2 forwarded step_b2's per-slot bp_chals wrap-expanded
        -- into its msg_for_next_wrap_proof → b2Slot{0,1}RealBpChalsWrap.
        , prevOldBpChals: slots2 Vector.nil
            ( map F b2Slot0RealBpChalsWrap
                :< map F b2Slot1RealBpChalsWrap
                :< Vector.nil
            )
        , prevEvals: b3Slot0PrevEvalsW :< b3Slot1PrevEvalsW :< Vector.nil
        , prevWrapDomainIndices:
            F (fromInt 0 :: WrapField) :< F (fromInt 1 :: WrapField) :< Vector.nil
        }

      b3TreeWrapAdvice :: WrapAdvice 2 (Slots2 0 2)
      b3TreeWrapAdvice = buildWrapAdvice b3TreeWrapAdviceInput

      b3TreeWrapProveCtx =
        { wrapMainConfig: treeWrapCtx.wrapMainConfig
        , crs: pallasWrapSrs
        , publicInput: b3TreeWrapPublicInput
        , advice: b3TreeWrapAdvice
        , debug: true
        , kimchiPrevChallenges:
            { sgX: b3Slot0ChalPolyComm.x
            , sgY: b3Slot0ChalPolyComm.y
            , challenges: b3Slot0RealBpChalsWrap
            }
              :<
                { sgX: b3Slot1ChalPolyComm.x
                , sgY: b3Slot1ChalPolyComm.y
                , challenges: b3Slot1RealBpChalsWrap
                }
              :<
                Vector.nil
        }

    b3TreeWrapRes <- liftEffect $ runExceptT $
      wrapSolveAndProve @1 @(Slots2 0 2) b3TreeWrapProveCtx treeWrapCR
    b3TreeWrapResult <- case b3TreeWrapRes of
      Left e -> liftEffect $ Exc.throw ("b3 tree wrapSolveAndProve: " <> show e)
      Right r -> pure r

    liftEffect $ for_ (Array.mapWithIndex Tuple b3TreeWrapResult.publicInputs) \(Tuple i x) ->
      Trace.field ("b3.wrap.proof.public_input." <> show i) x

    liftEffect $ Trace.string "tree_proof_return.end" "inductive_case_3_proved"

    -- =====================================================================
    -- INDUCTIVE CASE (b4): slot 0 = NRR (unchanged), slot 1 = REAL Tree b3
    -- wrap proof replacing b2. Expected public_output = 4 (= 1 + s3 with
    -- s3=3). Final round — by b4 all initial base-case dummy values have
    -- cycled out of the visible slot-1 chain. Mirror of b3 step with
    -- b2→b3 (prev) and b3→b4 (new) substitutions.
    -- =====================================================================
    liftEffect $ Trace.string "tree_proof_return.begin" "inductive_case_4"

    let
      b4RuleArgs =
        { isBaseCase: false
        , nrrInputVal: F zero -- NRR's output is always 0
        , prevInputVal: F (fromInt 3 :: StepField) -- b3's output was 3
        }

      -- b3's Tree step proof opening sg: reuse b3TreeWrapProofSg from the
      -- b3 wrap block (= pallasProofOpeningSg b3StepResult.proof).
      b3StepOpeningSg :: AffinePoint WrapField
      b3StepOpeningSg = b3TreeWrapProofSg

      -- Reuse b3StepAllEvals / b3TreeWrapDv from the b3 wrap block.

      b4Slot1WrapPrevEvals :: AllEvals StepField
      b4Slot1WrapPrevEvals = b3StepAllEvals

      b4Slot1PrevChalPolys =
        { sg: b3Slot0ChalPolyComm, challenges: b3Slot0RealBpChalsWrap }
          :< { sg: b3Slot1ChalPolyComm, challenges: b3Slot1RealBpChalsWrap }
          :< Vector.nil

    { advice: b4Slot0Advice, challengePolynomialCommitment: b4Slot0ChalPolyComm } <- liftEffect $
      buildStepAdviceWithOracles @0 @(PrevsSpecCons 0 PrevsSpecNil) oracleInput

    -- b4 slot-1 advice: verify REAL Tree b3 wrap proof.
    { advice: b4Slot1Advice, challengePolynomialCommitment: b4Slot1ChalPolyComm } <- liftEffect $
      buildStepAdviceWithOracles @2 @(PrevsSpecCons 2 PrevsSpecNil)
        { publicInput: unit
        , prevPublicInput: (F (fromInt 3 :: StepField)) -- b3 output = 3
        , wrapDomainLog2: treeWrapDomainLog2
        , stepDomainLog2: treeSelfStepDomainLog2
        , wrapVK: treeWrapCR.verifierIndex
        , stepOpeningSg: b3StepOpeningSg
        , kimchiPrevSg: b3StepOpeningSg
        , wrapProof: b3TreeWrapResult.proof
        , wrapPublicInput: b3TreeWrapResult.publicInputs
        , prevChalPolys: b4Slot1PrevChalPolys
        , wrapPlonkRaw:
            { alpha: SizedF.unwrapF b3TreeWrapDv.plonk.alpha
            , beta: SizedF.unwrapF b3TreeWrapDv.plonk.beta
            , gamma: SizedF.unwrapF b3TreeWrapDv.plonk.gamma
            , zeta: SizedF.unwrapF b3TreeWrapDv.plonk.zeta
            }
        , wrapPrevEvals: b4Slot1WrapPrevEvals
        , wrapBranchData: b3TreeWrapDv.branchData
        , wrapSpongeDigest: b3TreeWrapDv.spongeDigestBeforeEvaluations
        , mustVerify: true
        -- wrap_b3 hashed [b3Slot0RealBpChalsWrap, b3Slot1RealBpChalsWrap]
        -- into its own msg_for_next_wrap_proof digest.
        , wrapOwnPaddedBpChals:
            b3Slot0RealBpChalsWrap
              :< b3Slot1RealBpChalsWrap
              :< Vector.nil
        , fopState:
            { deferredValues:
                { plonk: b3TreeWrapDv.plonk
                , combinedInnerProduct: b3TreeWrapDv.combinedInnerProduct
                , xi: b3TreeWrapDv.xi
                , bulletproofChallenges: b3TreeWrapDv.bulletproofPrechallenges
                , b: b3TreeWrapDv.b
                }
            , shouldFinalize: false
            , spongeDigestBeforeEvaluations: F b3TreeWrapDv.spongeDigestBeforeEvaluations
            }
        , stepAdvicePrevEvals: b4Slot1WrapPrevEvals
        , kimchiPrevChallengesExpanded:
            map
              (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
              b3TreeWrapDv.bulletproofPrechallenges
        -- prevChallengesForStepHash: wrap_b3.stmt.msg_for_next_step
        -- .old_bulletproof_challenges step-expanded. b3 step stored:
        --   slot 0 (NRR verify): step-expansion of NRR wrap's bp_chals.
        --   slot 1 (real wrap_b2 verify): step-expansion of wrap_b2's
        --          bp_chals = b2TreeWrapDv.bulletproofPrechallenges
        --          step-expanded.
        , prevChallengesForStepHash:
            map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
              nrr.wrapDv.bulletproofPrechallenges
              :< map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
                b2TreeWrapDv.bulletproofPrechallenges
              :< Vector.nil
        }

    let
      StepAdvice b4s0 = b4Slot0Advice
      StepAdvice b4s1 = b4Slot1Advice
      Tuple b4Slot0Sppw _ = b4s0.perProofSlotsCarrier
      Tuple b4Slot1Sppw _ = b4s1.perProofSlotsCarrier

      treeB4Advice :: StepAdvice TreeProofReturnPrevsSpec StepIPARounds WrapIPARounds Unit 2 _
      treeB4Advice = StepAdvice
        { perProofSlotsCarrier: Tuple b4Slot0Sppw (Tuple b4Slot1Sppw unit)
        , publicInput: unit
        , publicUnfinalizedProofs:
            Vector.head b4s0.publicUnfinalizedProofs
              :< Vector.head b4s1.publicUnfinalizedProofs
              :< Vector.nil
        , messagesForNextWrapProof:
            Vector.head b4s0.messagesForNextWrapProof
              :< Vector.head b4s1.messagesForNextWrapProof
              :< Vector.nil
        , wrapVerifierIndex: extractWrapVKCommsAdvice treeWrapCR.verifierIndex
        , kimchiPrevChallenges:
            Vector.head b4s0.kimchiPrevChallenges
              :< Vector.head b4s1.kimchiPrevChallenges
              :< Vector.nil
        }

    b4StepRes <- liftEffect $ runExceptT $
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
        (treeProofReturnRule b4RuleArgs)
        treeStepCR
        treeB4Advice
    b4StepResult <- case b4StepRes of
      Left e -> liftEffect $ Exc.throw ("b4 stepSolveAndProve: " <> show e)
      Right r -> pure r

    liftEffect $ for_ (Array.mapWithIndex Tuple b4StepResult.publicInputs) \(Tuple i x) ->
      Trace.field ("b4.step.proof.public_input." <> show i) x

    liftEffect $ Trace.string "tree_proof_return.end" "inductive_case_4_step_proved"

    -- =====================================================================
    -- b4 WRAP: wrap step_b4. Mirror of b3 wrap with b3→b4 (new) and
    -- b2→b3 (prev) substitutions. Per-slot kimchi prev_challenges use
    -- step_b4's slot{0,1}ChalPolyComm + wrap-expanded b4StepResult's
    -- per-slot new bp_chals (iter 2bf pattern).
    -- =====================================================================
    let
      -- b3 step opening sg: kimchi prev sg for step_b4 slot 1.
      b3TreeStepOpeningSgOracle :: AffinePoint WrapField
      b3TreeStepOpeningSgOracle = b3TreeWrapProofSg

      b4StepKimchiPrevChalsSlot0 :: Vector StepIPARounds StepField
      b4StepKimchiPrevChalsSlot0 = nrrBpChalsExpandedForSlot0

      b4StepKimchiPrevChalsSlot1 :: Vector StepIPARounds StepField
      b4StepKimchiPrevChalsSlot1 =
        map (\sf -> toFieldPure (SizedF.unwrapF sf) stepEndoScalar)
          b3TreeWrapDv.bulletproofPrechallenges

      b4StepOraclesTree = ProofFFI.pallasProofOracles treeStepCR.verifierIndex
        { proof: b4StepResult.proof
        , publicInput: b4StepResult.publicInputs
        , prevChallenges:
            [ { sgX: nrrStepOpeningSgOracle.x
              , sgY: nrrStepOpeningSgOracle.y
              , challenges: Vector.toUnfoldable b4StepKimchiPrevChalsSlot0
              }
            , { sgX: b3TreeStepOpeningSgOracle.x
              , sgY: b3TreeStepOpeningSgOracle.y
              , challenges: Vector.toUnfoldable b4StepKimchiPrevChalsSlot1
              }
            ]
        }

      b4StepAllEvals :: AllEvals StepField
      b4StepAllEvals =
        { ftEval1: b4StepOraclesTree.ftEval1
        , publicEvals:
            { zeta: b4StepOraclesTree.publicEvalZeta
            , omegaTimesZeta: b4StepOraclesTree.publicEvalZetaOmega
            }
        , zEvals: ProofFFI.proofZEvals b4StepResult.proof
        , witnessEvals: ProofFFI.proofWitnessEvals b4StepResult.proof
        , coeffEvals: ProofFFI.proofCoefficientEvals b4StepResult.proof
        , sigmaEvals: ProofFFI.proofSigmaEvals b4StepResult.proof
        , indexEvals: ProofFFI.proofIndexEvals b4StepResult.proof
        }

      b4TreeWrapDvInput :: WrapDeferredValuesInput 2
      b4TreeWrapDvInput =
        { proof: b4StepResult.proof
        , verifierIndex: treeStepCR.verifierIndex
        , publicInput: b4StepResult.publicInputs
        , allEvals: b4StepAllEvals
        , pEval0Chunks: [ b4StepOraclesTree.publicEvalZeta ]
        , domainLog2: treeStepDomainLog2
        , zkRows: 3
        , srsLengthLog2: 16
        , generator: (domainGenerator treeStepDomainLog2 :: StepField)
        , shifts: (domainShifts treeStepDomainLog2 :: Vector 7 StepField)
        , vanishesOnZk: ProofFFI.permutationVanishingPolynomial
            { domainLog2: treeStepDomainLog2, zkRows: 3, pt: b4StepOraclesTree.zeta }
        , omegaForLagrange: \_ -> one
        , endo: stepEndoScalar
        , linearizationPoly: Linearization.pallas
        , prevSgs: nrrStepOpeningSgOracle :< b3TreeStepOpeningSgOracle :< Vector.nil
        , prevChallenges:
            b4StepKimchiPrevChalsSlot0
              :< b4StepKimchiPrevChalsSlot1
              :< Vector.nil
        , proofsVerifiedMask: true :< true :< Vector.nil
        }

      b4TreeWrapDv = wrapComputeDeferredValues b4TreeWrapDvInput

      b4MsgForNextStepDigestTree :: StepField
      b4MsgForNextStepDigestTree =
        fromJust'
          "b4 wrap prove: step PI[64] outer hash must exist" $
          Array.index b4StepResult.publicInputs 64

      b4TreeWrapProofSg :: AffinePoint WrapField
      b4TreeWrapProofSg = ProofFFI.pallasProofOpeningSg b4StepResult.proof

      PerProofUnfinalized b4Slot0UnfRec =
        Vector.head (unwrap treeB4Advice).publicUnfinalizedProofs

      PerProofUnfinalized b4Slot1UnfRec =
        Vector.head (Vector.drop @1 (unwrap treeB4Advice).publicUnfinalizedProofs)

      b4Slot0RealBpChalsWrap :: Vector WrapIPARounds WrapField
      b4Slot0RealBpChalsWrap =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF 128 WrapField)
                treeWrapEndoScalar
          )
          b4Slot0UnfRec.bulletproofChallenges

      b4Slot1RealBpChalsWrap :: Vector WrapIPARounds WrapField
      b4Slot1RealBpChalsWrap =
        map
          ( \(UnChecked v) ->
              toFieldPure (coerceViaBits v :: SizedF 128 WrapField)
                treeWrapEndoScalar
          )
          b4Slot1UnfRec.bulletproofChallenges

      b4MsgForNextWrapDigestTree :: WrapField
      b4MsgForNextWrapDigestTree = hashMessagesForNextWrapProofPureGeneral
        { sg: b4TreeWrapProofSg
        , paddedChallenges:
            b4Slot0RealBpChalsWrap
              :< b4Slot1RealBpChalsWrap
              :< Vector.nil
        }

      b4TreeWrapPublicInput = assembleWrapMainInput
        { deferredValues: b4TreeWrapDv
        , messagesForNextStepProofDigest: b4MsgForNextStepDigestTree
        , messagesForNextWrapProofDigest: b4MsgForNextWrapDigestTree
        }

      b4Slot0PerProof = convertSlotUnf b4Slot0UnfRec
      b4Slot1PerProof = convertSlotUnf b4Slot1UnfRec

      b4Slot0StepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
      b4Slot0StepAcc = WeierstrassAffinePoint
        { x: F nrrStepOpeningSg.x, y: F nrrStepOpeningSg.y }

      b4Slot1StepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
      b4Slot1StepAcc = WeierstrassAffinePoint
        { x: F b3TreeStepOpeningSgOracle.x, y: F b3TreeStepOpeningSgOracle.y }

      b4Slot0PrevEvalsW :: StepAllEvals (F WrapField)
      b4Slot0PrevEvalsW = slot0PrevEvalsW

      -- Slot 1 (Tree b3 wrap, real): oracles + evals over b3TreeWrapResult
      -- .proof with b3 wrap's actual kimchi prev_challenges.
      b4Slot1PrevEvalsW :: StepAllEvals (F WrapField)
      b4Slot1PrevEvalsW =
        let
          o = ProofFFI.vestaProofOracles treeWrapCR.verifierIndex
            { proof: b3TreeWrapResult.proof
            , publicInput: b3TreeWrapResult.publicInputs
            , prevChallenges:
                [ { sgX: b3Slot0ChalPolyComm.x
                  , sgY: b3Slot0ChalPolyComm.y
                  , challenges: Vector.toUnfoldable b3Slot0RealBpChalsWrap
                  }
                , { sgX: b3Slot1ChalPolyComm.x
                  , sgY: b3Slot1ChalPolyComm.y
                  , challenges: Vector.toUnfoldable b3Slot1RealBpChalsWrap
                  }
                ]
            }
          mkPE p = { zeta: F p.zeta, omegaTimesZeta: F p.omegaTimesZeta }
        in
          StepAllEvals
            { ftEval1: F o.ftEval1
            , publicEvals: PointEval
                { zeta: F o.publicEvalZeta
                , omegaTimesZeta: F o.publicEvalZetaOmega
                }
            , zEvals: PointEval (mkPE (ProofFFI.proofZEvals b3TreeWrapResult.proof))
            , witnessEvals: map (PointEval <<< mkPE) (ProofFFI.proofWitnessEvals b3TreeWrapResult.proof)
            , coeffEvals: map (PointEval <<< mkPE) (ProofFFI.proofCoefficientEvals b3TreeWrapResult.proof)
            , sigmaEvals: map (PointEval <<< mkPE) (ProofFFI.proofSigmaEvals b3TreeWrapResult.proof)
            , indexEvals: map (PointEval <<< mkPE) (ProofFFI.proofIndexEvals b3TreeWrapResult.proof)
            }

      b4TreeWrapAdviceInput :: BuildWrapAdviceInput 2 (Slots2 0 2)
      b4TreeWrapAdviceInput =
        { stepProof: b4StepResult.proof
        , whichBranch: F zero
        , prevUnfinalizedProofs: b4Slot0PerProof :< b4Slot1PerProof :< Vector.nil
        , prevMessagesForNextStepProofHash:
            F (fromBigInt (toBigInt b4MsgForNextStepDigestTree) :: WrapField)
        , prevStepAccs: b4Slot0StepAcc :< b4Slot1StepAcc :< Vector.nil
        -- wrap_b3 forwarded step_b3's per-slot bp_chals wrap-expanded
        -- into its msg_for_next_wrap_proof → b3Slot{0,1}RealBpChalsWrap.
        , prevOldBpChals: slots2 Vector.nil
            ( map F b3Slot0RealBpChalsWrap
                :< map F b3Slot1RealBpChalsWrap
                :< Vector.nil
            )
        , prevEvals: b4Slot0PrevEvalsW :< b4Slot1PrevEvalsW :< Vector.nil
        , prevWrapDomainIndices:
            F (fromInt 0 :: WrapField) :< F (fromInt 1 :: WrapField) :< Vector.nil
        }

      b4TreeWrapAdvice :: WrapAdvice 2 (Slots2 0 2)
      b4TreeWrapAdvice = buildWrapAdvice b4TreeWrapAdviceInput

      b4TreeWrapProveCtx =
        { wrapMainConfig: treeWrapCtx.wrapMainConfig
        , crs: pallasWrapSrs
        , publicInput: b4TreeWrapPublicInput
        , advice: b4TreeWrapAdvice
        , debug: true
        , kimchiPrevChallenges:
            { sgX: b4Slot0ChalPolyComm.x
            , sgY: b4Slot0ChalPolyComm.y
            , challenges: b4Slot0RealBpChalsWrap
            }
              :<
                { sgX: b4Slot1ChalPolyComm.x
                , sgY: b4Slot1ChalPolyComm.y
                , challenges: b4Slot1RealBpChalsWrap
                }
              :<
                Vector.nil
        }

    b4TreeWrapRes <- liftEffect $ runExceptT $
      wrapSolveAndProve @1 @(Slots2 0 2) b4TreeWrapProveCtx treeWrapCR
    b4TreeWrapResult <- case b4TreeWrapRes of
      Left e -> liftEffect $ Exc.throw ("b4 tree wrapSolveAndProve: " <> show e)
      Right r -> pure r

    liftEffect $ for_ (Array.mapWithIndex Tuple b4TreeWrapResult.publicInputs) \(Tuple i x) ->
      Trace.field ("b4.wrap.proof.public_input." <> show i) x

    liftEffect $ Trace.string "tree_proof_return.end" "inductive_case_4_proved"
