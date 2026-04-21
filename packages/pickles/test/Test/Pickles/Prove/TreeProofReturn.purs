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
-- | Required env vars at runtime:
-- | - `KIMCHI_DETERMINISTIC_SEED` — u64 seed for the patched kimchi RNG.
-- | - (optional) `KIMCHI_WITNESS_DUMP` — path template for witness dump.
-- | - (optional) `PICKLES_TRACE_FILE` — trace log path.
module Test.Pickles.Prove.TreeProofReturn
  ( spec
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Foldable (for_)
import Data.Int.Bits as Int
import Data.Maybe (Maybe(..))
import Data.Fin (unsafeFinite)
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw, throwException) as Exc
import Pickles.Dummy as Dummy
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.ProofFFI as ProofFFI
import Pickles.PlonkChecks (AllEvals)
import Pickles.Proof.Dummy (dummyWrapProof, dummyWrapProofWithZ)
import Pickles.Dummy.SimpleChain (simpleChainDummyPrevEvals)
import Pickles.Dummy.Tree (treeDummyPlonk, treeDummyProofZ1, treeDummyProofZ2)
import Pickles.Prove.Step (StepAdvice(..), StepRule, buildStepAdvice, buildStepAdviceWithOracles, dummyWrapTockPublicInput, extractWrapVKCommsAdvice, extractWrapVKForStepHash, stepCompile, stepSolveAndProve)
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, assembleWrapMainInput, wrapComputeDeferredValues)
import Pickles.Step.Prevs (StepSlot(..))
import Pickles.Types (PaddedLength, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepIPARounds, StepPerProofWitness(..), WrapIPARounds)
import Pickles.Util.Fatal (fromJust')
import Snarky.Circuit.Kimchi (SplitField, Type2)
import Snarky.Types.Shifted (Type2) as ShiftedType2
import Snarky.Types.Shifted (fromShifted, toShifted)
import Snarky.Circuit.DSL (SizedF, UnChecked(..), coerceViaBits)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (toFieldPure)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, fromInt, toBigInt)
import Pickles.Prove.Wrap (BuildWrapAdviceInput, WrapAdvice, buildWrapAdvice, buildWrapMainConfig, extractStepVKComms, wrapCompile, wrapSolveAndProve, zeroWrapAdvice)
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Prove.Wrap (WrapCompileContext) as WP
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Trace as Trace
import Pickles.Types (StepField, WrapField)
import Pickles.Wrap.Slots (Slots2, slots2)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (createCRS)
import Test.Pickles.Prove.NoRecursionReturn.Producer (produceNoRecursionReturn)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F(..), FVar, add_, const_, exists, if_, not_, true_)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
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
      dummySgValues = Dummy.computeDummySgValues lagrangeSrs vestaSrs
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
        }

      treePlaceholderAdvice = buildStepAdvice @TreeProofReturnPrevsSpec
        { publicInput: unit
        , mostRecentWidth: 2
        , wrapDomainLog2: treeWrapDomainLog2
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
        @Unit @Unit
        @(F StepField) @(FVar StepField)
        @(F StepField) @(FVar StepField)
        treeCtx (treeProofReturnRule baseRuleArgs) treePlaceholderAdvice

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
        (zeroWrapAdvice :: WrapAdvice 2 _)

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
      oracleInput ::
        { publicInput :: Unit
        , prevPublicInput :: F StepField
        , mostRecentWidth :: Int
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
        , prevPublicInput: F zero        -- NRR's output
        , mostRecentWidth: 0             -- NRR is N=0
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
        , mustVerify: true               -- slot 0 always verifies
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
      slot1BaseCaseWrapPI = dummyWrapTockPublicInput
        { mostRecentWidth: 2
        -- branchData.domainLog2 for OCaml Proof.dummy N2 N2 ~domain_log2:15.
        , wrapDomainLog2: treeSelfStepDomainLog2
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
        , fopProofState: Dummy.treeStepDummyFopProofState { proofsVerified: 2 }
        }
    { advice: slot1Advice, challengePolynomialCommitment: b0Slot1ChalPolyComm } <- liftEffect $
      buildStepAdviceWithOracles @2 @(PrevsSpecCons 2 PrevsSpecNil)
        { publicInput: unit
        , prevPublicInput: (F (negate one)) :: F StepField
        , mostRecentWidth: 2
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
        -- Tree compile, so its Ro counter is past module-init. Use the
        -- Tree-runtime z1/z2 values captured from dump_tree_proof_return's
        -- `expand_proof.dummy_proof.z1/z2` trace; everything else in the
        -- dummy proof (lr=g0, sg=g0, delta=g0, evals=Dummy.evals,
        -- ft_eval1=Dummy.evals.ft_eval1) is deterministic and matches
        -- module-init dummyWrapProof.
        , wrapProof: dummyWrapProofWithZ
            { z1: treeDummyProofZ1, z2: treeDummyProofZ2 }
        , wrapPublicInput: slot1BaseCaseWrapPI
        , prevChalPolys:
            slot1BaseCaseDummyChalPoly
              :< slot1BaseCaseDummyChalPoly
              :< Vector.nil
              :: Vector PaddedLength _
        , wrapPlonkRaw: treeDummyPlonk
        , wrapPrevEvals: simpleChainDummyPrevEvals
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
        , fopState: Dummy.treeStepDummyFopProofState { proofsVerified: 2 }
        , stepAdvicePrevEvals: Dummy.roComputeResult.stepDummyPrevEvals
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

    treeStepResult <- liftEffect $
      stepSolveAndProve
        @TreeProofReturnPrevsSpec @67
        @Unit @Unit
        @(F StepField) @(FVar StepField)
        @(F StepField) @(FVar StepField)
        (\e -> Exc.throw ("tree stepSolveAndProve: " <> show e))
        treeCtx
        (treeProofReturnRule baseRuleArgs)
        treeStepCR
        treeRealAdvice

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
      msgForNextStepDigestTree = fromJust'
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

      -- `dummyIpaChallenges.wrapExpanded` already has type `Vector
      -- WrapIPARounds WrapField`; no coercion needed. (The similar
      -- `fromBigInt <<< toBigInt` pattern in SimpleChain.purs:596 is
      -- same-field identity and should eventually be cleaned up.)
      msgForNextWrapDummyChals :: Vector WrapIPARounds WrapField
      msgForNextWrapDummyChals = Dummy.dummyIpaChallenges.wrapExpanded

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
            { proof: dummyWrapProofWithZ
                { z1: treeDummyProofZ1, z2: treeDummyProofZ2 }
            , publicInput: slot1BaseCaseWrapPI
            , prevChallenges: map toFFI [ dummyChalPoly, dummyChalPoly ]
            }
          de = Dummy.roComputeResult.wrapDummyEvals
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
        , kimchiPrevChallenges:
            -- Padded-length-2 accumulator for the wrap prover's kimchi
            -- prev_challenges. Both entries dummy for base case.
            let
              padEntry =
                { sgX: nrrWrapSg.x
                , sgY: nrrWrapSg.y
                , challenges: Dummy.dummyIpaChallenges.wrapExpanded
                }
            in
              padEntry :< padEntry :< Vector.nil
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

    treeWrapResult <- liftEffect $
      wrapSolveAndProve @1 @(Slots2 0 2)
        (\e -> Exc.throwException e)
        treeWrapProveCtx
        treeWrapCR

    liftEffect $ for_ (Array.mapWithIndex Tuple treeWrapResult.publicInputs) \(Tuple i x) ->
      Trace.field ("wrap.proof.public_input." <> show i) x

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
        , nrrInputVal: F zero       -- NRR's output is always 0
        , prevInputVal: F zero      -- b0's output was 0
        }

      -- b0's Tree step proof opening sg: what b1 slot-1's oracleInput
      -- feeds as stepOpeningSg (i.e. the sg field stored in wrap_b0's
      -- messages_for_next_wrap_proof, per wrap.ml:541-556).
      b0StepOpeningSg :: AffinePoint WrapField
      b0StepOpeningSg = ProofFFI.pallasProofOpeningSg treeStepResult.proof

      -- wrap-field endo (for expanding step unfinalized bp chals to wrap-field
      -- msgForNextWrap challenges).
      treeWrapEndoScalarB1 :: WrapField
      treeWrapEndoScalarB1 =
        let EndoScalar e = (endoScalar :: EndoScalar WrapField) in e

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
    { advice: b1Slot0Advice } <- liftEffect $
      buildStepAdviceWithOracles @0 @(PrevsSpecCons 0 PrevsSpecNil) oracleInput

    -- b1 slot-1 advice: NEW — verifying REAL Tree b0 wrap proof.
    { advice: b1Slot1Advice } <- liftEffect $
      buildStepAdviceWithOracles @2 @(PrevsSpecCons 2 PrevsSpecNil)
        { publicInput: unit
        , prevPublicInput: (F zero) :: F StepField  -- b0 output was 0
        , mostRecentWidth: 2
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

    b1StepResult <- liftEffect $
      stepSolveAndProve
        @TreeProofReturnPrevsSpec @67
        @Unit @Unit
        @(F StepField) @(FVar StepField)
        @(F StepField) @(FVar StepField)
        (\e -> Exc.throw ("b1 stepSolveAndProve: " <> show e))
        treeCtx
        (treeProofReturnRule b1RuleArgs)
        treeStepCR
        treeB1Advice

    liftEffect $ for_ (Array.mapWithIndex Tuple b1StepResult.publicInputs) \(Tuple i x) ->
      Trace.field ("b1.step.proof.public_input." <> show i) x

    liftEffect $ Trace.string "tree_proof_return.end" "inductive_case_proved"
