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
import Data.Tuple (Tuple(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles.Dummy as Dummy
import Pickles.ProofFFI as ProofFFI
import Pickles.PlonkChecks (AllEvals)
import Pickles.Prove.Step (StepAdvice(..), StepRule, buildStepAdvice, buildStepAdviceWithOracles, extractWrapVKCommsAdvice, extractWrapVKForStepHash, stepCompile, stepSolveAndProve)
import Pickles.Step.Prevs (StepSlot)
import Pickles.Types (StepIPARounds, WrapIPARounds)
import Snarky.Circuit.Kimchi (SplitField, Type2)
import Snarky.Types.Shifted (Type2) as ShiftedType2
import Snarky.Circuit.DSL (SizedF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Curves.Class (EndoScalar(..), endoScalar)
import Pickles.Prove.Wrap (WrapAdvice, buildWrapMainConfig, extractStepVKComms, wrapCompile, zeroWrapAdvice)
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Prove.Wrap (WrapCompileContext) as WP
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Trace as Trace
import Pickles.Types (StepField, WrapField)
import Pickles.Wrap.Slots (Slots2)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (createCRS)
import Test.Pickles.Prove.NoRecursionReturn.Producer (produceNoRecursionReturn)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F(..), FVar, add_, const_, exists, if_, not_, true_)
import Snarky.Data.EllipticCurve (AffinePoint)
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
        , wrapVK :: _
        , wrapSg :: _
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
        , wrapVK: nrr.wrapCR.verifierIndex
        , wrapSg: nrrWrapSg
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
        , kimchiPrevSg: nrr.stepSg
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
        , prevChallengesForStepHash: Dummy.dummyIpaChallenges.stepExpanded
        }

    -- Single-slot advice builds: slot 0 from buildStepAdviceWithOracles
    -- (real NRR data), slot 1 from buildStepAdvice (dummy N=2).
    -- We splice their carriers into Tree's heterogeneous
    -- `PrevsSpecCons 0 (PrevsSpecCons 2 PrevsSpecNil)` shape.
    { advice: slot0Advice } <- liftEffect $
      buildStepAdviceWithOracles @(PrevsSpecCons 0 PrevsSpecNil) oracleInput

    let
      slot1Dummy :: StepAdvice
        (PrevsSpecCons 2 PrevsSpecNil)
        StepIPARounds
        WrapIPARounds
        Unit
        1
        (Tuple (StepSlot 2 StepIPARounds WrapIPARounds (F StepField) (Type2 (SplitField (F StepField) Boolean)) Boolean) Unit)
      slot1Dummy = buildStepAdvice @(PrevsSpecCons 2 PrevsSpecNil)
        { publicInput: unit
        , mostRecentWidth: 2
        -- `buildStepAdvice` sets slot-1's dummy branchData.domainLog2
        -- = input.wrapDomainLog2. That field is semantically the
        -- prev slot's STEP domain (per OCaml fixture line 912:
        -- expand_proof.deferred.branch_data.domain_log2 = 15 for Tree
        -- slot 1, i.e. Tree step's log_size_of_group). Pass 15, not
        -- Tree's WRAP domain 14 — branchData drives FOP's
        -- maskedGen → inv_ would see wrong gen with 14.
        , wrapDomainLog2: treeSelfStepDomainLog2
        }

      StepAdvice s0 = slot0Advice
      StepAdvice s1 = slot1Dummy
      Tuple slot0Sppw _ = s0.perProofSlotsCarrier
      Tuple slot1Sppw _ = s1.perProofSlotsCarrier

      treeRealAdvice :: StepAdvice TreeProofReturnPrevsSpec StepIPARounds WrapIPARounds Unit 2 _
      treeRealAdvice = StepAdvice
        { perProofSlotsCarrier: Tuple slot0Sppw (Tuple slot1Sppw unit)
        , publicInput: unit
        -- Slot 0: real NRR unfinalized (from slot0Advice).
        -- Slot 1: dummy (from slot1Dummy).
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

    -- TODO(iter 2c): Tree wrap prove.
    -- TODO(iter 3):  witness diff via KIMCHI_WITNESS_DUMP on all 4 proofs.

    liftEffect $ Trace.string "tree_proof_return.end" "compile_only"
