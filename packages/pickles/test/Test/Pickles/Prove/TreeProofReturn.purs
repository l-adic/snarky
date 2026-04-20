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
import Data.Int.Bits as Int
import Data.Maybe (Maybe(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles.Dummy as Dummy
import Pickles.ProofFFI as ProofFFI
import Pickles.Prove.Step (StepRule, buildStepAdvice, extractWrapVKCommsAdvice, stepCompile)
import Pickles.Prove.Wrap (WrapAdvice, buildWrapMainConfig, wrapCompile, zeroWrapAdvice)
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Prove.Wrap (WrapCompileContext) as WP
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Trace as Trace
import Pickles.Types (StepField)
import Pickles.Wrap.Slots (Slots2, NoSlots)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F(..), FVar, const_, exists, true_)
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Spec (SpecT, describe, it)

-- | Tree_proof_return prev-spec: slot 0 has width 0 (No_recursion_return
-- | proof), slot 1 has width 2 (self).
type TreeProofReturnPrevsSpec = PrevsSpecCons 0 (PrevsSpecCons 2 PrevsSpecNil)

-- | No_recursion_return rule — identical to `Test.Pickles.Prove.NoRecursionReturn`.
-- | N=0 Output mode, returns zero, no prev proofs.
-- | Reference: test_no_sideloaded.ml:100-107
nrrRule :: StepRule 0 Unit Unit (F StepField) (FVar StepField) Unit Unit
nrrRule _ = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: const_ zero
  }

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
  :: StepRule 2
       Unit
       Unit
       (F StepField)
       (FVar StepField)
       (F StepField)
       (FVar StepField)
treeProofReturnRule _ = do
  -- Prev input witnesses: slot-0 (No_recursion_return) input value,
  -- slot-1 (self) input value. For the base case these are supplied
  -- via the step advice; at compile time they're placeholders.
  nrrInput <- exists $ lift $ pure (F zero)
  prevInput <- exists $ lift $ pure (F zero)
  pure
    { prevPublicInputs: nrrInput :< prevInput :< Vector.nil
    -- iter 1: placeholder must-verify flags. Real structure for
    -- the base case is [true_, not is_base_case]; iter 2 will
    -- thread is_base_case through from the advice.
    , proofMustVerify: true_ :< true_ :< Vector.nil
    , publicOutput: const_ zero
    }

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.TreeProofReturn" do
  it "Tree_proof_return base case (step0 + wrap0) compiles" \_ -> do
    liftEffect $ Trace.string "tree_proof_return.begin" "base_case"

    -- ===== SRS setup (same depths as NoRecursionReturn / Simple_chain) =====
    let pallasWrapSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    let lagrangeSrs = pallasWrapSrs
    vestaSrs <- liftEffect $ createCRS @StepField

    let
      dummySgValues = Dummy.computeDummySgValues lagrangeSrs vestaSrs
      nrrWrapSg = dummySgValues.ipa.wrap.sg
      nrrWrapDomainLog2 = 13
      treeWrapDomainLog2 = 13  -- override_wrap_domain:N1 → h = 2^13

    -- ===== Phase 1: compile No_recursion_return step + wrap =====
    -- This produces the compiled wrap VK whose point commitments get
    -- baked into Tree_proof_return's `known_wrap_keys` for slot 0.
    let
      nrrCtx =
        { srsData:
            { perSlotLagrangeAt: Vector.nil
            , blindingH:
                (coerce $ ProofFFI.vestaSrsBlindingGenerator lagrangeSrs)
                  :: AffinePoint (F StepField)
            , perSlotFopDomainLog2: Vector.nil
            , perSlotKnownWrapKeys: Vector.nil
            }
        , dummySg: nrrWrapSg
        , crs: vestaSrs
        }
      nrrPlaceholderAdvice = buildStepAdvice @PrevsSpecNil
        { publicInput: unit
        , mostRecentWidth: 0
        , wrapDomainLog2: nrrWrapDomainLog2
        }

    nrrStepCR <- liftEffect $
      stepCompile @PrevsSpecNil @1 @Unit @Unit @(F StepField) @(FVar StepField) @Unit @Unit
        nrrCtx nrrRule nrrPlaceholderAdvice

    let
      nrrStepDomainLog2 = ProofFFI.pallasProverIndexDomainLog2 nrrStepCR.proverIndex
      nrrWrapCtx :: WP.WrapCompileContext 1
      nrrWrapCtx =
        { wrapMainConfig:
            buildWrapMainConfig vestaSrs nrrStepCR.verifierIndex
              { stepWidth: 0, domainLog2: nrrStepDomainLog2 }
        , crs: pallasWrapSrs
        }
    nrrWrapCR <- liftEffect $
      wrapCompile @1 @NoSlots nrrWrapCtx
        (zeroWrapAdvice :: WrapAdvice 0 _)
    let nrrWrapVKCommsAdvice = extractWrapVKCommsAdvice nrrWrapCR.verifierIndex

    -- ===== Phase 2: compile Tree_proof_return step =====
    -- Heterogeneous prev-slot config:
    --   slot 0: lagrange @ NRR wrap domain (2^13), FOP log2=13,
    --           known VK = NRR's wrap VK (Just)
    --   slot 1: lagrange @ self wrap domain (2^13), FOP log2=13,
    --           known VK = Nothing (self — placeholder, patched post-compile)
    let
      -- Both slots use wrap domain 2^13 (No_recursion_return's h=2^13 and
      -- Tree_proof_return's own h=2^13 via override_wrap_domain:N1). We
      -- pre-compute a `LagrangeBaseLookup` closure for each slot — they
      -- happen to be identical here but kept per-slot for symmetry with
      -- heterogeneous cases where they'd differ.
      mkLagrangeAt = mkConstLagrangeBaseLookup \i ->
        (coerce (ProofFFI.vestaSrsLagrangeCommitmentAt pallasWrapSrs 13 i))
          :: AffinePoint (F StepField)

      treeSrsData =
        { perSlotLagrangeAt: mkLagrangeAt :< mkLagrangeAt :< Vector.nil
        , blindingH:
            (coerce $ ProofFFI.vestaSrsBlindingGenerator lagrangeSrs)
              :: AffinePoint (F StepField)
        , perSlotFopDomainLog2: nrrWrapDomainLog2 :< treeWrapDomainLog2 :< Vector.nil
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
    treeStepCR <- liftEffect $
      stepCompile @TreeProofReturnPrevsSpec @67
        @Unit @Unit
        @(F StepField) @(FVar StepField)
        @(F StepField) @(FVar StepField)
        treeCtx treeProofReturnRule treePlaceholderAdvice

    -- ===== Phase 3: compile Tree_proof_return wrap =====
    let
      treeStepDomainLog2 = ProofFFI.pallasProverIndexDomainLog2 treeStepCR.proverIndex
      treeWrapCtx :: WP.WrapCompileContext 1
      treeWrapCtx =
        { wrapMainConfig:
            buildWrapMainConfig vestaSrs treeStepCR.verifierIndex
              { stepWidth: 2, domainLog2: treeStepDomainLog2 }
        , crs: pallasWrapSrs
        }
    _treeWrapCR <- liftEffect $
      wrapCompile @1 @(Slots2 0 2) treeWrapCtx
        (zeroWrapAdvice :: WrapAdvice 2 _)

    -- TODO(iter 2): NRR step prove → NRR wrap prove →
    --               Tree step prove (slot 0 = real NRR proof,
    --                                slot 1 = dummy N2) →
    --               Tree wrap prove.
    -- TODO(iter 3): witness diff via KIMCHI_WITNESS_DUMP on all 4 proofs.

    liftEffect $ Trace.string "tree_proof_return.end" "compile_only"
