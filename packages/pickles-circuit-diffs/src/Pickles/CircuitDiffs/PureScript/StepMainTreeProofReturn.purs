module Pickles.CircuitDiffs.PureScript.StepMainTreeProofReturn
  ( compileStepMainTreeProofReturn
  , StepMainTreeProofReturnParams
  , class TreeProofReturnAdvice
  , getTreeProofReturnIsBaseCase
  , getTreeProofReturnNoRecursiveInput
  , getTreeProofReturnPrev
  ) where

-- | step_main circuit for the Tree_proof_return rule.
-- |
-- | **N = 2**, **Output mode**, **heterogeneous prevs** at the rule
-- | level but homogeneous at the value-type level: both prev
-- | `public_input` slots are `StepField.typ` even though the first prev's
-- | rule has `max_proofs_verified = N0` (No_recursion_return) and the
-- | second is `self` with `max_proofs_verified = N2`. Our
-- | `Vector n (FVar StepField)` `prevPublicInputs` field handles this
-- | shape without needing an HList.
-- |
-- | Rule body computes `self = if is_base_case then 0 else 1 + prev`
-- | and exposes it as `publicOutput`. This exercises the Output-mode
-- | `hashAppFields = varToFields input <> varToFields output` path
-- | where `input = Unit` (contributes `[]`) and `output = FVar StepField`
-- | (contributes `[self]`) — matching OCaml step_main.ml:566-573's
-- | `Output _ -> ret_var` branch.
-- |
-- | Reference: mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:315-392
-- |            (Tree_proof_return).
-- | OCaml dump target: `step_main_tree_proof_return_circuit.json`
-- |            produced by `mina/src/lib/crypto/pickles/dump_circuit_impl.ml`.

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Tuple.Nested (Tuple2, tuple2, (/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, dummyWrapSg, mkStepArtifact, preComputeSelfStepDomainLog2)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainNoRecursionReturn (StepMainNoRecursionReturnParams)
import Pickles.CircuitDiffs.PureScript.WrapMainNoRecursionReturn (compileWrapMainNoRecursionReturn)
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Slots (Compiled, Slot)
import Pickles.Step.Main (RuleOutput, SlotVkBlueprintCompiled(..), stepMain)
import Pickles.Types (StatementIO)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F, FVar, Snarky, const_, exists, if_, not_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | Tree_proof_return has HETEROGENEOUS prev wrap_domains (slot 0: 2^13
-- | from No_recursion_return; slot 1: 2^14 from self @
-- | override_wrap_domain:N1). Each slot needs its own lagrange lookup
-- | keyed on the slot's domain size.
type StepMainTreeProofReturnParams =
  { perSlotLagrangeAt :: Vector 2 (LagrangeBaseLookup StepField)
  , blindingH :: AffinePoint (F StepField)
  -- SRS data for compiling NRR's wrap circuit (used to derive slot 0's
  -- known wrap key). Mirrors `IvpWrapParams` and
  -- `StepMainNoRecursionReturnParams` from
  -- `compileWrapMainNoRecursionReturn`.
  , nrrWrapSrsData :: IvpWrapParams
  , nrrStepSrsData :: StepMainNoRecursionReturnParams
  }

-- | Application-specific advice for the Tree_proof_return rule.
-- |
-- | Three requests from the OCaml test fixture:
-- | * `Is_base_case` — boolean controlling the base-vs-inductive branch.
-- | * `No_recursion_input` — the prev[0] public_input value (the
-- |   No_recursion_return proof's output field).
-- | * `Recursive_input` — the prev[1] public_input value (the parent
-- |   Tree_proof_return proof's output field).
-- |
-- | The proof witnesses themselves are tracked abstractly via the step
-- | advice monad; this class only supplies the field / boolean values
-- | the rule's `exists` calls request.
class Monad m <= TreeProofReturnAdvice m where
  getTreeProofReturnIsBaseCase :: Unit -> m Boolean
  getTreeProofReturnNoRecursiveInput :: Unit -> m (F StepField)
  getTreeProofReturnPrev :: Unit -> m (F StepField)

-- | Compilation instance: throws if evaluated. `exists` discards the
-- | AsProverT during circuit shape walks, so the throw never fires.
instance TreeProofReturnAdvice Effect where
  getTreeProofReturnIsBaseCase _ =
    throw "TreeProofReturnAdvice.getTreeProofReturnIsBaseCase: not available during compilation"
  getTreeProofReturnNoRecursiveInput _ =
    throw "TreeProofReturnAdvice.getTreeProofReturnNoRecursiveInput: not available during compilation"
  getTreeProofReturnPrev _ =
    throw "TreeProofReturnAdvice.getTreeProofReturnPrev: not available during compilation"

-- | Tree_proof_return rule:
-- |   `self = if is_base_case then 0 else 1 + prev`
-- |   prev[0].public_input = no_recursive_input (always verified)
-- |   prev[1].public_input = prev (verified unless base case)
-- |   public_output = self
-- |
-- | Reference: test_no_sideloaded.ml:354-390
treeProofReturnRule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => TreeProofReturnAdvice m
  => Unit
  -> Snarky (KimchiConstraint StepField) t m
       (RuleOutput 2 (FVar StepField) (FVar StepField))
treeProofReturnRule _ = do
  no_recursive_input <- exists $ lift $ getTreeProofReturnNoRecursiveInput unit
  prev <- exists $ lift $ getTreeProofReturnPrev unit
  (is_base_case) <- exists $ lift $
    getTreeProofReturnIsBaseCase unit
  let proofMustVerify = not_ is_base_case
  self <- if_ is_base_case (const_ zero) (CVar.add_ (const_ one) prev)
  pure
    { prevPublicInputs: no_recursive_input :< prev :< Vector.nil
    -- prev[0] always verifies (Boolean.true_ in OCaml);
    -- prev[1] verifies iff not base case.
    , proofMustVerify:
        (coerce (const_ one :: FVar StepField) :: BoolVar StepField)
          :< proofMustVerify
          :< Vector.nil
    , publicOutput: self
    }

compileStepMainTreeProofReturn
  :: StepMainTreeProofReturnParams -> Effect StepArtifact
compileStepMainTreeProofReturn params = do
  -- Compile NRR's wrap artifact up-front. The artifact bundles
  -- NRR's step CS + wrap CS + derived wrap VK + step domain log2 —
  -- everything TPR's slot 0 needs as compile-time constants.
  -- Mirrors OCaml `dump_tree_proof_return.ml:50-83`'s NRR-first
  -- compile order, with `Lazy.force compiled.wrap_key` and
  -- `compiled.step_domains` exposed via the artifact record.
  nrrArt <- compileWrapMainNoRecursionReturn
    params.nrrWrapSrsData
    params.nrrStepSrsData
  -- Slot 1 is self → its FOP domain log2 = TPR's own step domain
  -- log2. Resolved via shape pass (mirrors OCaml `Fix_domains.domains`).
  selfLog2 <- preComputeSelfStepDomainLog2 (runStepCompile nrrArt 1)
  mkStepArtifact <$> runStepCompile nrrArt selfLog2
  where
  runStepCompile nrrArt selfLog2 =
    compile (Proxy @Unit) (Proxy @(Vector 67 (F StepField))) (Proxy @(KimchiConstraint StepField))
      -- N=2, output size = 33*2 + 1 = 67 (two unfinalized proofs + digest
      -- + two msg_wrap entries). Wrap domain log2 = 14 from
      -- `override_wrap_domain:N1` (common.ml:25-29).
      -- Heterogeneous spec: slot 0 is No_recursion_return (n=0), slot 1
      -- is self (n=2). Per-slot FOP domain_log2 (`finalize_other_proof
      -- ~step_domains`) uses the prev's STEP_DOMAINS (NOT wrap_domains):
      -- * slot 0: NRR's step_domain.h, derived from `nrrArt.stepDomainLog2`.
      -- * slot 1: self's step_domain.h, derived via shape pass.
      -- Per-slot known wrap keys:
      -- * slot 0: VkBlueprintConst nrrArt.wrapVk — derived from compiled NRR
      --   wrap CS. Mirrors OCaml `Lazy.force compiled.wrap_key` at
      --   `step_branch_data.ml:164`.
      -- * slot 1: VkBlueprintShared — slot's prev is SELF, uses the
      --   `exists`-allocated VK inside stepMain.
      -- Single-rule: mpvMax = len = 2, mpvPad = 0.
      ( \_ -> stepMain
          @(Tuple2 (Slot Compiled 0 1 (StatementIO Unit (F StepField))) (Slot Compiled 2 1 (StatementIO Unit (F StepField))))
          @Unit
          @(F StepField)
          @(F StepField)
          @(Tuple2 (StatementIO Unit (F StepField)) (StatementIO Unit (F StepField)))
          @2
          @1
          treeProofReturnRule
          { perSlotLagrangeAt: params.perSlotLagrangeAt
          , blindingH: params.blindingH
          , perSlotFopDomainLog2s:
              (nrrArt.stepDomainLog2 :< Vector.nil)
                :< (selfLog2 :< Vector.nil)
                :< Vector.nil
          , perSlotVkBlueprints:
              VkBlueprintConst nrrArt.wrapVk /\ VkBlueprintShared /\ unit
          }
          dummyWrapSg
          -- Side-loaded VK carrier: two Cons slots, both compiled.
          (tuple2 unit unit)
      )
      Kimchi.initialState
