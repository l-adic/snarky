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
-- | `public_input` slots are `Field.typ` even though the first prev's
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
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Partial.Unsafe (unsafeCrashWith)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, deriveWrapVKFromCompiled, dummyWrapSg)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainNoRecursionReturn (StepMainNoRecursionReturnParams)
import Pickles.CircuitDiffs.PureScript.WrapMainNoRecursionReturn (compileWrapMainNoRecursionReturn)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Step.Main (RuleOutput, SlotVkSource(..), stepMain)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (StatementIO, StepField, WrapField)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
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
  (is_base_case :: BoolVar StepField) <- exists $ lift $
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
  :: StepMainTreeProofReturnParams -> Effect (CompiledCircuit StepField)
compileStepMainTreeProofReturn params = do
  -- Compile NRR's wrap CS up-front and derive its real wrap VK. This
  -- mirrors `dump_tree_proof_return.ml:50-83` which compiles
  -- No_recursion_return before TPR so its `compiled.wrap_key` is
  -- loaded when TPR's compile reads slot 0's prev tag (via
  -- `Lazy.force compiled.wrap_key` in `step_branch_data.ml:164`).
  -- `@2` = `PaddedLength` = wrap-side `prev_challenges` (always padded
  -- to 2 by `Wrap_hack.pad_accumulator`).
  nrrWrapBuiltState <- compileWrapMainNoRecursionReturn
    params.nrrWrapSrsData
    params.nrrStepSrsData
  pallasSrs <- createCRS @WrapField
  let
    realNrrWrapVK = deriveWrapVKFromCompiled @2 pallasSrs nrrWrapBuiltState
  compile (Proxy @Unit) (Proxy @(Vector 67 (F StepField))) (Proxy @(KimchiConstraint StepField))
    -- N=2, output size = 33*2 + 1 = 67 (two unfinalized proofs + digest
    -- + two msg_wrap entries). Wrap domain log2 = 14 from
    -- `override_wrap_domain:N1` (common.ml:25-29).
    -- Self: input=Unit (Output mode), output=Field. Prevs: both
    -- public_input slots are Field (prev[0]=No_recursion_return's
    -- output, prev[1]=self's output), so prevInputVal=F StepField.
    -- Heterogeneous spec: slot 0 is No_recursion_return (n=0), slot 1 is
    -- self (n=2). With stepMain's spec-indexed carrier, slot 0's SPPW
    -- has empty prev_challenges / prev_sgs (correctly reflecting that a
    -- N=0 prev verified zero prior proofs). The v1 path over-allocated
    -- slot 0 to size 2, producing ~4 extra on-curve-check rows vs OCaml.
    -- Per-slot FOP domain_log2 — `finalize_other_proof ~step_domains`
    -- uses the prev's STEP_DOMAINS (NOT wrap_domains):
    -- * slot 0: NRR's step_domain.h = 2^9 (real NRR step CS rounds
    --   up to 2^9 = 512 rows; the previous `13` reflected a fixture
    --   placeholder, not OCaml's actual `Lazy.force compiled.step_domains`
    --   reading the compiled NRR step CS's domain).
    -- * slot 1: self's step_domain.h = 2^15 (TPR step CS rounds to
    --   2^15 — matches the `domainLog2s: 15` in
    --   `WrapMainTreeProofReturn.purs:57` and the empirical
    --   branch_data row 81 coefficient `60 = 4*15`). Note: self's
    --   wrap_domains.h is 2^14 (override_wrap_domain:N1), used for
    --   the IVP lagrange lookup, not the FOP domain.
    --
    -- Per-slot known wrap keys:
    -- * slot 0: Just realNrrWrapVK — the actual NRR wrap VK derived
    --   from the compiled NRR wrap CS. Mirrors OCaml's
    --   `Lazy.force compiled.wrap_key` at `step_branch_data.ml:164`,
    --   loaded from NRR's earlier compile (`compile_promise` in
    --   `dump_tree_proof_return.ml:50-83`).
    -- * slot 1: Nothing — slot's prev is SELF, uses the shared
    --   `exists`-allocated VK inside stepMain.
    -- Single-rule: mpvMax = len = 2, mpvPad = 0.
    ( \_ -> stepMain
        @( PrevsSpecCons 0 (StatementIO Unit (F StepField))
            (PrevsSpecCons 2 (StatementIO Unit (F StepField)) PrevsSpecNil)
        )
        @67
        @Unit
        @Unit
        @(F StepField)
        @(FVar StepField)
        @(F StepField)
        @(FVar StepField)
        @( Tuple (StatementIO Unit (F StepField))
            (Tuple (StatementIO Unit (F StepField)) Unit)
        )
        @2
        @0
        treeProofReturnRule
        { perSlotLagrangeAt: params.perSlotLagrangeAt
        , blindingH: params.blindingH
        , perSlotFopDomainLog2s:
            (9 :< Vector.nil) :< (15 :< Vector.nil) :< Vector.nil
        , perSlotVkSources: ConstVk realNrrWrapVK :< SharedExistsVk :< Vector.nil
        -- Phase 2b.31a: thunks for mpvMax-padding dummies. Single-rule
        -- callers have mpvPad=0 so `mpvFrontPad` short-circuits and the
        -- thunks never fire — `unsafeCrashWith` is fine.
        , dummyUnfp: \_ -> unsafeCrashWith "dummyUnfp: unused at mpvPad=0"
        }
        dummyWrapSg
        -- Side-loaded VK carrier (Step 2d-β1.5b): two Cons slots
        -- (NRR external, Self), both compiled; carrier =
        -- `Unit /\ Unit /\ Unit`.
        (unit /\ unit /\ unit)
    )
    Kimchi.initialState
