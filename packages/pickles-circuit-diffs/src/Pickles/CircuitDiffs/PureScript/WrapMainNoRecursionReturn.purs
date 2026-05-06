-- | N=0 wrapper for the wrap_main library circuit (No_recursion_return).
-- |
-- | Configuration: branches=1, step_widths=[0], Max_widths_by_slot=[N0; N0],
-- | Features.none. Same shape as Add_one_return — both are N=0 leaf rules
-- | whose step proofs have no prev unfinalized_proofs and no
-- | messages_for_next_wrap_proof entries. The wrap circuit's
-- | verify_one-of-step is the same minimal configuration; only the
-- | embedded step VK differs (since NRR's step CS uses Output mode with
-- | `output = 0`, while AOR uses Input_and_output mode).
-- |
-- | Used by `compileStepMainTreeProofReturn` to derive NRR's wrap VK
-- | (via `deriveWrapVKFromCompiled`) so TPR's slot 0 known wrap key
-- | is the real OCaml `Lazy.force compiled.wrap_key` for NRR rather
-- | than a placeholder. Mirrors `dump_tree_proof_return.ml:50-83` which
-- | compiles NRR up-front so its `compiled.wrap_key` is loaded when TPR's
-- | compile reads slot 0's prev tag (`step_branch_data.ml:164`).
module Pickles.CircuitDiffs.PureScript.WrapMainNoRecursionReturn
  ( compileWrapMainNoRecursionReturn
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, deriveStepVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainNoRecursionReturn (StepMainNoRecursionReturnParams, compileStepMainNoRecursionReturn)
import Pickles.Types (StepField, WrapField)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Pickles.Wrap.Slots (NoSlots)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

compileWrapMainNoRecursionReturn
  :: IvpWrapParams
  -> StepMainNoRecursionReturnParams
  -> Effect (CompiledCircuit WrapField)
compileWrapMainNoRecursionReturn { lagrangeAt, blindingH } stepParams = do
  -- Recompile NRR's step CS (mpv=0, no prev proofs, Output mode) and
  -- derive its VK commitments via the kimchi commitment pipeline.
  -- Same pattern as `compileWrapMainAddOneReturn` — both are N=0 leaf
  -- rules with structurally identical wrap configs.
  stepBuiltState <- compileStepMainNoRecursionReturn stepParams
  vestaSrs <- createCRS @StepField
  let
    realStepVK = deriveStepVKFromCompiled @0 vestaSrs stepBuiltState
    config :: WrapMainConfig 1
    config =
      -- N=0 NRR: single branch, step_widths=[0]. `domainLog2s` is the
      -- STEP CS's evaluation-domain log2 (= 9, since NRR's step CS has
      -- 433 gates which round up to 2^9 = 512). Identical to AOR.
      { stepWidths: 0 :< Vector.nil
      , domainLog2s: 9 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Nothing
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  -- NoSlots: mpv=0, no per_proofs. OCaml's `compile_promise` for NRR
  -- sets `Max_proofs_verified.n = N0 = 0` (the rule has `prevs = []`),
  -- so the wrap statement packs only 1 PI entry.
  compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMain @1 @NoSlots config stmt)
    Kimchi.initialState
