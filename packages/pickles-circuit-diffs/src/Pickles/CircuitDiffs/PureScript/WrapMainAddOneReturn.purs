-- | N=0 wrapper for the wrap_main library circuit (Add_one_return).
-- |
-- | Configuration: branches=1, step_widths=[0], Max_widths_by_slot=[N0; N0],
-- | Features.none. The slot widths come from the [[0]; [0]] padded vector
-- | passed to `Wrap_main.wrap_main` in `dump_circuit_impl.ml` for this fixture.
-- |
-- | **N = 0**: no previous proofs in the step proof being wrapped. This is
-- | the only N=0 wrap fixture in the suite — the step proof's own public
-- | input has no unfinalized_proofs slots and no messages_for_next_wrap_proof
-- | entries, so the wrap circuit's verify-one-of-step is a minimal
-- | configuration compared to Simple_chain (step_widths=[1]) and
-- | Simple_chain_n2 (step_widths=[0;2]).
-- |
-- | OCaml dump target: `wrap_main_add_one_return_circuit.json` produced by
-- | `mina/src/lib/crypto/pickles/dump_circuit_impl.ml` with
-- | `step_widths:[0]`, `padded:[[0];[0]]`, `domain_log2:13`.
module Pickles.CircuitDiffs.PureScript.WrapMainAddOneReturn
  ( compileWrapMainAddOneReturn
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, deriveStepVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainAddOneReturn (StepMainAddOneReturnParams, compileStepMainAddOneReturn)
import Pickles.Types (StepField, WrapField)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Pickles.Wrap.Slots (NoSlots)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

compileWrapMainAddOneReturn
  :: IvpWrapParams
  -> StepMainAddOneReturnParams
  -> Effect (CompiledCircuit WrapField)
compileWrapMainAddOneReturn { lagrangeAt, blindingH } stepParams = do
  -- Recompile the step CS (Add_one_return, mpv=0, no prev proofs) and
  -- derive its VK commitments via the kimchi commitment pipeline.
  -- Same pattern as wrap_main_circuit / wrap_main_n2_circuit fixes.
  stepBuiltState <- compileStepMainAddOneReturn stepParams
  vestaSrs <- createCRS @StepField
  let
    realStepVK = deriveStepVKFromCompiled @0 vestaSrs stepBuiltState
    config :: WrapMainConfig 1
    config =
      -- N=0 Add_one_return: single branch, step_widths=[0]. The
      -- `domainLog2s` field is the STEP proof's evaluation-domain log2
      -- (passed into `Branch_data.Checked.Wrap.pack` as `4 * log2`),
      -- NOT the wrap circuit's domain. For AOR the step CS is tiny
      -- (no verify_one machinery) → step domain log2 = 9, matching
      -- `compileStepMainAddOneReturn`'s `domain_log2 = 9` comment.
      -- Previously this was set to 13 (the wrap_domain log2),
      -- producing `4*13 = 52` in branch_data instead of OC's `4*9 = 36`.
      { stepWidths: 0 :< Vector.nil
      , domainLog2s: 9 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Nothing
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  -- NoSlots: mpv=0, no per_proofs. OCaml's `compile_promise` for
  -- Add_one_return sets `Max_proofs_verified.n = N0 = 0` (the rule has
  -- `prevs = []`), so the wrap statement packs only 1 PI entry — the
  -- previous `Slots2 0 0` (mpv=2) caused the +8103 row delta.
  compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMain @1 @NoSlots config stmt)
    Kimchi.initialState
