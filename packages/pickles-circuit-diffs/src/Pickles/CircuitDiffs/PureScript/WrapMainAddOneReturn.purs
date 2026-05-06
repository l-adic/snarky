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
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepVKFromCompiled, deriveWrapVKFromCompiled)
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
  -> Effect WrapArtifact
compileWrapMainAddOneReturn { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainAddOneReturn stepParams
  vestaSrs <- createCRS @StepField
  pallasSrs <- createCRS @WrapField
  let
    realStepVK = deriveStepVKFromCompiled @0 vestaSrs stepArt.stepCs

    config :: WrapMainConfig 1
    config =
      -- N=0 Add_one_return: single branch, step_widths=[0].
      -- `domainLog2s` is the STEP proof's evaluation-domain log2
      -- (passed into `Branch_data.Checked.Wrap.pack` as `4 * log2`),
      -- derived from the step artifact.
      { stepWidths: 0 :< Vector.nil
      , domainLog2s: stepArt.stepDomainLog2 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Nothing
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  -- NoSlots: mpv=0, no per_proofs.
  wrapCs <- compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMain @1 @NoSlots config stmt)
    Kimchi.initialState
  pure
    { stepCs: stepArt.stepCs
    , stepDomainLog2: stepArt.stepDomainLog2
    , wrapCs
    , wrapVk: deriveWrapVKFromCompiled @2 pallasSrs wrapCs
    }
