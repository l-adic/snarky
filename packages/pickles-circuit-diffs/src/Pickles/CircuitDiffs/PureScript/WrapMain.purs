-- | N1 wrapper for the wrap_main library circuit.
-- |
-- | Configuration: branches=1, step_widths=[1], Max_widths_by_slot=[N0; N1],
-- | Features.none. The slot widths come from the [[0]; [1]] padded vector
-- | passed to `Wrap_main.wrap_main` in `dump_circuit_impl.ml` for this fixture.
module Pickles.CircuitDiffs.PureScript.WrapMain
  ( compileWrapMainN1
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, deriveStepVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainSimpleChain (StepMainSimpleChainParams, compileStepMainSimpleChain)
import Pickles.Types (StepField, WrapField)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMain)
import Pickles.Wrap.Slots (Slots1)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

compileWrapMainN1
  :: IvpWrapParams
  -> StepMainSimpleChainParams
  -> Effect (CompiledCircuit WrapField)
compileWrapMainN1 { lagrangeAt, blindingH } stepParams = do
  -- Recompile the step CS and derive its VK commitments. This is what
  -- OCaml `compile_promise` does when it produces the step VK input to
  -- `Wrap_main.wrap_main`. Same step CS shape (we already match
  -- `step_main_simple_chain_circuit` byte-for-byte) + same Vesta SRS +
  -- same kimchi commitment algorithm = same VK constants. Mirrors the
  -- wrap_main_n2_circuit fix in commit `cf352650`.
  stepBuiltState <- compileStepMainSimpleChain stepParams
  vestaSrs <- createCRS @StepField
  let
    realStepVK = deriveStepVKFromCompiled @1 vestaSrs stepBuiltState
    config :: WrapMainConfig 1
    config =
      -- domainLog2 = 14 mirrors production Simple_chain N1 (verified
      -- via OCaml `compile.wrap_domains.h.log2` trace).
      { stepWidths: 1 :< Vector.nil
      , domainLog2s: 14 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Nothing
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  -- Slots1 1: mpv=1, slot 0 width=1. OCaml's `compile_promise` for
  -- Simple_chain N1 sets `Max_proofs_verified.n = N1 = 1`, so the wrap
  -- statement allocates `unfinalized_proofs : Vector 1 per_proof` and
  -- `messages_for_next_wrap_proof : Vector 1 Digest` — total 34 packed
  -- PI entries. The previous `Slots2 0 1` (mpv=2) produced 67 entries
  -- because PS was using the global Pickles cap as mpv; that mismatch
  -- was the +4074 row delta root cause.
  compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMain @1 @(Slots1 1) config stmt)
    Kimchi.initialState
