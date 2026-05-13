-- | N=0 wrapper for the `wrap_main` library circuit at `num_chunks=2`,
-- | `override_wrap_domain=N1`. Mirrors `dump_chunks2.ml` — same N=0
-- | single-rule compile shape as Add_one_return but the step circuit
-- | is large enough (2^17 rows) that kimchi's PCS commits the step's
-- | `w/z/t_comm` with `num_chunks=2`. The wrap IVP MSM therefore walks
-- | 2 chunks per per-polynomial commitment.
-- |
-- | Configuration: `branches=1`, `step_widths=[0]`, wrap domain log2=14
-- | (= N1), step domain log2=17, num_chunks=2. OCaml fixture:
-- | `chunks2_wrap_main_circuit.json` (9388 gates).
module Pickles.CircuitDiffs.PureScript.WrapMainChunks2
  ( compileWrapMainChunks2
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepVKFromCompiled, deriveWrapVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainChunks2 (StepMainChunks2Params, compileStepMainChunks2)
import Pickles.Field (StepField, WrapField)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMainForPrevs)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

compileWrapMainChunks2
  :: IvpWrapParams
  -> StepMainChunks2Params
  -> Effect WrapArtifact
compileWrapMainChunks2 { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainChunks2 stepParams
  vestaSrs <- createCRS @StepField
  pallasSrs <- createCRS @WrapField
  let
    realStepVK = deriveStepVKFromCompiled @0 vestaSrs stepArt.stepCs

    config :: WrapMainConfig 1
    config =
      { stepWidths: 0 :< Vector.nil
      -- WrapMainConfig.domainLog2s is the STEP proof's domain log2,
      -- not the wrap circuit's domain (see commit 601cded5 / memory
      -- `project_wrap_main_circuit_constant_public_input`). chunks2
      -- step CS rounds to 2^17.
      , domainLog2s: stepArt.stepDomainLog2 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Nothing
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  -- `slots` derived from `@Unit` via `SlotsFromSpec` funcdep. The
  -- @2 numChunks type-app drives the wrap IVP's chunked w/z/t MSM
  -- (Pcs_batch.combine_split_commitments with num_chunks=2).
  wrapCs <- compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMainForPrevs @1 @Unit @2 config stmt)
    Kimchi.initialState
  pure
    { stepCs: stepArt.stepCs
    , stepDomainLog2: stepArt.stepDomainLog2
    , wrapCs
    , wrapVk: deriveWrapVKFromCompiled @2 pallasSrs wrapCs
    }
