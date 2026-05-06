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
import Pickles.CircuitDiffs.PureScript.Common (WrapArtifact, deriveStepVKFromCompiled, deriveWrapVKFromCompiled)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainSimpleChain (StepMainSimpleChainParams, compileStepMainSimpleChain)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (StatementIO, StepField, WrapField)
import Pickles.Wrap.Main (WrapMainConfig, WrapMainInput, wrapMainForPrevs)
import Snarky.Circuit.DSL (F)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

compileWrapMainN1
  :: IvpWrapParams
  -> StepMainSimpleChainParams
  -> Effect WrapArtifact
compileWrapMainN1 { lagrangeAt, blindingH } stepParams = do
  stepArt <- compileStepMainSimpleChain stepParams
  vestaSrs <- createCRS @StepField
  pallasSrs <- createCRS @WrapField
  let
    realStepVK = deriveStepVKFromCompiled @1 vestaSrs stepArt.stepCs

    config :: WrapMainConfig 1
    config =
      { stepWidths: 1 :< Vector.nil
      , domainLog2s: stepArt.stepDomainLog2 :< Vector.nil
      , stepKeys: realStepVK :< Vector.nil
      , lagrangeAt
      , perBranchLagrangeAt: Nothing
      , blindingH
      , allPossibleDomainLog2s:
          unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
      }
  -- mpv=1, slot 0 width=1; slots derived from PrevsSpec via funcdep.
  wrapCs <- compile (Proxy @WrapMainInput) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMainForPrevs @1 @(PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil) config stmt)
    Kimchi.initialState
  pure
    { stepCs: stepArt.stepCs
    , stepDomainLog2: stepArt.stepDomainLog2
    , wrapCs
    , wrapVk: deriveWrapVKFromCompiled @2 pallasSrs wrapCs
    }
